package C8080;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;

import static C8080.Token.TokenType.*;

/** Converts C source text into tokens while retaining source positions for diagnostics. */
public class Lexer {
    /** A lexical failure with the source span that caused it. */
    public static final class LexicalError extends IllegalArgumentException {
        private static final long serialVersionUID = 1L;

        private final int line;
        private final int column;
        private final int length;

        private LexicalError(String message, int line, int column, int length) {
            super(message + " at line " + line + ", column " + column + ".");
            this.line = line;
            this.column = column;
            this.length = Math.max(1, length);
        }

        public int line() { return line; }
        public int column() { return column; }
        public int length() { return length; }
    }

    private static final Map<String, Token.TokenType> KEYWORDS = Map.ofEntries(
            Map.entry("volatile", VOLATILE),
            Map.entry("int", INT), Map.entry("char", CHAR), Map.entry("void", VOID),
            Map.entry("enum", ENUM), Map.entry("struct", STRUCT), Map.entry("union", UNION),
            Map.entry("const", CONST), Map.entry("static", STATIC), Map.entry("return", RETURN),
            Map.entry("if", IF), Map.entry("else", ELSE), Map.entry("while", WHILE),
            Map.entry("for", FOR), Map.entry("break", BREAK), Map.entry("continue", CONTINUE),
            Map.entry("switch", SWITCH), Map.entry("case", CASE), Map.entry("default", DEFAULT),
            Map.entry("do", DO), Map.entry("long", LONG), Map.entry("short", SHORT),
            Map.entry("asm", ASM),
            Map.entry("float", FLOAT), Map.entry("double", DOUBLE), Map.entry("unsigned", UNSIGNED),
            Map.entry("signed", SIGNED), Map.entry("extern", EXTERN), Map.entry("typedef", TYPEDEF),
            Map.entry("sizeof", SIZEOF));

    private static final Map<String, Token.TokenType> TWO_CHARACTER_OPERATORS = Map.ofEntries(
            Map.entry("==", EQUAL_EQUAL), Map.entry("!=", NOT_EQUAL), Map.entry("<=", LESS_EQUAL),
            Map.entry(">=", GREATER_EQUAL), Map.entry("&&", AND_AND), Map.entry("||", OR_OR),
            Map.entry("++", PLUS_PLUS), Map.entry("--", MINUS_MINUS), Map.entry("+=", PLUS_EQUALS),
            Map.entry("-=", MINUS_EQUALS), Map.entry("*=", STAR_EQUALS), Map.entry("/=", DIV_EQUALS),
            Map.entry("%=", MOD_EQUALS), Map.entry("&=", AMP_EQUALS), Map.entry("|=", PIPE_EQUALS),
            Map.entry("^=", CARET_EQUALS), Map.entry("<<", SHIFT_LEFT), Map.entry(">>", SHIFT_RIGHT),
            Map.entry("->", ARROW));

    private static final Map<Character, Token.TokenType> ONE_CHARACTER_OPERATORS = Map.ofEntries(
            Map.entry('=', EQUALS), Map.entry('<', LESS), Map.entry('>', GREATER),
            Map.entry('+', PLUS), Map.entry('-', MINUS), Map.entry('*', STAR),
            Map.entry('%', PERCENT), Map.entry('!', BANG), Map.entry('&', AMP),
            Map.entry('|', PIPE), Map.entry('^', CARET), Map.entry('~', TILDE),
            Map.entry('.', PERIOD), Map.entry('(', OPEN_PAREN), Map.entry(')', CLOSE_PAREN),
            Map.entry('[', OPEN_BRACKET), Map.entry(']', CLOSE_BRACKET), Map.entry('?', QUESTION),
            Map.entry('{', OPEN_BRACE), Map.entry('}', CLOSE_BRACE), Map.entry(';', SEMICOLON),
            Map.entry(',', COMMA), Map.entry(':', COLON));

    private final String source;
    private final List<Token> tokens = new ArrayList<>();
    private int index;
    private int line = 1;
    private int column = 1;
    private BooleanSupplier cancelled = () -> false;

    /** Creates a lexer; null source is treated as an empty translation unit. */
    public Lexer(String source) {
        this.source = source == null ? "" : source;
    }

    /** Tokenizes the source and returns an immutable list ending with an EOF token. */
    public List<Token> tokenize() {
        return tokenize(() -> false);
    }

    List<Token> tokenize(BooleanSupplier cancellation) {
        BooleanSupplier previousCancellation = cancelled;
        cancelled = cancellation == null ? () -> false : cancellation;
        try {
            return tokenizeCancellable();
        } finally {
            cancelled = previousCancellation;
        }
    }

    private List<Token> tokenizeCancellable() {
        tokens.clear();
        index = 0;
        line = 1;
        column = 1;
        while (!eof()) {
            checkCancelled();
            char current = peek();
            if (Character.isWhitespace(current)) {
                advance();
                continue;
            }

            int tokenLine = line;
            int tokenColumn = column;
            if (isIdentifierStart(current)) {
                tokenizeIdentifier(tokenLine, tokenColumn);
            } else if (startsNumber(current)) {
                tokenizeNumber(tokenLine, tokenColumn);
            } else if (current == '.' && source.startsWith("...", index)) {
                advance();
                advance();
                advance();
                add(ELLIPSIS, "...", tokenLine, tokenColumn);
            } else if (current == '/') {
                tokenizeSlash(tokenLine, tokenColumn);
            } else if (current == '"' || current == '\'') {
                tokenizeQuotedLiteral(tokenLine, tokenColumn);
            } else {
                tokenizeOperator(tokenLine, tokenColumn);
            }
        }
        tokens.add(new Token(EOF, "", line, column));
        return List.copyOf(tokens);
    }

    private void tokenizeIdentifier(int tokenLine, int tokenColumn) {
        StringBuilder value = new StringBuilder();
        while (!eof() && isIdentifierPart(peek())) {
            value.append(advance());
        }
        String spelling = value.toString();
        Token.TokenType type = KEYWORDS.getOrDefault(spelling, IDENTIFIER);
        add(type, spelling, tokenLine, tokenColumn);
        if (type == ASM) tokenizeAsmBlockIfPresent(tokenLine, tokenColumn);
    }

    private void tokenizeAsmBlockIfPresent(int tokenLine, int tokenColumn) {
        int openingBrace = index;
        while (openingBrace < source.length() && Character.isWhitespace(source.charAt(openingBrace))) openingBrace++;
        if (openingBrace >= source.length() || source.charAt(openingBrace) != '{') return;
        while (index < openingBrace) advance();
        advance();
        int bodyStart = index;
        int bodyLine = line;
        int bodyColumn = column;
        char quote = 0;
        boolean escaped = false;
        boolean comment = false;
        while (!eof()) {
            char current = peek();
            if (comment) {
                if (current == '\n' || current == '\r') comment = false;
                advance();
                continue;
            }
            if (quote != 0) {
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == quote) quote = 0;
                advance();
                continue;
            }
            if (current == ';') {
                comment = true;
                advance();
                continue;
            }
            if (current == '{') fail("Nested braces are not supported in asm blocks", line, column);
            if (current == '}') {
                add(ASM_BLOCK, source.substring(bodyStart, index), bodyLine, bodyColumn);
                advance();
                return;
            }
            if (current == '\'' || current == '"') quote = current;
            advance();
        }
        fail("Unterminated asm block", tokenLine, tokenColumn);
    }

    private void tokenizeNumber(int tokenLine, int tokenColumn) {
        StringBuilder spelling = new StringBuilder();
        int radixDigitCount = -1;
        boolean incompleteExponent = false;
        if (hasRadixPrefix()) {
            spelling.append(advance()).append(advance());
            int radix = spelling.charAt(1) == 'b' || spelling.charAt(1) == 'B' ? 2 : 16;
            radixDigitCount = 0;
            while (!eof() && (Character.digit(peek(), radix) >= 0 || peek() == '_')) {
                char digit = advance();
                spelling.append(digit);
                if (digit != '_') radixDigitCount++;
            }
        } else {
            while (!eof() && (Character.isDigit(peek()) || peek() == '_')) {
                spelling.append(advance());
            }
            if (!eof() && peek() == '.') {
                spelling.append(advance());
                while (!eof() && Character.isDigit(peek())) {
                    spelling.append(advance());
                }
            }
            if (!eof() && (peek() == 'e' || peek() == 'E')) {
                spelling.append(advance());
                if (!eof() && (peek() == '+' || peek() == '-')) {
                    spelling.append(advance());
                }
                int exponentDigits = 0;
                while (!eof() && Character.isDigit(peek())) {
                    spelling.append(advance());
                    exponentDigits++;
                }
                incompleteExponent = exponentDigits == 0;
            }
        }
        while (!eof() && "uUlLfF".indexOf(peek()) >= 0) {
            spelling.append(advance());
        }
        if (radixDigitCount == 0) {
            fail("Missing digits after numeric radix prefix", tokenLine, tokenColumn, spelling.length());
        }
        if (incompleteExponent) {
            fail("Incomplete numeric exponent", tokenLine, tokenColumn, spelling.length());
        }
        add(NUMBER, spelling.toString(), tokenLine, tokenColumn);
    }

    private void tokenizeSlash(int tokenLine, int tokenColumn) {
        advance();
        if (!eof() && peek() == '/') {
            while (!eof() && advance() != '\n') {
            }
        } else if (!eof() && peek() == '*') {
            advance();
            skipBlockComment(tokenLine, tokenColumn);
        } else if (!eof() && peek() == '=') {
            advance();
            add(DIV_EQUALS, "/=", tokenLine, tokenColumn);
        } else {
            add(F_SLASH, "/", tokenLine, tokenColumn);
        }
    }

    private void skipBlockComment(int tokenLine, int tokenColumn) {
        while (!eof()) {
            if (advance() == '*' && !eof() && peek() == '/') {
                advance();
                return;
            }
        }
        fail("Unterminated block comment", tokenLine, tokenColumn);
    }

    private void tokenizeQuotedLiteral(int tokenLine, int tokenColumn) {
        char quote = advance();
        String literalKind = quote == '"' ? "string" : "character";
        StringBuilder value = new StringBuilder();
        boolean closed = false;
        while (!eof()) {
            char current = advance();
            if (current == quote) {
                closed = true;
                break;
            }
            if (current == '\n' || current == '\r') {
                fail("Unescaped newline in " + literalKind + " literal", tokenLine, tokenColumn);
            }
            if (current == '\\') {
                if (eof()) {
                    break;
                }
                appendEscape(value, advance(), tokenLine, tokenColumn);
            } else {
                value.append(current);
            }
        }
        if (!closed) {
            fail("Unterminated " + literalKind + " literal", tokenLine, tokenColumn);
        }

        if (quote == '\'' && value.length() > 1) {
            fail("Character literal contains " + value.length() + " characters; use a string for multiple characters",
                    tokenLine, tokenColumn);
        }
        String data = quote == '\''
                ? Integer.toString(value.isEmpty() ? 0 : value.charAt(0))
                : value.toString();
        add(quote == '"' ? STRING : NUMBER, data, tokenLine, tokenColumn);
    }

    private void appendEscape(StringBuilder value, char escape, int tokenLine, int tokenColumn) {
        if (escape == 'x') {
            int decoded = 0;
            int digits = 0;
            while (!eof() && Character.digit(peek(), 16) >= 0) {
                decoded = (decoded << 4) | Character.digit(advance(), 16);
                digits++;
            }
            if (digits == 0) {
                fail("Expected hexadecimal escape digits", tokenLine, tokenColumn);
            }
            value.append((char) (decoded & 0xff));
        } else if (escape >= '0' && escape <= '7') {
            int decoded = escape - '0';
            for (int digitCount = 1; digitCount < 3 && !eof() && peek() >= '0' && peek() <= '7'; digitCount++) {
                decoded = (decoded << 3) | (advance() - '0');
            }
            value.append((char) (decoded & 0xff));
        } else {
            value.append(decodeEscape(escape));
        }
    }

    private static char decodeEscape(char escape) {
        return switch (escape) {
            case 'n' -> '\n';
            case 'r' -> '\r';
            case 't' -> '\t';
            case 'a' -> '\7';
            case 'b' -> '\b';
            case 'f' -> '\f';
            case 'v' -> '\13';
            default -> escape;
        };
    }

    private void tokenizeOperator(int tokenLine, int tokenColumn) {
        char first = advance();
        if (!eof()) {
            String pair = "" + first + peek();
            if ((pair.equals("<<") || pair.equals(">>")) && index + 1 < source.length()
                    && source.charAt(index + 1) == '=') {
                advance();
                advance();
                add(pair.equals("<<") ? SHIFT_LEFT_EQUALS : SHIFT_RIGHT_EQUALS,
                        pair + "=", tokenLine, tokenColumn);
                return;
            }
            Token.TokenType pairType = TWO_CHARACTER_OPERATORS.get(pair);
            if (pairType != null) {
                advance();
                add(pairType, pair, tokenLine, tokenColumn);
                return;
            }
        }
        Token.TokenType type = ONE_CHARACTER_OPERATORS.get(first);
        if (type == null) {
            fail("Unexpected character '" + first + "'", tokenLine, tokenColumn);
        }
        add(type, Character.toString(first), tokenLine, tokenColumn);
    }

    private boolean hasRadixPrefix() {
        if (index + 1 >= source.length() || source.charAt(index) != '0') {
            return false;
        }
        char prefix = source.charAt(index + 1);
        return prefix == 'x' || prefix == 'X' || prefix == 'b' || prefix == 'B';
    }

    private boolean startsNumber(char current) {
        return Character.isDigit(current)
                || current == '.' && index + 1 < source.length() && Character.isDigit(source.charAt(index + 1));
    }

    private static boolean isIdentifierStart(char value) {
        return Character.isLetter(value) || value == '_';
    }

    private static boolean isIdentifierPart(char value) {
        return Character.isLetterOrDigit(value) || value == '_';
    }

    private void add(Token.TokenType type, String data, int atLine, int atColumn) {
        tokens.add(new Token(type, data, atLine, atColumn));
    }

    private boolean eof() {
        return index >= source.length();
    }

    private char peek() {
        return source.charAt(index);
    }

    private char advance() {
        if ((index & 255) == 0) checkCancelled();
        char value = source.charAt(index++);
        if (value == '\r') {
            if (!eof() && source.charAt(index) == '\n') {
                index++;
            }
            line++;
            column = 1;
            return '\n';
        } else if (value == '\n') {
            line++;
            column = 1;
        } else {
            column++;
        }
        return value;
    }

    private void checkCancelled() {
        if (cancelled.getAsBoolean()) throw new CancellationException("Lexing was cancelled.");
    }

    private static void fail(String message, int line, int column) {
        fail(message, line, column, 1);
    }

    private static void fail(String message, int line, int column, int length) {
        throw new LexicalError(message, line, column, length);
    }
}
