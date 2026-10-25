package C8080;

import java.nio.file.Path;

/** One lexical unit with its position and, when available, original source context. */
public class Token {
    /** Lexical category of a C token. */
    public enum TokenType {
        IDENTIFIER, NUMBER, STRING,
        INT, CHAR, VOID, LONG, SHORT, FLOAT, DOUBLE, UNSIGNED, SIGNED, TYPEDEF, EXTERN, SIZEOF,
        ENUM, STRUCT, UNION, CONST, VOLATILE, STATIC, RETURN, IF, ELSE, WHILE, FOR, ASM, ASM_BLOCK,
        BREAK, CONTINUE, SWITCH, CASE, DEFAULT, DO,
        EQUALS, EQUAL_EQUAL, NOT_EQUAL, LESS, LESS_EQUAL, GREATER, GREATER_EQUAL,
        PLUS, MINUS, STAR, F_SLASH, PERCENT, BANG, AMP, PIPE, CARET, TILDE,
        AND_AND, OR_OR, PLUS_PLUS, MINUS_MINUS,
        PLUS_EQUALS, MINUS_EQUALS, STAR_EQUALS, DIV_EQUALS, MOD_EQUALS,
        AMP_EQUALS, PIPE_EQUALS, CARET_EQUALS, SHIFT_LEFT, SHIFT_RIGHT,
        SHIFT_LEFT_EQUALS, SHIFT_RIGHT_EQUALS,
        OPEN_PAREN, CLOSE_PAREN, OPEN_BRACE, CLOSE_BRACE, OPEN_BRACKET, CLOSE_BRACKET,
        QUESTION, ARROW, SEMICOLON, COMMA, COLON, PERIOD, ELLIPSIS, EOF
    }

    public final TokenType type;
    public final String data;
    public final int line;
    public final int column;
    public final Path sourcePath;
    public final String sourceLine;

    /** Creates a token with a default source position and no original source attachment. */
    public Token(TokenType type, String data) {
        this(type, data, 1, 1);
    }

    /** Creates a token with line and column metadata but no original file attachment. */
    public Token(TokenType type, String data, int line, int column) {
        this(type, data, line, column, null, "");
    }

    /** Creates a token with its source coordinates and the original line used for diagnostics. */
    public Token(TokenType type, String data, int line, int column, Path sourcePath, String sourceLine) {
        this.type = type;
        this.data = data;
        this.line = line;
        this.column = column;
        this.sourcePath = sourcePath;
        this.sourceLine = sourceLine;
    }

    /** Returns the token type and spelling for diagnostics. */
    @Override
    public String toString() {
        return "[type=" + type + ", data=" + data + "]";
    }
}
