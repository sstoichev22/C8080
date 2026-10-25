package C8080;

import static C8080.Token.TokenType.*;

import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;

/** Parses C tokens into declarations and statements while retaining declaration source locations. */
public class Parser {
    /** A parsed C expression. */
    public sealed interface Expr permits NumberExpr, FloatExpr, StringExpr, VariableExpr, MemberExpr, IndexExpr,
            UnaryExpr, BinaryExpr, CallExpr, AssignExpr, UpdateExpr, CastExpr, SizeofExpr, InitListExpr,
            ConditionalExpr, CommaExpr {}
    /** Integer constant with its C type. */
    public record NumberExpr(BigInteger value, CType type) implements Expr {
        /** Creates an int constant. */
        public NumberExpr(int value) {
            this(BigInteger.valueOf(value), CType.INT);
        }
    }
    /** Floating constant with its C type. */
    public record FloatExpr(double value, CType type) implements Expr {}
    /** String literal with decoded bytes. */
    public record StringExpr(String value) implements Expr {}
    /** Reference to a named object, function, or enumerator. */
    public record VariableExpr(String name) implements Expr {}
    /** Member access; pointer is true for -> and false for the dot operator. */
    public record MemberExpr(Expr base, String name, boolean pointer) implements Expr {}
    /** Array subscript base[index]. */
    public record IndexExpr(Expr base, Expr index) implements Expr {}
    /** Prefix unary operator such as -, !, ~, & or *. */
    public record UnaryExpr(Token.TokenType op, Expr value) implements Expr {}
    /** Binary arithmetic, bitwise, comparison, or logical operator. */
    public record BinaryExpr(Expr left, Token.TokenType op, Expr right) implements Expr {}
    /** Direct or indirect function call. */
    public record CallExpr(Expr callee, List<Expr> arguments) implements Expr {}
    /** Simple or compound assignment. */
    public record AssignExpr(Expr target, Token.TokenType op, Expr value) implements Expr {}
    /** Increment or decrement by amount, prefix or postfix. */
    public record UpdateExpr(Expr target, int amount, boolean prefix) implements Expr {}
    /** Explicit conversion to a type. */
    public record CastExpr(CType type, Expr value) implements Expr {}
    /** sizeof applied to a type or to an expression. */
    public record SizeofExpr(CType type, Expr value) implements Expr {}
    /** Brace-enclosed initializer list. */
    public record InitListExpr(List<Expr> values) implements Expr {}
    /** Conditional operator condition ? yes : no. */
    public record ConditionalExpr(Expr condition, Expr yes, Expr no) implements Expr {}
    /** Comma operator evaluating left then right. */
    public record CommaExpr(Expr left, Expr right) implements Expr {}
    /** Storage class of a declaration. */
    public enum Storage { AUTO, STATIC, EXTERN, TYPEDEF }
    /** A parsed C statement. */
    public sealed interface Stmt permits BlockStmt, DeclStmt, DeclGroup, EmptyStmt, ExprStmt, ReturnStmt, IfStmt,
            WhileStmt, DoWhileStmt, ForStmt, SwitchStmt, BreakStmt, ContinueStmt, AsmStmt {}
    /** Compound statement with its own scope. */
    public record BlockStmt(List<Stmt> statements) implements Stmt {}
    /** One declared name with type, optional initializer, and storage class. */
    public record DeclStmt(CType type, String name, Expr initializer, Storage storage) implements Stmt {}
    /** Declarations that share one declaration statement. */
    public record DeclGroup(List<DeclStmt> declarations) implements Stmt {}
    /** Empty statement consisting of a semicolon. */
    public record EmptyStmt() implements Stmt {}
    /** Expression evaluated for its effects. */
    public record ExprStmt(Expr value) implements Stmt {}
    /** return statement; value is null for a bare return. */
    public record ReturnStmt(Expr value) implements Stmt {}
    /** if statement; no is null when there is no else branch. */
    public record IfStmt(Expr condition, Stmt yes, Stmt no) implements Stmt {}
    /** while loop. */
    public record WhileStmt(Expr condition, Stmt body) implements Stmt {}
    /** do-while loop. */
    public record DoWhileStmt(Stmt body, Expr condition) implements Stmt {}
    /** for loop; omitted clauses are null. */
    public record ForStmt(Stmt init, Expr condition, Expr update, Stmt body) implements Stmt {}
    /** One case label value (null for default) and its statements. */
    public record SwitchCase(BigInteger value, List<Stmt> statements) {}
    /** switch statement with its cases in source order. */
    public record SwitchStmt(Expr value, List<SwitchCase> cases) implements Stmt {}
    /** break statement. */
    public record BreakStmt() implements Stmt {}
    /** continue statement. */
    public record ContinueStmt() implements Stmt {}
    /** Inline asm block with its verbatim source text. */
    public record AsmStmt(String source) implements Stmt {}
    /** Function prototype or definition; body is null for a prototype. */
    public record Function(
            CType type, String name, List<DeclStmt> parameters, boolean variadic, Storage storage, BlockStmt body) {}
    /** Translation unit: globals, functions, and the functions visible at each global. */
    public record Unit(List<DeclStmt> globals, List<Function> functions, Map<DeclStmt, Set<String>> visibleAtGlobal) {}
    private record Declarator(CType type, String name, Token identifier) {}
    /** Inclusive generated-token bounds of an AST node; token coordinates precede preprocessing source mapping. */
    public record SourceSpan(Token first, Token last) {}
    private final Map<Object, Token> identifiers = new IdentityHashMap<>();
    private final Map<Object, SourceSpan> spans = new IdentityHashMap<>();

    /** Returns exact identifier tokens for declarations and variable references, keyed by AST identity. */
    public Map<Object, Token> identifiers() {
        return Collections.unmodifiableMap(identifiers);
    }

    /** Returns generated-token bounds keyed by AST identity; parentheses do not replace inner expression bounds. */
    public Map<Object, SourceSpan> spans() {
        return Collections.unmodifiableMap(spans);
    }

    private <T> T located(T node, int start) {
        if (i > start) spans.putIfAbsent(node, new SourceSpan(tokens.get(start), previous()));
        return node;
    }
    private final List<Token> tokens;
    private BooleanSupplier cancelled = () -> false;
    private final Map<String, CType> types = new LinkedHashMap<>();
    private final Map<String, BigInteger> constants = new LinkedHashMap<>();
    private final Deque<Set<String>> tagScopes = new ArrayDeque<>();
    private final Deque<Set<String>> typedefScopes = new ArrayDeque<>();
    private final Deque<Map<String, String>> ordinaryScopes = new ArrayDeque<>();
    private Map<String, String> bodyParameters = Map.of();
    private int i, anonymous;
    private final Map<Object, Token> positions = new IdentityHashMap<>();
    /** Returns identity-keyed source locations for AST nodes created by this parser. */
    public Map<Object, Token> positions() {
        return positions;
    }

    /** Returns the token currently being parsed, for diagnostic translation. */
    public Token currentToken() {
        return peek();
    }

    /** Creates a parser over a complete token stream ending with EOF. */
    public Parser(List<Token> tokens) {
        this(tokens, () -> false);
    }

    Parser(List<Token> tokens, BooleanSupplier cancellation) {
        cancelled = cancellation == null ? () -> false : cancellation;
        checkCancelled();
        List<Token> input = Objects.requireNonNull(tokens, "tokens");
        int expectedSize = input.size();
        ArrayList<Token> copied = new ArrayList<>();
        boolean earlyEof = false;
        int index = 0;
        for (Token token : input) {
            if ((index & 255) == 0) checkCancelled();
            Token present = Objects.requireNonNull(token, "tokens contains null");
            if (present.type == EOF && index != expectedSize - 1) earlyEof = true;
            copied.add(present);
            index++;
        }
        checkCancelled();
        if (copied.isEmpty() || index != expectedSize || copied.get(copied.size() - 1).type != EOF || earlyEof) {
            throw new IllegalArgumentException("Token stream must contain exactly one EOF token at the end.");
        }
        this.tokens = Collections.unmodifiableList(copied);
        tagScopes.push(new HashSet<>());
        typedefScopes.push(new HashSet<>());
        ordinaryScopes.push(new LinkedHashMap<>());
    }

    /** Parses the complete token stream as one translation unit. */
    public Unit parse() {
        return parse(cancelled);
    }

    Unit parse(BooleanSupplier cancellation) {
        BooleanSupplier previousCancellation = cancelled;
        cancelled = cancellation == null ? () -> false : cancellation;
        try {
            return parseCancellable();
        } finally {
            cancelled = previousCancellation;
        }
    }

    private Unit parseCancellable() {
        List<DeclStmt> globals = new ArrayList<>();
        List<Function> functions = new ArrayList<>();
        Map<DeclStmt, Set<String>> visibleAtGlobal = new IdentityHashMap<>();
        Set<String> declaredFunctions = new LinkedHashSet<>();

        while (!check(EOF)) {
            checkCancelled();
            Storage declarationStorage = storage();
            CType baseType = parseType();
            if (match(SEMICOLON)) {
                continue;
            }

            Declarator declaration = declarator(baseType, false);
            Token declarationAt = declaration.identifier;
            if (match(OPEN_PAREN)) {
                Function function = parseFunction(declaration, declarationAt, declarationStorage, declaredFunctions);
                functions.add(function);
            } else {
                List<DeclStmt> declarations = declarationList(baseType, declaration, declarationStorage);
                globals.addAll(declarations);
                for (DeclStmt global : declarations) {
                    visibleAtGlobal.put(global, Set.copyOf(declaredFunctions));
                }
            }
        }
        return new Unit(List.copyOf(globals), List.copyOf(functions), Collections.unmodifiableMap(visibleAtGlobal));
    }

    private Function parseFunction(
            Declarator declaration, Token declarationAt, Storage storage, Set<String> declaredFunctions) {
        if (typedefScopes.peek().contains(declaration.name)) {
            fail("Conflicting declaration for " + declaration.name
                    + ".\nExpected: " + ordinaryScopes.peek().get(declaration.name)
                    + "\nPresented: " + declaration.type + " " + declaration.name + "(...) function");
        }
        ordinaryScopes.peek().put(declaration.name, declaration.type + " " + declaration.name + "(...) function");
        declaredFunctions.add(declaration.name);

        Map<String, CType> previousTypes = new LinkedHashMap<>(types);
        Map<String, BigInteger> previousConstants = new LinkedHashMap<>(constants);
        List<DeclStmt> parameters = new ArrayList<>();
        boolean variadic = parseParameters(parameters);
        consume(CLOSE_PAREN, "Expected ')' after parameters.");
        for (DeclStmt parameter : parameters) {
            types.remove(parameter.name());
            constants.remove(parameter.name());
        }

        BlockStmt body = null;
        if (!match(SEMICOLON)) {
            bodyParameters = new LinkedHashMap<>();
            for (DeclStmt parameter : parameters) {
                bodyParameters.put(parameter.name(), "parameter " + parameter.type() + " " + parameter.name());
            }
            Stmt parsedBody = statement();
            if (!(parsedBody instanceof BlockStmt block)) {
                fail("Function body must be a block.");
            }
            body = (BlockStmt) parsedBody;
        }

        Function function =
                new Function(declaration.type, declaration.name, List.copyOf(parameters), variadic, storage, body);
        positions.put(function, declarationAt);
        identifiers.put(function, declarationAt);
        types.clear();
        types.putAll(previousTypes);
        constants.clear();
        constants.putAll(previousConstants);
        return function;
    }

    private boolean parseParameters(List<DeclStmt> parameters) {
        if (check(VOID) && ahead(1) == CLOSE_PAREN) {
            advance();
            return false;
        }
        if (check(CLOSE_PAREN)) {
            return false;
        }
        boolean variadic = false;
        do {
            if (match(ELLIPSIS)) {
                variadic = true;
                break;
            }
            Declarator parameter = declarator(parseType(), true);
            DeclStmt declared = new DeclStmt(parameter.type.decay(), parameter.name, null, Storage.AUTO);
            parameters.add(declared);
            if (parameter.identifier != null) {
                positions.put(declared, parameter.identifier);
                identifiers.put(declared, parameter.identifier);
            }
        } while (match(COMMA));
        return variadic;
    }
    private Storage storage() {
        if (match(STATIC))
            return Storage.STATIC;
        if (match(EXTERN))
            return Storage.EXTERN;
        if (match(TYPEDEF))
            return Storage.TYPEDEF;
        return Storage.AUTO;
    }

    private List<DeclStmt> declarationList(CType base, Declarator first, Storage storage) {
        List<DeclStmt> declarations = new ArrayList<>();
        Declarator declaration = first;
        do {
            Token declarationAt = declaration.identifier;
            Expr initializer = match(EQUALS) ? initializer() : null;
            CType type = inferArrayBound(declaration.type, initializer);
            String presented = (storage == Storage.TYPEDEF ? "typedef " : "") + type + " " + declaration.name;
            validateOrdinaryDeclaration(declaration.name, presented, storage);
            ordinaryScopes.peek().put(declaration.name, presented);

            if (storage == Storage.TYPEDEF) {
                declareTypedef(declaration.name, type, initializer);
            } else {
                types.remove(declaration.name);
                constants.remove(declaration.name);
                DeclStmt declared = new DeclStmt(type, declaration.name, initializer, storage);
                declarations.add(declared);
                positions.put(declared, declarationAt);
                identifiers.put(declared, declarationAt);
            }
            if (!match(COMMA)) {
                break;
            }
            declaration = declarator(base, false);
        } while (true);

        consume(SEMICOLON, "Expected ';' after declaration.");
        return declarations;
    }

    private CType inferArrayBound(CType type, Expr initializer) {
        if (type.kind != CType.Kind.ARRAY || type.count != 0) {
            return type;
        }
        int count = initializer instanceof StringExpr string ? string.value.length() + 1
                : initializer instanceof InitListExpr list   ? list.values.size()
                                                             : 0;
        return CType.array(type.element, count);
    }

    private void validateOrdinaryDeclaration(String name, String presented, Storage storage) {
        String previous = ordinaryScopes.peek().get(name);
        boolean conflictsWithTypedef = storage != Storage.TYPEDEF && typedefScopes.peek().contains(name);
        boolean conflictsWithObject =
                storage == Storage.TYPEDEF && previous != null && !typedefScopes.peek().contains(name);
        boolean conflictsWithParameter = previous != null && previous.startsWith("parameter ");
        boolean conflictsWithEnumerator = previous != null && previous.startsWith("enumerator ");
        if (conflictsWithTypedef || conflictsWithObject || conflictsWithParameter || conflictsWithEnumerator) {
            fail("Conflicting declaration for " + name + ".\nExpected: " + previous + "\nPresented: " + presented
                    + "\nTypedefs, objects and parameters share the ordinary identifier namespace in this scope.");
        }
    }

    private void declareTypedef(String name, CType type, Expr initializer) {
        if (initializer != null) {
            fail("A typedef cannot have an initializer.");
        }
        CType previous = types.get(name);
        if (typedefScopes.peek().contains(name) && previous != null) {
            if (!previous.sameDeclaration(type)) {
                fail("Conflicting typedef for " + name + ".\nExpected: " + previous + "\nPresented: " + type);
            }
            type = previous.compositeDeclaration(type);
        }
        types.put(name, type);
        typedefScopes.peek().add(name);
    }

    private Expr initializer() {
        if (!match(OPEN_BRACE))
            return assignment();
        List<Expr> values = new ArrayList<>();
        if (!check(CLOSE_BRACE)) {
            do {
                values.add(initializer());
            } while (match(COMMA) && !check(CLOSE_BRACE));
        }
        consume(CLOSE_BRACE, "Expected '}' after initializer.");
        return new InitListExpr(List.copyOf(values));
    }
    private Declarator declarator(CType base, boolean optionalName) {
        if (match(OPEN_PAREN)) {
            consume(STAR, "Expected '*' in function pointer declarator.");
            boolean pointerVolatile = qualifiers();
            Token identifier = check(IDENTIFIER) ? advance()
                    : optionalName ? null : consume(IDENTIFIER, "Expected function pointer name.");
            String name = identifier == null ? "_parameter_" + anonymous++ : identifier.data;
            consume(CLOSE_PAREN, "Expected ')' after function pointer name.");
            if (check(OPEN_BRACKET)) {
                List<Integer> dimensions = new ArrayList<>();
                while (match(OPEN_BRACKET)) {
                    int count = check(CLOSE_BRACKET) ? 0 : constant(expression()).intValueExact();
                    consume(CLOSE_BRACKET, "Expected ']'.");
                    dimensions.add(count);
                }
                CType array = base;
                for (int n = dimensions.size() - 1; n >= 0; n--) array = CType.array(array, dimensions.get(n));
                CType pointer = CType.pointer(array);
                return new Declarator(pointerVolatile ? pointer.asVolatile() : pointer, name, identifier);
            }
            consume(OPEN_PAREN, "Expected function pointer parameter list or array bound.");
            List<CType> parameters = new ArrayList<>();
            boolean variadic = false;
            if (check(VOID) && ahead(1) == CLOSE_PAREN)
                advance();
            else if (!check(CLOSE_PAREN))
                do {
                    if (match(ELLIPSIS)) {
                        variadic = true;
                        break;
                    }
                    parameters.add(declarator(parseType(), true).type.decay());
                } while (match(COMMA));
            consume(CLOSE_PAREN, "Expected ')' after function pointer parameters.");
            CType pointer = CType.pointer(CType.function(base, parameters, variadic));
            return new Declarator(pointerVolatile ? pointer.asVolatile() : pointer, name, identifier);
        }
        CType type = base;
        while (match(STAR)) {
            type = CType.pointer(type);
            if (qualifiers())
                type = type.asVolatile();
        }
        Token identifier = check(IDENTIFIER) ? advance()
                : optionalName ? null : consume(IDENTIFIER, "Expected declaration name.");
        String name = identifier == null ? "_parameter_" + anonymous++ : identifier.data;
        List<Integer> dimensions = new ArrayList<>();
        while (match(OPEN_BRACKET)) {
            int count = check(CLOSE_BRACKET) ? 0 : constant(expression()).intValueExact();
            consume(CLOSE_BRACKET, "Expected ']'.");
            dimensions.add(count);
        }
        for (int n = dimensions.size() - 1; n >= 0; n--) type = CType.array(type, dimensions.get(n));
        return new Declarator(type, name, identifier);
    }
    private CType parseType() {
        boolean isVolatile = qualifiers();
        boolean unsigned = match(UNSIGNED), signed = !unsigned&& match(SIGNED);
        isVolatile |= qualifiers();
        CType type;
        if (match(INT))
            type = unsigned ? CType.UINT : CType.INT;
        else if (match(CHAR))
            type = CType.integer(signed ? "signed char" : unsigned ? "unsigned char" : "char", 1, !signed);
        else if (match(SHORT)) {
            isVolatile |= qualifiers();
            match(INT);
            type = CType.integer("short", 2, unsigned);
        } else if (match(LONG)) {
            isVolatile |= qualifiers();
            if (match(LONG))
                isVolatile |= qualifiers();
            match(INT);
            type = CType.integer("long", 8, unsigned);
        } else if (match(FLOAT))
            type = CType.FLOAT;
        else if (match(DOUBLE))
            type = CType.DOUBLE;
        else if (match(VOID))
            type = CType.VOID;
        else if (match(ENUM))
            type = parseEnum();
        else if (match(STRUCT, UNION)) {
            boolean union = previous().type == UNION;
            String tag = check(IDENTIFIER) ? advance().data : "_aggregate_" + anonymous++;
            String name = (union ? "union " : "struct ") + tag;

            boolean declaresTag = check(OPEN_BRACE) || check(SEMICOLON);
            if (!types.containsKey(name) || declaresTag && !tagScopes.peek().contains(name)) {
                type = CType.aggregate(name, union);
                types.put(name, type);
                tagScopes.peek().add(name);
            } else
                type = types.get(name);
            if (match(OPEN_BRACE)) {
                List<CType.Field> fields = new ArrayList<>();
                while (!check(CLOSE_BRACE) && !check(EOF)) {
                    CType fieldBase = parseType();
                    Declarator field = declarator(fieldBase, false);
                    do {
                        fields.add(new CType.Field(field.name, field.type, 0));
                        if (!match(COMMA))
                            break;
                        field = declarator(fieldBase, false);
                    } while (true);
                    consume(SEMICOLON, "Expected ';' after field.");
                }
                consume(CLOSE_BRACE, "Expected '}' after aggregate.");
                type.define(fields);
            }
        } else if (check(IDENTIFIER) && peek().data.equals("bool")) {
            advance();
            type = CType.integer("bool", 1, true);
        } else if (check(IDENTIFIER) && types.containsKey(peek().data))
            type = types.get(advance().data);
        else if (check(IDENTIFIER) && peek().data.matches("u?int[0-9]+")) {
            Token typeToken = advance();
            String name = typeToken.data;
            int width = integerWidth(typeToken);
            type = CType.integer(name, (width + 7) / 8, name.startsWith("u"));
        } else if (unsigned || signed)
            type = unsigned ? CType.UINT : CType.INT;
        else {
            fail("Expected a C type."
                    + (check(IDENTIFIER) ? " '" + peek().data
                                            + ("' has not been declared. Include its header or declare the type before "
                                               + "this use.")
                                         : ""));
            return CType.INT;
        }
        isVolatile |= qualifiers();
        return isVolatile ? type.asVolatile() : type;
    }

    private int integerWidth(Token typeToken) {
        String name = typeToken.data;
        int digitStart = name.startsWith("u") ? 4 : 3;
        int width = 0;
        for (int index = digitStart; index < name.length(); index++) {
            width = Math.min(CType.MAX_INTEGER_BITS + 1, width * 10 + name.charAt(index) - '0');
        }
        if (width < 1 || width > CType.MAX_INTEGER_BITS) {
            throw new SourceDiagnostic(typeToken, "intN/uintN supports 1 to " + CType.MAX_INTEGER_BITS
                    + (" bits (VCC_INT_MAX_BITS in limits.h). Larger integers cannot fit the compiler's bounded "
                       + "temporary stack; use an array and chunked arithmetic instead."));
        }
        return width;
    }

    private CType parseEnum() {
        String tag = check(IDENTIFIER) ? advance().data : "_enum_" + anonymous++;
        types.put("enum " + tag, CType.INT);
        if (match(OPEN_BRACE)) {
            BigInteger next = BigInteger.ZERO;
            while (!check(CLOSE_BRACE)) {
                String name = consume(IDENTIFIER, "Expected enumerator name.").data;
                if (match(EQUALS)) next = constant(assignment());
                if (ordinaryScopes.peek().containsKey(name)) fail("Conflicting declaration for enumerator " + name);
                constants.put(name, next);
                ordinaryScopes.peek().put(name, "enumerator " + name);
                next = next.add(BigInteger.ONE);
                if (!match(COMMA)) break;
            }
            consume(CLOSE_BRACE, "Expected '}' after enum.");
        }
        return CType.INT;
    }

    private boolean qualifiers() {
        boolean isVolatile = false;
        while (match(CONST, VOLATILE)) isVolatile |= previous().type == VOLATILE;
        return isVolatile;
    }
    private boolean typeAhead() {
        return switch (peek().type) {
            case INT, CHAR, VOID, LONG, SHORT, FLOAT, DOUBLE, UNSIGNED, SIGNED, CONST, VOLATILE, ENUM, STRUCT, UNION ->
                true;
            case IDENTIFIER ->
                peek().data.equals("bool") || types.containsKey(peek().data) || peek().data.matches("u?int[0-9]+");
            default -> false;
        };
    }
    private Stmt statement() {
        int start = i;
        Token at = peek();
        Stmt result = statementValue();
        positions.put(result, at);
        return located(result, start);
    }
    private Stmt statementValue() {
        if (match(ASM)) {
            Token assembly = consume(ASM_BLOCK, "Expected an asm block after 'asm'.");
            match(SEMICOLON);
            return new AsmStmt(assembly.data);
        }
        if (match(OPEN_BRACE)) {
            Map<String, CType> savedTypes = new LinkedHashMap<>(types);
            Map<String, BigInteger> savedConstants = new LinkedHashMap<>(constants);
            tagScopes.push(new HashSet<>());
            typedefScopes.push(new HashSet<>());
            ordinaryScopes.push(new LinkedHashMap<>(bodyParameters));
            bodyParameters = Map.of();
            try {
                List<Stmt> body = new ArrayList<>();
                while (!check(CLOSE_BRACE) && !check(EOF)) body.add(statement());
                consume(CLOSE_BRACE, "Expected '}' after block.");
                return new BlockStmt(List.copyOf(body));
            } finally {
                tagScopes.pop();
                types.clear();
                types.putAll(savedTypes);
                typedefScopes.pop();
                ordinaryScopes.pop();
                constants.clear();
                constants.putAll(savedConstants);
            }
        }
        if (match(SEMICOLON))
            return new EmptyStmt();
        if (check(STATIC) || check(EXTERN) || check(TYPEDEF) || typeAhead()) {
            Storage storage = storage();
            CType base = parseType();
            if (match(SEMICOLON))
                return new EmptyStmt();
            return new DeclGroup(List.copyOf(declarationList(base, declarator(base, false), storage)));
        }
        if (match(RETURN)) {
            Expr value = check(SEMICOLON) ? null : expression();
            consume(SEMICOLON, "Expected ';' after return.");
            return new ReturnStmt(value);
        }
        if (match(IF)) {
            Expr condition = parenthesized();
            Stmt yes = statement(), no = match(ELSE) ? statement() : null;
            return new IfStmt(condition, yes, no);
        }
        if (match(WHILE))
            return new WhileStmt(parenthesized(), statement());
        if (match(DO)) {
            Stmt body = statement();
            consume(WHILE, "Expected while after do.");
            Expr condition = parenthesized();
            consume(SEMICOLON, "Expected ';' after do-while.");
            return new DoWhileStmt(body, condition);
        }
        if (match(FOR)) {
            Map<String, CType> savedTypes = new LinkedHashMap<>(types);
            Map<String, BigInteger> savedConstants = new LinkedHashMap<>(constants);
            tagScopes.push(new HashSet<>());
            typedefScopes.push(new HashSet<>());
            ordinaryScopes.push(new LinkedHashMap<>());
            try {
                consume(OPEN_PAREN, "Expected '(' after for.");
                Stmt init;
                if (check(SEMICOLON)) {
                    advance();
                    init = null;
                } else if (typeAhead() || check(STATIC) || check(EXTERN) || check(TYPEDEF))
                    init = statement();
                else {
                    init = new ExprStmt(expression());
                    consume(SEMICOLON, "Expected ';' after initializer.");
                }
                Expr condition = check(SEMICOLON) ? null : expression();
                consume(SEMICOLON, "Expected ';' after condition.");
                Expr update = check(CLOSE_PAREN) ? null : expression();
                consume(CLOSE_PAREN, "Expected ')' after for clauses.");
                return new ForStmt(init, condition, update, statement());
            } finally {
                tagScopes.pop();
                types.clear();
                types.putAll(savedTypes);
                typedefScopes.pop();
                ordinaryScopes.pop();
                constants.clear();
                constants.putAll(savedConstants);
            }
        }
        if (match(SWITCH)) {
            Expr value = parenthesized();
            consume(OPEN_BRACE, "Expected '{' after switch.");
            List<SwitchCase> cases = new ArrayList<>();
            while (!check(CLOSE_BRACE) && !check(EOF)) {
                BigInteger selector;
                if (match(CASE))
                    selector = constant(assignment());
                else if (match(DEFAULT))
                    selector = null;
                else {
                    fail("Expected case or default.");
                    return null;
                }
                consume(COLON, "Expected ':' after case.");
                List<Stmt> body = new ArrayList<>();
                while (!check(CASE) && !check(DEFAULT) && !check(CLOSE_BRACE) && !check(EOF)) body.add(statement());
                cases.add(new SwitchCase(selector, List.copyOf(body)));
            }
            consume(CLOSE_BRACE, "Expected '}' after switch.");
            return new SwitchStmt(value, List.copyOf(cases));
        }
        if (match(BREAK)) {
            consume(SEMICOLON, "Expected ';'.");
            return new BreakStmt();
        }
        if (match(CONTINUE)) {
            consume(SEMICOLON, "Expected ';'.");
            return new ContinueStmt();
        }
        Expr expression = expression();
        consume(SEMICOLON, "Expected ';' after expression.");
        return new ExprStmt(expression);
    }
    private Expr parenthesized() {
        consume(OPEN_PAREN, "Expected '('.");
        Expr value = expression();
        consume(CLOSE_PAREN, "Expected ')'.");
        return value;
    }
    private Expr expression() {
        Expr value = assignment();
        while (match(COMMA)) value = new CommaExpr(value, assignment());
        return value;
    }
    private Expr assignment() {
        int start = i;
        Token at = peek();
        Expr result = assignmentValue();
        positions.putIfAbsent(result, at);
        return located(result, start);
    }
    private Expr assignmentValue() {
        Expr left = conditional();
        if (match(EQUALS, PLUS_EQUALS, MINUS_EQUALS, STAR_EQUALS, DIV_EQUALS, MOD_EQUALS, AMP_EQUALS, PIPE_EQUALS,
                    CARET_EQUALS, SHIFT_LEFT_EQUALS, SHIFT_RIGHT_EQUALS))
            return new AssignExpr(left, previous().type, assignment());
        return left;
    }
    private Expr conditional() {
        Expr value = binary(1);
        if (match(QUESTION)) {
            Expr yes = expression();
            consume(COLON, "Expected ':' in conditional.");
            return new ConditionalExpr(value, yes, conditional());
        }
        return value;
    }
    private Expr binary(int minimum) {
        int start = i;
        Expr left = unary();
        while (precedence(peek().type) >= minimum) {
            Token.TokenType op = advance().type;
            left = located(new BinaryExpr(left, op, binary(precedence(op) + 1)), start);
        }
        return left;
    }
    private Expr unary() {
        int start = i;
        return located(unaryValue(), start);
    }
    private Expr unaryValue() {
        if (match(PLUS_PLUS, MINUS_MINUS)) {
            Token.TokenType op = previous().type;
            return new UpdateExpr(unary(), op == PLUS_PLUS ? 1 : -1, true);
        }
        if (match(PLUS, MINUS, BANG, TILDE, AMP, STAR))
            return new UnaryExpr(previous().type, unary());
        if (match(SIZEOF)) {
            if (match(OPEN_PAREN)) {
                if (typeAhead()) {
                    CType type = abstractType();
                    consume(CLOSE_PAREN, "Expected ')' after sizeof type.");
                    return new SizeofExpr(type, null);
                }
                Expr value = expression();
                consume(CLOSE_PAREN, "Expected ')' after sizeof.");
                return new SizeofExpr(null, value);
            }
            return new SizeofExpr(null, unary());
        }
        if (check(OPEN_PAREN)) {
            int save = i;
            advance();
            if (typeAhead()) {
                CType type = abstractType();
                consume(CLOSE_PAREN, "Expected ')' after cast type.");
                return new CastExpr(type, unary());
            }
            i = save;
        }
        Expr value = primary();
        while (true) {
            if (match(OPEN_PAREN)) {
                List<Expr> arguments = new ArrayList<>();
                if (!check(CLOSE_PAREN))
                    do {
                        arguments.add(assignment());
                    } while (match(COMMA));
                consume(CLOSE_PAREN, "Expected ')' after arguments.");
                Token at = positions.get(value);
                value = new CallExpr(value, List.copyOf(arguments));
                if (at != null)
                    positions.put(value, at);
            } else if (match(OPEN_BRACKET)) {
                Expr index = expression();
                consume(CLOSE_BRACKET, "Expected ']' after index.");
                value = new IndexExpr(value, index);
            } else if (match(PERIOD, ARROW)) {
                boolean pointer = previous().type == ARROW;
                value = new MemberExpr(value, consume(IDENTIFIER, "Expected field name.").data, pointer);
            } else if (match(PLUS_PLUS, MINUS_MINUS))
                value = new UpdateExpr(value, previous().type == PLUS_PLUS ? 1 : -1, false);
            else
                break;
        }
        return value;
    }
    private CType abstractType() {
        CType type = parseType();
        while (match(STAR)) {
            type = CType.pointer(type);
            if (qualifiers())
                type = type.asVolatile();
        }
        while (match(OPEN_BRACKET)) {
            int count = constant(expression()).intValueExact();
            consume(CLOSE_BRACKET, "Expected ']'.");
            type = CType.array(type, count);
        }
        return type;
    }
    private Expr primary() {
        int start = i;
        Token at = peek();
        Expr result = primaryValue();
        positions.putIfAbsent(result, at);
        if (result instanceof VariableExpr && at.type == IDENTIFIER) identifiers.put(result, at);
        return located(result, start);
    }
    private Expr primaryValue() {
        if (match(NUMBER))
            return numeric(previous().data);
        if (match(STRING)) {
            StringBuilder value = new StringBuilder(previous().data);
            while (match(STRING)) value.append(previous().data);
            return new StringExpr(value.toString());
        }
        if (match(IDENTIFIER)) {
            String name = previous().data;
            if (name.equals("true") || name.equals("false")) // built-in like bool; there is no <stdbool.h>
                return new NumberExpr(name.equals("true") ? BigInteger.ONE : BigInteger.ZERO, CType.INT);
            BigInteger value = constants.get(name);
            return value == null ? new VariableExpr(name) : new NumberExpr(value, CType.INT);
        }
        if (match(OPEN_PAREN)) {
            Expr value = expression();
            consume(CLOSE_PAREN, "Expected ')'.");
            return value;
        }
        fail("Expected expression.");
        return null;
    }
    private Expr numeric(String raw) {
        String text = raw.replace("_", "");
        boolean hex = text.startsWith("0x") || text.startsWith("0X"),
                binary = text.startsWith("0b") || text.startsWith("0B");
        if (!hex && !binary && (text.contains(".") || text.matches(".*[eE].*") || text.matches(".*[fF]$"))) {
            boolean single = text.matches(".*[fF]$");
            return new FloatExpr(
                    Double.parseDouble(text.replaceAll("[fFlL]$", "")), single ? CType.FLOAT : CType.DOUBLE);
        }
        boolean unsigned = text.matches(".*[uU].*"), wide = text.matches(".*[lL].*");
        text = text.replaceAll("[uUlL]+$", "");
        int radix = hex ? 16 : binary ? 2 : text.startsWith("0") && text.length() > 1 ? 8 : 10;
        BigInteger value = new BigInteger(hex || binary ? text.substring(2) : text, radix);
        int width = wide ? 8 : 4;
        if (value.bitLength() > (unsigned ? width * 8 : width * 8 - 1)) {
            if ((hex || binary) && !wide && value.bitLength() <= 32)
                unsigned = true;
            else
                width = Math.max(8, ((value.bitLength() + 8) / 8 + 3) / 4 * 4);
        }
        return new NumberExpr(value, CType.integer((unsigned ? "uint" : "int") + (width * 8), width, unsigned));
    }
    private int precedence(Token.TokenType type) {
        return switch (type) {
            case OR_OR -> 1;
            case AND_AND -> 2;
            case PIPE -> 3;
            case CARET -> 4;
            case AMP -> 5;
            case EQUAL_EQUAL, NOT_EQUAL -> 6;
            case LESS, LESS_EQUAL, GREATER, GREATER_EQUAL -> 7;
            case SHIFT_LEFT, SHIFT_RIGHT -> 8;
            case PLUS, MINUS -> 9;
            case STAR, F_SLASH, PERCENT -> 10;
            default -> -1;
        };
    }
    /** Parses and evaluates an integer constant expression; throws IllegalArgumentException when it is not constant. */
    public static BigInteger parseIntegerConstantExpression(String source) {
        return parseIntegerConstantExpression(source, () -> false);
    }
    static BigInteger parseIntegerConstantExpression(String source, BooleanSupplier cancellation) {
        BooleanSupplier callback = cancellation == null ? () -> false : cancellation;
        if (callback.getAsBoolean()) throw new CancellationException("Parsing was cancelled.");
        Parser parser = new Parser(new Lexer(source).tokenize(callback), callback);
        Expr expression = parser.expression();
        parser.consume(EOF, "Unexpected token in constant expression.");
        parser.checkCancelled();
        ConstantEvaluator.Value evaluated = ConstantEvaluator.evaluate(expression, callback);
        parser.checkCancelled();
        if (evaluated.type().kind != CType.Kind.INTEGER)
            throw new IllegalArgumentException("Expected an integer constant expression.");
        return evaluated.integer();
    }
    /** Evaluates an integer constant expression that must fit in int. */
    public static int parseConstantExpression(String source) {
        return parseIntegerConstantExpression(source).intValue();
    }
    /** Evaluates an already parsed integer constant expression. */
    public static BigInteger constant(Expr expression) {
        ConstantEvaluator.Value value = ConstantEvaluator.evaluate(expression);
        if (value.type().kind != CType.Kind.INTEGER)
            throw new IllegalArgumentException("Expected an integer constant expression.");
        return value.integer();
    }
    private boolean match(Token.TokenType... types) {
        for (Token.TokenType type : types)
            if (check(type)) {
                advance();
                return true;
            }
        return false;
    }
    private boolean check(Token.TokenType type) {
        return peek().type == type;
    }
    private Token.TokenType ahead(int distance) {
        return tokens.get(Math.min(i + distance, tokens.size() - 1)).type;
    }
    private Token advance() {
        checkCancelled();
        Token token = peek();
        if (!check(EOF))
            i++;
        return token;
    }
    private Token previous() {
        return tokens.get(i - 1);
    }
    private Token peek() {
        return tokens.get(Math.min(i, tokens.size() - 1));
    }
    private Token consume(Token.TokenType type, String message) {
        if (check(type))
            return advance();
        if (type == SEMICOLON && i > 0) {
            Token following = peek();
            String insertion = following.type == EOF
                    ? " Insert ';' at the end of the input to finish the statement."
                    : " Insert ';' before this token to finish the statement.";
            throw new SourceDiagnostic(following, message + insertion);
        }
        fail(message);
        return peek();
    }
    private void fail(String message) {
        throw new SourceDiagnostic(
                peek(), message + "\nCheck the highlighted token and the punctuation immediately before it.");
    }

    private void checkCancelled() {
        if (cancelled.getAsBoolean()) throw new CancellationException("Parsing was cancelled.");
    }
}
