package C8080;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Coordinates preprocessing, parsing, code generation, optimization, and runtime linking. */
public class Compiler {
    private static final Pattern LOCATION = Pattern.compile("line (\\d+), column (\\d+)");
    private static final Pattern ASSEMBLY_LABEL = Pattern.compile("(?m)^\\s*([A-Za-z_][A-Za-z_0-9]*)\\s*:");
    private static final Pattern ASSEMBLY_DECLARATION = Pattern.compile("(?m)^\\s*(?i:extern|public|global)\\b[^\\n]*");
    private static final Pattern ASSEMBLY_SYMBOL = Pattern.compile("(?<![A-Za-z_0-9])([A-Za-z_][A-Za-z_0-9]*)(?![A-Za-z_0-9])");

    private final List<Path> includeDirectories;
    private boolean warningsEnabled;
    private List<SourceDiagnostic> warnings = List.of();

    /** Creates a compiler that resolves headers from the standard project locations. */
    public Compiler() {
        this(List.of());
    }

    /** Creates a compiler with additional include directories used for headers and runtime libraries. */
    public Compiler(List<Path> includeDirectories) {
        this.includeDirectories = List.copyOf(includeDirectories);
    }

    /** Enables or disables non-fatal C diagnostics on subsequent compilations. */
    public void setWarningsEnabled(boolean enabled) {
        warningsEnabled = enabled;
    }

    /** Returns an immutable snapshot of warnings from the most recent compilation. */
    public List<SourceDiagnostic> warnings() {
        return warnings;
    }

    /** Compiles source without attaching an originating file path, using the default optimization level. */
    public String compile(String source) {
        return compile(source, null);
    }

    /** Compiles source and maps diagnostics back to its originating file when a path is supplied. */
    public String compile(String source, Path sourcePath) {
        return compile(source, sourcePath, 0);
    }

    /**
     * Compiles one translation unit. Optimization level zero preserves generated instructions; level one
     * enables code-generation optimizations and the assembly optimizer.
     */
    public String compile(String source, Path sourcePath, int optimizationLevel) {
        return compile(source, sourcePath, optimizationLevel, () -> false);
    }

    /** Compiles one translation unit and stops when the supplied cancellation state becomes true. */
    public String compile(String source, Path sourcePath, int optimizationLevel, BooleanSupplier cancelled) {
        if (optimizationLevel < 0 || optimizationLevel > 1) {
            throw new IllegalArgumentException("Supported optimization levels are -O0 and -O1.");
        }
        warnings = List.of();
        BooleanSupplier cancellation = cancelled == null ? () -> false : cancelled;
        checkCancelled(cancellation);

        Preprocessor preprocessor = new Preprocessor(includeDirectories);
        String preprocessed = preprocess(preprocessor, source, sourcePath, cancellation);
        checkCancelled(cancellation);
        List<Token> tokens = tokenize(preprocessor, preprocessed, sourcePath, cancellation);
        checkCancelled(cancellation);
        List<Token> mappedTokens = mapTokens(tokens, preprocessor.sourceLines(), sourcePath, cancellation);
        Parser parser = new Parser(mappedTokens, cancellation);
        Parser.Unit unit = parse(parser);
        checkCancelled(cancellation);

        String namespace = namespaceFor(sourcePath);
        if (warningsEnabled) {
            warnings = CompilerWarnings.analyze(unit, parser.positions());
        }
        checkCancelled(cancellation);
        String assembly = generateAssembly(parser, unit, namespace, optimizationLevel, cancellation);
        checkCancelled(cancellation);
        return assembly;
    }

    private static String preprocess(Preprocessor preprocessor, String source, Path sourcePath,
                                     BooleanSupplier cancelled) {
        try {
            return preprocessor.process(source, sourcePath, cancelled);
        } catch (SourceDiagnostic diagnostic) {
            throw diagnostic;
        } catch (IllegalArgumentException error) {
            String firstLine = source == null ? "" : source.lines().findFirst().orElse("");
            throw new SourceDiagnostic(sourcePath, 1, 1, 1, firstLine,
                    error.getMessage() + "\nCheck the include path, directive, and macro arguments on this line.");
        }
    }

    private static void checkCancelled(BooleanSupplier cancelled) {
        if (cancelled.getAsBoolean()) {
            throw new CancellationException("Compilation was cancelled.");
        }
    }

    private static List<Token> tokenize(Preprocessor preprocessor, String source, Path sourcePath,
                                       BooleanSupplier cancelled) {
        try {
            return new Lexer(source).tokenize(cancelled);
        } catch (IllegalArgumentException error) {
            int line = 1;
            int column = 1;
            int length = 1;
            if (error instanceof Lexer.LexicalError lexical) {
                line = lexical.line();
                column = lexical.column();
                length = lexical.length();
            } else {
                Matcher location = LOCATION.matcher(error.getMessage());
                if (location.find()) {
                    line = Integer.parseInt(location.group(1));
                    column = Integer.parseInt(location.group(2));
                }
            }
            List<Preprocessor.SourceLine> sourceLines = preprocessor.sourceLines();
            Preprocessor.SourceLine origin = sourceLines.isEmpty()
                    ? new Preprocessor.SourceLine(sourcePath, line, "")
                    : sourceLines.get(Math.min(line - 1, sourceLines.size() - 1));
            Preprocessor.MappedLocation mapped = preprocessor.mapLocation(line, column, length);
            if (mapped != null) {
                origin = mapped.source();
                column = mapped.column();
                length = mapped.length();
            }
            throw new SourceDiagnostic(origin.path(), origin.line(), column, length, origin.text(), error.getMessage());
        }
    }

    private static List<Token> mapTokens(List<Token> tokens, List<Preprocessor.SourceLine> sourceLines,
                                         Path sourcePath, BooleanSupplier cancelled) {
        List<Token> mapped = new ArrayList<>(tokens.size());
        for (int index = 0; index < tokens.size(); index++) {
            if ((index & 255) == 0) checkCancelled(cancelled);
            Token token = tokens.get(index);
            Preprocessor.SourceLine origin = sourceLines.isEmpty()
                    ? new Preprocessor.SourceLine(sourcePath, token.line, "")
                    : sourceLines.get(Math.min(token.line - 1, sourceLines.size() - 1));
            Path originPath = origin.path() == null ? sourcePath : origin.path();
            mapped.add(new Token(token.type, token.data, origin.line(), token.column, originPath, origin.text()));
        }
        return mapped;
    }

    private static Parser.Unit parse(Parser parser) {
        try {
            return parser.parse();
        } catch (SourceDiagnostic diagnostic) {
            throw diagnostic;
        } catch (IllegalArgumentException error) {
            throw new SourceDiagnostic(parser.currentToken(), error.getMessage());
        }
    }

    private static String namespaceFor(Path sourcePath) {
        if (sourcePath == null) {
            return "UNIT";
        }
        int hash = sourcePath.toAbsolutePath().normalize().toString().hashCode();
        return "U" + Integer.toUnsignedString(hash, 16).toUpperCase(Locale.ROOT);
    }

    private static String generateAssembly(Parser parser, Parser.Unit unit, String namespace, int optimizationLevel,
                                           BooleanSupplier cancelled) {
        try {
            String assembly = new CodeGenerator(namespace, parser.positions(), optimizationLevel == 1, cancelled)
                    .generate(unit);
            checkCancelled(cancelled);
            return optimizationLevel == 0 ? assembly : AssemblyOptimizer.optimize(assembly, cancelled);
        } catch (SourceDiagnostic diagnostic) {
            throw diagnostic;
        } catch (IllegalArgumentException error) {
            throw new SourceDiagnostic(parser.currentToken(), error.getMessage());
        }
    }

    /** Appends runtime implementations for unresolved library calls found in assembly. */
    public String linkRuntime(String assembly) {
        String linked = assembly == null ? "" : assembly;
        if (defines(linked, "PRINTF") && references(linked, "PRINTF_INTEGER")
                && !defines(linked, "PRINTF_INTEGER")) {
            linked += "\npublic PRINTF_INTEGER\nextern PRINTF\nPRINTF_INTEGER:\nJMP PRINTF\n";
        }

        Map<String, String> libraries = new LinkedHashMap<>();
        libraries.put("stdio.c", "PRINTF puts");
        libraries.put("stdio-integer.c", "PRINTF_INTEGER");
        libraries.put("string.c", "MEMCPY memmove memset memcmp memchr strlen strcpy strncpy strcat strncat strcmp strncmp strchr strrchr strstr strspn strcspn strpbrk strtok");
        libraries.put("ctype.c", "isalnum isalpha isblank iscntrl isdigit isgraph islower isprint ispunct isspace isupper isxdigit tolower toupper");
        libraries.put("stdlib.c", "abs labs div ldiv atoi atol strtol strtoul strtod strtof atof rand srand malloc calloc realloc free bsearch qsort");
        libraries.put("time.c", "clock difftime");
        libraries.put("math.c", "fabs fabsf copysign copysignf fmin fmax fminf fmaxf isnan isinf isfinite signbit");

        Set<String> added = new HashSet<>();
        boolean changed;
        do {
            changed = false;
            for (Map.Entry<String, String> library : libraries.entrySet()) {
                if (added.contains(library.getKey()) || !referencesAny(linked, library.getValue())) {
                    continue;
                }
                linked += compile(loadRuntime(library.getKey()), Path.of("runtime", library.getKey()), 1);
                added.add(library.getKey());
                changed = true;
                break;
            }
        } while (changed);

        linked = appendIfUnresolved(linked, "PUTCHAR", "putchar.asm");
        linked = appendIfUnresolved(linked, "time", "timer.asm");
        for (String symbol : List.of("getchar", "abort", "exit")) {
            linked = appendIfUnresolved(linked, symbol, symbol + ".asm");
        }
        return linked;
    }

    private String appendIfUnresolved(String assembly, String symbol, String runtimeName) {
        return references(assembly, symbol) && !defines(assembly, symbol)
                ? assembly + loadRuntime(runtimeName)
                : assembly;
    }

    private static boolean referencesAny(String assembly, String symbols) {
        for (String symbol : symbols.split(" ")) {
            if (references(assembly, symbol) && !defines(assembly, symbol)) {
                return true;
            }
        }
        return false;
    }

    private static boolean defines(String assembly, String symbol) {
        Matcher labels = ASSEMBLY_LABEL.matcher(assembly);
        while (labels.find()) {
            if (labels.group(1).equals(symbol)) {
                return true;
            }
        }
        return false;
    }

    private static boolean references(String assembly, String symbol) {
        String code = ASSEMBLY_DECLARATION.matcher(assembly.replaceAll("(?m);[^\\n]*", "")).replaceAll("");
        Matcher symbols = ASSEMBLY_SYMBOL.matcher(code);
        while (symbols.find()) {
            if (symbols.group(1).equals(symbol)) {
                return true;
            }
        }
        return false;
    }

    private String loadRuntime(String name) {
        if (name.equals("stdio-integer.c")) {
            return "#define VCC_PRINTF_INTEGER 1\n#define printf PRINTF_INTEGER\n" + loadRuntime("stdio.c");
        }

        Path canonical = Path.of("src", "stdlib", "lib", name);
        if (Files.isRegularFile(canonical)) {
            return "\n" + readRuntime(canonical, "runtime library");
        }

        try (var resource = Compiler.class.getResourceAsStream("/stdlib/lib/" + name)) {
            if (resource != null) {
                return "\n" + new String(resource.readAllBytes(), StandardCharsets.UTF_8);
            }
        } catch (IOException error) {
            throw new IllegalArgumentException("Cannot read runtime " + name, error);
        }

        for (Path include : includeDirectories) {
            Path library = include.resolveSibling("lib").resolve(name);
            if (Files.isRegularFile(library)) {
                return "\n" + readRuntime(library, "runtime library");
            }
        }
        throw new IllegalArgumentException("Runtime library not found: " + name);
    }

    private static String readRuntime(Path path, String description) {
        try {
            return SourceAccess.readString(path);
        } catch (IOException error) {
            throw new IllegalArgumentException("Cannot read " + description + " " + path + ": "
                    + error.getMessage(), error);
        }
    }
}
