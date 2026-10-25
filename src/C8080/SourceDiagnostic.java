package C8080;

import java.nio.file.Path;
import java.util.Locale;

/** A compiler diagnostic carrying source coordinates and a formatted source excerpt. */
public final class SourceDiagnostic extends IllegalArgumentException {
    private static final long serialVersionUID = 1L;

    /** Diagnostic severity. */
    public enum Severity {
        ERROR,
        WARNING
    }

    private final Path file;
    private final int line;
    private final int column;
    private final int length;
    private final String explanation;
    private final Severity severity;

    /** Creates an error diagnostic, highlighting at least one character. */
    public SourceDiagnostic(Path file, int line, int column, int length, String sourceLine, String explanation) {
        this(file, line, column, length, sourceLine, explanation, Severity.ERROR);
    }

    /** Creates a diagnostic with the specified severity and source excerpt. */
    public SourceDiagnostic(Path file, int line, int column, int length, String sourceLine,
                            String explanation, Severity severity) {
        super(format(file, line, column, length, sourceLine, explanation, severity));
        this.file = file;
        this.line = Math.max(1, line);
        this.column = Math.max(1, column);
        this.length = Math.max(1, length);
        this.explanation = explanation;
        this.severity = severity;
    }

    /** Creates an error diagnostic at the token's source range. */
    public SourceDiagnostic(Token token, String explanation) {
        this(token.sourcePath, token.line, token.column, Math.max(1, token.data.length()),
                token.sourceLine, explanation);
    }

    /** Source file of the diagnostic, or null for unnamed source. */
    public Path file() {
        return file;
    }

    /** 1-based source line. */
    public int line() {
        return line;
    }

    /** 1-based source column. */
    public int column() {
        return column;
    }

    /** Number of characters to underline. */
    public int length() {
        return length;
    }

    /** Human-readable explanation without the location prefix. */
    public String explanation() {
        return explanation;
    }

    /** Severity of the diagnostic. */
    public Severity severity() {
        return severity;
    }

    private static String format(Path file, int line, int column, int length, String sourceLine,
                                 String explanation, Severity severity) {
        String path = file == null
                ? Path.of("source.c").toAbsolutePath().normalize().toString()
                : file.toAbsolutePath().normalize().toString();
        String code = sourceLine == null ? "" : sourceLine;
        int normalizedColumn = Math.max(1, column);
        int start = Math.min(normalizedColumn - 1, code.length());
        StringBuilder padding = new StringBuilder(start);
        for (int index = 0; index < start; index++) {
            padding.append(code.charAt(index) == '\t' ? '\t' : ' ');
        }
        int remaining = Math.max(1, code.length() - start);
        int highlightWidth = Math.max(1, Math.min(length, remaining));
        String label = severity.name().toLowerCase(Locale.ROOT);
        return path + ":" + Math.max(1, line) + ":" + normalizedColumn + ": " + label + "\n"
                + "  " + code + "\n  " + padding + "^".repeat(highlightWidth) + "\n" + explanation;
    }
}
