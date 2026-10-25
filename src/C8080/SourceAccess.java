package C8080;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

/** Optional per-thread project boundary for builds requested by external tools. Ordinary IDE builds are unrestricted. */
public final class SourceAccess {
    private static final ThreadLocal<Path> ROOT = new ThreadLocal<>();

    private SourceAccess() {}

    /** Restricts subsequent source reads on this thread to an existing canonical project directory. */
    public static void restrictTo(Path root) throws IOException {
        ROOT.set(root.toRealPath());
    }

    /** Reports whether a discovery candidate remains inside the configured project, including existing links. */
    public static boolean allows(Path path) {
        Path root = ROOT.get();
        if (root == null) return true;
        Path absolute = path.toAbsolutePath().normalize();
        try {
            Path existing = absolute;
            while (existing != null && !Files.exists(existing)) existing = existing.getParent();
            return absolute.startsWith(root) && existing != null && existing.toRealPath().startsWith(root);
        } catch (IOException error) {
            return false;
        }
    }

    /** Rejects paths that escape an active external-tool project boundary. */
    public static void check(Path path) {
        if (!allows(path)) throw new IllegalArgumentException("Path is outside the MCP project: " + path);
    }

    /** Reads UTF-8 source, limiting external-tool source files to eight MiB. */
    public static String readString(Path path) throws IOException {
        check(path);
        if (ROOT.get() != null && Files.size(path) > 8 * 1024 * 1024)
            throw new IllegalArgumentException("MCP source exceeds eight MiB: " + path);
        return Files.readString(path);
    }
}
