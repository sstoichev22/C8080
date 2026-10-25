package C8080.Main;

import C8080.Compiler;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/** Command-line C compiler: translates one C file to Vulcan assembly. */
public final class Main {
    private Main() {}
    /** Compiles the C file named by the first argument and writes or prints its assembly; exits nonzero on errors. */
    public static void main(String[] args) {
        if (args.length < 1 || args.length > 2) {
            System.err.println("Usage: java C8080.Main.Main source.c [output.asm]");
            System.exit(2);return;
        }
        Path source=Path.of(args[0]).toAbsolutePath().normalize();
        try {
            Compiler compiler=new Compiler(List.of(source.getParent()));
            String assembly=compiler.compile(Files.readString(source),source);
            if(args.length==2)Files.writeString(Path.of(args[1]),assembly);
            else System.out.print(assembly);
        } catch(Exception error) {
            System.err.println(error.getMessage());System.exit(1);
        }
    }
}
