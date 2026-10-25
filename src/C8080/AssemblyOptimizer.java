package C8080;

import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;
import java.util.regex.Pattern;

/** Removes self moves and unconditional jumps that fall through to their target label. */
public final class AssemblyOptimizer {
    private static final String INLINE_ASM_BEGIN_PREFIX = "; VCC_INLINE_ASM_BEGIN ";
    private static final String INLINE_ASM_END_PREFIX = "; VCC_INLINE_ASM_END ";
    private static final Pattern SELF_MOVE = Pattern.compile("MOV ([ABCDEHL]), ?\\1");

    private AssemblyOptimizer() {}

    /** Returns assembly with redundant self moves and fall-through jumps removed. */
    public static String optimize(String assembly) {
        return optimize(assembly, () -> false);
    }

    static String optimize(String assembly, BooleanSupplier cancelled) {
        BooleanSupplier cancellation = cancelled == null ? () -> false : cancelled;
        checkCancelled(cancellation);
        String[] lines = assembly.split("\\n", -1);
        StringBuilder optimized = new StringBuilder(assembly.length());
        boolean hasOutputLine = false;
        String inlineAssemblyId = null;
        for (int index = 0; index < lines.length; index++) {
            checkCancelled(cancellation);
            String instruction = lines[index].trim();
            String inlineBegin = inlineMarkerId(instruction, INLINE_ASM_BEGIN_PREFIX);
            String inlineEnd = inlineMarkerId(instruction, INLINE_ASM_END_PREFIX);
            if (inlineAssemblyId == null && inlineBegin == null && inlineEnd == null
                    && (SELF_MOVE.matcher(instruction).matches() || jumpsToNextLabel(lines, index, instruction)))
                continue;
            if (hasOutputLine) optimized.append('\n');
            optimized.append(lines[index]);
            hasOutputLine = true;
            if (inlineAssemblyId == null && inlineBegin != null) inlineAssemblyId = inlineBegin;
            else if (inlineAssemblyId != null && inlineAssemblyId.equals(inlineEnd)) inlineAssemblyId = null;
        }
        checkCancelled(cancellation);
        String result = optimized.toString();
        checkCancelled(cancellation);
        return result;
    }

    static String inlineBegin(String id) {
        return INLINE_ASM_BEGIN_PREFIX + id;
    }

    static String inlineEnd(String id) {
        return INLINE_ASM_END_PREFIX + id;
    }

    private static String inlineMarkerId(String line, String prefix) {
        if (!line.startsWith(prefix)) return null;
        String id = line.substring(prefix.length());
        return id.matches("[A-Za-z_][A-Za-z_0-9]*") ? id : null;
    }

    private static void checkCancelled(BooleanSupplier cancelled) {
        if (cancelled.getAsBoolean()) throw new CancellationException("Assembly optimization was cancelled.");
    }

    private static boolean jumpsToNextLabel(String[] lines, int index, String instruction) {
        return instruction.startsWith("JMP ")
                && index + 1 < lines.length
                && lines[index + 1].trim().equals(instruction.substring(4).trim() + ":");
    }
}
