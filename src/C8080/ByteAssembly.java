package C8080;

import java.util.Locale;

/** Lowers byte operations whose emulated accumulator may temporarily hold a ninth carry bit. */
final class ByteAssembly {
    private ByteAssembly() {}

    static String lower(String instruction, String label) {
        String opcode = instruction.trim().toUpperCase(Locale.ROOT);
        String emittedInstruction = "    " + instruction + "\n";
        if (opcode.equals("CMA")) {
            return emittedInstruction + preserveCarryAndMask(label, 255);
        }
        if (isArithmetic(opcode, "ADD", "ADC", "ADI", "ACI")) {
            return emittedInstruction + normalizeAddition(label);
        }
        if (isArithmetic(opcode, "SUB", "SBB", "SUI", "SBI")) {
            return emittedInstruction + preserveCarryAndMask(label, 255);
        }
        String byteRotate = switch (opcode) {
            case "RLC 1", "RRC 1", "RAL 1", "RAR 1" -> opcode.substring(0, 3);
            default -> opcode;
        };
        return switch (byteRotate) {
            case "RAL" -> "    ADC A\n" + normalizeAddition(label);
            case "RLC" -> "    ADD A\n" + normalizeAddition(label)
                    + "    JNC " + label + "_rotate\n    ORI 1\n    STC\n"
                    + label + "_rotate:\n";
            case "RAR" -> "    JNC " + label + "_input\n    ORI 256\n"
                    + label + "_input:\n    RRC 1\n" + preserveCarryAndMask(label, 255);
            case "RRC" -> "    RRC 1\n" + preserveCarryAndMask(label, 127)
                    + "    JNC " + label + "_rotate\n    ORI 128\n    STC\n"
                    + label + "_rotate:\n";
            default -> emittedInstruction;
        };
    }

    private static boolean isArithmetic(String opcode, String first, String second, String third, String fourth) {
        return opcode.startsWith(first + " ") || opcode.startsWith(second + " ")
                || opcode.startsWith(third + " ") || opcode.startsWith(fourth + " ");
    }

    private static String normalizeAddition(String label) {
        return "    CPI 256\n"
                + "    JC " + label + "_low\n"
                + "    ANI 255\n"
                + "    STC\n"
                + "    JMP " + label + "_end\n"
                + label + "_low:\n"
                + "    ANI 255\n"
                + label + "_end:\n";
    }

    private static String preserveCarryAndMask(String label, int mask) {
        return "    JNC " + label + "_low\n"
                + "    ANI " + mask + "\n"
                + "    STC\n"
                + "    JMP " + label + "_end\n"
                + label + "_low:\n"
                + "    ANI " + mask + "\n"
                + label + "_end:\n";
    }
}
