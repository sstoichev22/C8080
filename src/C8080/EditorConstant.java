package C8080;

import java.util.Locale;

/** Computes constant values and IEEE 754 details for editor tooltips. */
public final class EditorConstant {
    private EditorConstant() {}

    /** Returns the converted value of one initialized global declaration, or null when unavailable. */
    public static String value(String declaration) {
        try {
            Parser.Unit unit = new Parser(new Lexer(declaration).tokenize()).parse();
            if (unit.globals().size() != 1 || unit.globals().get(0).initializer() == null) {
                return null;
            }
            Parser.DeclStmt global = unit.globals().get(0);
            ConstantEvaluator.Value value = ConstantEvaluator.evaluate(global.initializer()).convert(global.type());
            if (value.type().kind == CType.Kind.FLOAT) {
                return value.type().size == 4
                        ? Float.toString((float) value.floating())
                        : Double.toString(value.floating());
            }
            return value.integer().toString();
        } catch (IllegalArgumentException unavailable) {
            return null;
        }
    }

    /** Returns decimal, binary, and hexadecimal details for a floating literal, or null if it is invalid. */
    public static String floatingLiteral(String literal) {
        try {
            Parser.DeclStmt declaration = new Parser(new Lexer("double __hover = " + literal + ";").tokenize())
                    .parse().globals().get(0);
            ConstantEvaluator.Value value = ConstantEvaluator.evaluate(declaration.initializer());
            if (value.type().kind != CType.Kind.FLOAT) {
                return null;
            }

            boolean singlePrecision = value.type().size == 4;
            int width = singlePrecision ? 32 : 64;
            long bits = singlePrecision
                    ? Integer.toUnsignedLong(Float.floatToRawIntBits((float) value.floating()))
                    : Double.doubleToRawLongBits(value.floating());
            String binary = Long.toBinaryString(bits);
            binary = "0".repeat(width - binary.length()) + binary;
            String decimal = singlePrecision
                    ? Float.toString((float) value.floating())
                    : Double.toString(value.floating());
            String hexadecimal = String.format(Locale.ROOT, singlePrecision ? "%08X" : "%016X", bits);
            return "Decimal: " + decimal
                    + "\nIEEE 754 " + (singlePrecision ? "float32" : "double64") + " bits:"
                    + "\nBinary: 0b" + binary
                    + "\nHex: 0x" + hexadecimal;
        } catch (IllegalArgumentException unavailable) {
            return null;
        }
    }
}
