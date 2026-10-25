package C8080;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;
import java.util.function.Function;

import static C8080.Parser.*;
import static C8080.Token.TokenType.*;

/** Evaluates side-effect-free C expressions used in constant contexts. */
final class ConstantEvaluator {
    private ConstantEvaluator() {}

    /** Result of a constant expression: an integer or floating value of the given type. */
    record Value(CType type, BigInteger integer, double floating, boolean negativeNaN) {
        Value(CType type, BigInteger integer, double floating) {
            this(type, integer, floating, false);
        }

        /** Returns the value as a double, converting an integer result when necessary. */
        @Override
        public double floating() {
            return negativeNaN ? Math.copySign(Double.NaN, -1.0) : floating;
        }

        boolean truth() {
            return type.kind == CType.Kind.FLOAT ? floating != 0.0 : integer.signum() != 0;
        }

        Value convert(CType destination) {
            if (destination.isBoolean()) {
                return ConstantEvaluator.integer(truth() ? BigInteger.ONE : BigInteger.ZERO, destination);
            }
            if (destination.kind == CType.Kind.FLOAT) {
                double converted = type.kind == CType.Kind.FLOAT ? floating() : integer.doubleValue();
                return ConstantEvaluator.floating(converted, destination);
            }
            if (destination.kind != CType.Kind.INTEGER && destination.kind != CType.Kind.POINTER) {
                throw new IllegalArgumentException("Constant conversion requires a scalar type.");
            }

            BigInteger converted = integer;
            if (type.kind == CType.Kind.FLOAT) {
                if (!Double.isFinite(floating)) {
                    throw new IllegalArgumentException("Cannot cast an infinite or NaN constant to an integer.");
                }
                converted = new BigDecimal(floating).toBigInteger();
            }
            return ConstantEvaluator.integer(converted, destination);
        }
    }

    static Value evaluate(Expr expression) {
        return evaluate(expression, ConstantEvaluator::typeOf);
    }

    static Value evaluate(Expr expression, Function<Expr, CType> types) {
        return evaluate(expression, types, () -> false);
    }

    static Value evaluate(Expr expression, BooleanSupplier cancellation) {
        BooleanSupplier callback = cancellation == null ? () -> false : cancellation;
        return evaluate(expression, value -> typeOf(value, callback), callback);
    }

    private static Value evaluate(Expr expression, Function<Expr, CType> types, BooleanSupplier cancellation) {
        checkCancelled(cancellation);
        if (expression instanceof NumberExpr number) {
            return integer(number.value(), number.type());
        }
        if (expression instanceof FloatExpr number) {
            return floating(number.value(), number.type());
        }
        if (expression instanceof CastExpr cast) {
            return evaluate(cast.value(), types, cancellation).convert(cast.type());
        }
        if (expression instanceof SizeofExpr size) {
            CType measuredType = size.type() != null ? size.type() : types.apply(size.value());
            checkCancelled(cancellation);
            if (measuredType.size <= 0) {
                throw new IllegalArgumentException("sizeof requires a complete object type.");
            }
            return integer(BigInteger.valueOf(measuredType.size), CType.UINT);
        }
        if (expression instanceof ConditionalExpr conditional) {
            Expr selected = evaluate(conditional.condition(), types, cancellation).truth()
                    ? conditional.yes()
                    : conditional.no();
            CType resultType = CType.conditionalCommon(types.apply(conditional.yes()), types.apply(conditional.no()));
            checkCancelled(cancellation);
            return evaluate(selected, types, cancellation).convert(resultType);
        }
        if (expression instanceof UnaryExpr unary) {
            return evaluateUnary(unary, types, cancellation);
        }
        if (expression instanceof BinaryExpr binary) {
            return evaluateBinary(binary, types, cancellation);
        }
        throw new IllegalArgumentException("Static initializer must be constant.");
    }

    private static Value evaluateUnary(UnaryExpr unary, Function<Expr, CType> types, BooleanSupplier cancellation) {
        Value value = evaluate(unary.value(), types, cancellation);
        if (unary.op() == BANG) {
            return bool(!value.truth());
        }
        value = value.convert(CType.common(value.type(), CType.INT));
        if (value.type().kind == CType.Kind.FLOAT) {
            return switch (unary.op()) {
                case PLUS -> value;
                case MINUS -> Double.isNaN(value.floating())
                        ? new Value(value.type(), null, Double.NaN, !value.negativeNaN())
                        : floating(-value.floating(), value.type());
                default -> throw new IllegalArgumentException("Invalid floating constant operator.");
            };
        }
        return switch (unary.op()) {
            case PLUS -> value;
            case MINUS -> integer(value.integer().negate(), value.type());
            case TILDE -> integer(value.integer().not(), value.type());
            default -> throw new IllegalArgumentException("Not a constant unary expression.");
        };
    }

    private static Value evaluateBinary(BinaryExpr binary, Function<Expr, CType> types, BooleanSupplier cancellation) {
        Value left = evaluate(binary.left(), types, cancellation);
        if (binary.op() == AND_AND && !left.truth()) {
            return bool(false);
        }
        if (binary.op() == OR_OR && left.truth()) {
            return bool(true);
        }

        checkCancelled(cancellation);
        Value right = evaluate(binary.right(), types, cancellation);
        if (binary.op() == AND_AND || binary.op() == OR_OR) {
            return bool(right.truth());
        }
        if (binary.op() == SHIFT_LEFT || binary.op() == SHIFT_RIGHT) {
            return evaluateShift(binary.op(), left, right);
        }

        CType commonType = CType.common(left.type(), right.type());
        left = left.convert(commonType);
        right = right.convert(commonType);
        if (commonType.kind == CType.Kind.FLOAT) {
            return floatingBinary(left, binary.op(), right);
        }

        BigInteger leftInteger = left.integer();
        BigInteger rightInteger = right.integer();
        int comparison = leftInteger.compareTo(rightInteger);
        return switch (binary.op()) {
            case PLUS -> integer(leftInteger.add(rightInteger), commonType);
            case MINUS -> integer(leftInteger.subtract(rightInteger), commonType);
            case STAR -> integer(leftInteger.multiply(rightInteger), commonType);
            case F_SLASH -> {
                requireNonzeroDivisor(rightInteger);
                yield integer(leftInteger.divide(rightInteger), commonType);
            }
            case PERCENT -> {
                requireNonzeroDivisor(rightInteger);
                yield integer(leftInteger.remainder(rightInteger), commonType);
            }
            case AMP -> integer(leftInteger.and(rightInteger), commonType);
            case PIPE -> integer(leftInteger.or(rightInteger), commonType);
            case CARET -> integer(leftInteger.xor(rightInteger), commonType);
            case EQUAL_EQUAL -> bool(comparison == 0);
            case NOT_EQUAL -> bool(comparison != 0);
            case LESS -> bool(comparison < 0);
            case LESS_EQUAL -> bool(comparison <= 0);
            case GREATER -> bool(comparison > 0);
            case GREATER_EQUAL -> bool(comparison >= 0);
            default -> throw new IllegalArgumentException("Not a constant binary expression.");
        };
    }

    private static Value evaluateShift(Token.TokenType operator, Value left, Value right) {
        requireInteger(left);
        requireInteger(right);
        CType promotedType = CType.common(left.type(), CType.INT);
        left = left.convert(promotedType);
        int width = left.type().size * 8;
        BigInteger shift = right.integer();
        if (shift.signum() < 0 || shift.compareTo(BigInteger.valueOf(width)) >= 0) {
            throw new IllegalArgumentException(
                    "Constant shift count must be nonnegative and smaller than the promoted operand width.");
        }
        int count = shift.intValue();
        BigInteger shifted = operator == SHIFT_LEFT
                ? left.integer().shiftLeft(count)
                : left.integer().shiftRight(count);
        return integer(shifted, left.type());
    }

    private static void requireNonzeroDivisor(BigInteger divisor) {
        if (divisor.signum() == 0) {
            throw new IllegalArgumentException("Constant division or remainder by zero is undefined.");
        }
    }

    private static Value floatingBinary(Value left, Token.TokenType operator, Value right) {
        double leftValue = left.floating();
        double rightValue = right.floating();
        return switch (operator) {
            case PLUS -> floatingArithmetic(leftValue + rightValue, left.type());
            case MINUS -> floatingArithmetic(leftValue - rightValue, left.type());
            case STAR -> floatingArithmetic(leftValue * rightValue, left.type());
            case F_SLASH -> floatingArithmetic(leftValue / rightValue, left.type());
            case EQUAL_EQUAL -> bool(leftValue == rightValue);
            case NOT_EQUAL -> bool(leftValue != rightValue);
            case LESS -> bool(leftValue < rightValue);
            case LESS_EQUAL -> bool(leftValue <= rightValue);
            case GREATER -> bool(leftValue > rightValue);
            case GREATER_EQUAL -> bool(leftValue >= rightValue);
            default -> throw new IllegalArgumentException("Invalid floating constant operator.");
        };
    }

    private static Value floatingArithmetic(double value, CType type) {
        return floating(Double.isNaN(value) ? Double.NaN : value, type);
    }

    private static Value integer(BigInteger value, CType type) {
        int width = type.size * 8;
        BigInteger modulus = BigInteger.ONE.shiftLeft(width);
        BigInteger normalized = value.mod(modulus);
        if (!type.unsigned && normalized.testBit(width - 1)) {
            normalized = normalized.subtract(modulus);
        }
        return new Value(type, normalized, 0.0);
    }

    private static Value floating(double value, CType type) {
        if (Double.isNaN(value)) {
            boolean negative = (Double.doubleToRawLongBits(value) & Long.MIN_VALUE) != 0;
            return new Value(type, null, Double.NaN, negative);
        }
        double rounded = type.size == 4 ? (double) (float) value : value;
        return new Value(type, null, rounded);
    }

    private static Value bool(boolean value) {
        return integer(value ? BigInteger.ONE : BigInteger.ZERO, CType.INT);
    }

    private static void requireInteger(Value value) {
        if (value.type().kind != CType.Kind.INTEGER) {
            throw new IllegalArgumentException("Constant shift operands must be integers.");
        }
    }

    private static CType typeOf(Expr expression) {
        return typeOf(expression, () -> false);
    }

    private static CType typeOf(Expr expression, BooleanSupplier cancellation) {
        checkCancelled(cancellation);
        if (expression instanceof NumberExpr number) return number.type();
        if (expression instanceof FloatExpr number) return number.type();
        if (expression instanceof CastExpr cast) return cast.type();
        if (expression instanceof SizeofExpr) return CType.UINT;
        if (expression instanceof StringExpr string) return CType.array(CType.CHAR, string.value().length() + 1);
        if (expression instanceof UnaryExpr unary) {
            return unary.op() == BANG ? CType.INT : CType.common(typeOf(unary.value(), cancellation), CType.INT);
        }
        if (expression instanceof ConditionalExpr conditional) {
            return CType.conditionalCommon(typeOf(conditional.yes(), cancellation), typeOf(conditional.no(), cancellation));
        }
        if (expression instanceof BinaryExpr binary) {
            return switch (binary.op()) {
                case EQUAL_EQUAL, NOT_EQUAL, LESS, LESS_EQUAL, GREATER, GREATER_EQUAL, AND_AND, OR_OR -> CType.INT;
                case SHIFT_LEFT, SHIFT_RIGHT -> CType.common(typeOf(binary.left(), cancellation), CType.INT);
                default -> CType.common(typeOf(binary.left(), cancellation), typeOf(binary.right(), cancellation));
            };
        }
        throw new IllegalArgumentException("Expected a constant expression.");
    }

    private static void checkCancelled(BooleanSupplier cancellation) {
        if (cancellation.getAsBoolean()) throw new CancellationException("Constant evaluation was cancelled.");
    }
}
