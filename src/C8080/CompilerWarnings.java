package C8080;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static C8080.Parser.*;

/** Finds source-level issues that can be diagnosed without rejecting compilation. */
final class CompilerWarnings {
    private final Map<Object, Token> positions;
    private final List<SourceDiagnostic> warnings = new ArrayList<>();

    private CompilerWarnings(Map<Object, Token> positions) {
        this.positions = positions;
    }

    static List<SourceDiagnostic> analyze(Unit unit, Map<Object, Token> positions) {
        CompilerWarnings analyzer = new CompilerWarnings(positions);
        analyzer.visit(unit, null);
        return List.copyOf(analyzer.warnings);
    }

    private void warn(Object node, Token fallback, String message) {
        Token location = positions.getOrDefault(node, fallback);
        if (location != null) {
            warnings.add(new SourceDiagnostic(location.sourcePath, location.line, location.column,
                    Math.max(1, location.data.length()), location.sourceLine, message,
                    SourceDiagnostic.Severity.WARNING));
        }
    }

    private void visit(Object node, Token fallback) {
        if (node == null) {
            return;
        }
        Token location = positions.getOrDefault(node, fallback);
        if (node instanceof DeclStmt declaration) {
            warnOnIntegerOverflow(declaration, location);
        } else if (node instanceof BinaryExpr binary) {
            warnOnInvalidConstantOperand(binary, location);
        } else if (node instanceof BlockStmt block) {
            visitBlock(block, location);
            return;
        }

        if (node instanceof Iterable<?> children) {
            for (Object child : children) {
                visit(child, location);
            }
            return;
        }
        if (isParserRecord(node)) {
            visitRecordComponents(node, location);
        }
    }

    private void warnOnIntegerOverflow(DeclStmt declaration, Token location) {
        if (declaration.initializer() == null
                || declaration.type().kind != CType.Kind.INTEGER
                || declaration.type().isBoolean()) {
            return;
        }
        try {
            BigInteger value = Parser.constant(declaration.initializer());
            int bits = declaration.type().size * 8;
            BigInteger minimum = declaration.type().unsigned
                    ? BigInteger.ZERO
                    : BigInteger.ONE.shiftLeft(bits - 1).negate();
            BigInteger maximum = BigInteger.ONE.shiftLeft(bits - (declaration.type().unsigned ? 0 : 1))
                    .subtract(BigInteger.ONE);
            if (value.compareTo(minimum) < 0 || value.compareTo(maximum) > 0) {
                warn(declaration, location, "Constant " + value + " overflows " + declaration.type()
                        + "; conversion wraps to the target width.");
            }
        } catch (IllegalArgumentException | ArithmeticException notConstant) {
        }
    }

    private void warnOnInvalidConstantOperand(BinaryExpr expression, Token location) {
        try {
            BigInteger right = Parser.constant(expression.right());
            if ((expression.op() == Token.TokenType.F_SLASH || expression.op() == Token.TokenType.PERCENT)
                    && right.signum() == 0) {
                warn(expression, location, "Division or remainder by zero has no portable C result.");
            }
            if ((expression.op() == Token.TokenType.SHIFT_LEFT || expression.op() == Token.TokenType.SHIFT_RIGHT)
                    && right.signum() < 0) {
                warn(expression, location, "Negative shift count is invalid in C.");
            }
        } catch (IllegalArgumentException | ArithmeticException notConstant) {
        }
    }

    private void visitBlock(BlockStmt block, Token location) {
        boolean unreachable = false;
        for (Stmt statement : block.statements()) {
            if (unreachable) {
                warn(statement, location, "This statement is unreachable after return, break or continue.");
            }
            visit(statement, location);
            unreachable |= alwaysTerminates(statement);
        }
    }

    private static boolean alwaysTerminates(Stmt statement) {
        if (statement instanceof ReturnStmt || statement instanceof BreakStmt
                || statement instanceof ContinueStmt) {
            return true;
        }
        if (statement instanceof BlockStmt block) {
            return block.statements().stream().anyMatch(CompilerWarnings::alwaysTerminates);
        }
        if (statement instanceof IfStmt conditional) {
            return conditional.no() != null
                    && alwaysTerminates(conditional.yes())
                    && alwaysTerminates(conditional.no());
        }
        return false;
    }

    private static boolean isParserRecord(Object node) {
        Class<?> type = node.getClass();
        return type.isRecord() && type.getEnclosingClass() == Parser.class;
    }

    private void visitRecordComponents(Object node, Token fallback) {
        try {
            for (var component : node.getClass().getRecordComponents()) {
                visit(component.getAccessor().invoke(node), fallback);
            }
        } catch (ReflectiveOperationException failure) {
            throw new IllegalStateException("Unable to inspect parser node " + node.getClass().getSimpleName(), failure);
        }
    }
}
