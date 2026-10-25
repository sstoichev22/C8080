package C8080;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/** Describes target C types, their layout, and the conversions used by the compiler. */
public final class CType {
    public static final int MAX_INTEGER_BITS = 2048;

    /** Structural category of a C type. */
    public enum Kind { VOID, INTEGER, FLOAT, POINTER, ARRAY, STRUCT, UNION, FUNCTION }

    /** A member declaration paired with its computed byte offset. */
    public record Field(String name, CType type, int offset) {}

    public static final CType VOID = new CType(Kind.VOID, "void", 0, false, null, 0);
    public static final CType CHAR = integer("char", 1, true);
    public static final CType INT = integer("int", 4, false);
    public static final CType UINT = integer("unsigned int", 4, true);
    public static final CType LONG = integer("long", 8, false);
    public static final CType FLOAT = new CType(Kind.FLOAT, "float", 4, false, null, 0);
    public static final CType DOUBLE = new CType(Kind.FLOAT, "double", 8, false, null, 0);

    public final Kind kind;
    public final String name;
    public int size;
    public final boolean unsigned;
    public final CType element;
    public final int count;
    public List<Field> fields = List.of();
    public List<CType> parameters = List.of();
    public boolean variadic;
    public boolean volatileQualified;

    private CType unqualified;
    private CType volatileView;
    private final List<CType> qualifiedViews = new ArrayList<>();
    private int aggregateAlignment = 1;
    private boolean aggregateDefined;

    private CType(Kind kind, String name, int size, boolean unsigned, CType element, int count) {
        this.kind = kind;
        this.name = name;
        this.size = size;
        this.unsigned = unsigned;
        this.element = element;
        this.count = count;
    }

    /** Creates an integer type with a byte width from one through 65,536. */
    public static CType integer(String name, int bytes, boolean unsigned) {
        if (bytes < 1 || bytes > 65_536) {
            throw new IllegalArgumentException("Integer width must be between 1 and 65536 bytes.");
        }
        return new CType(Kind.INTEGER, name, bytes, unsigned, null, 0);
    }

    /** Creates an eight-byte target pointer to {@code element}. */
    public static CType pointer(CType element) {
        return new CType(Kind.POINTER, element.name + "*", 8, true, element, 0);
    }

    /** Returns a volatile-qualified view, reusing it on repeated requests. */
    public CType asVolatile() {
        if (volatileQualified) {
            return this;
        }
        if (volatileView != null) {
            return volatileView;
        }
        CType qualifiedElement = kind == Kind.ARRAY ? element.asVolatile() : element;
        CType result = new CType(kind, name, size, unsigned, qualifiedElement, count);
        result.fields = fields;
        result.parameters = parameters;
        result.variadic = variadic;
        result.aggregateAlignment = aggregateAlignment;
        result.volatileQualified = true;
        result.unqualified = this;
        volatileView = result;
        qualifiedViews.add(result);
        return result;
    }

    /** Creates a function type with an immutable parameter list. */
    public static CType function(CType result, List<CType> parameters, boolean variadic) {
        CType type = new CType(Kind.FUNCTION, result.name + "()", 0, false, result, 0);
        type.parameters = List.copyOf(parameters);
        type.variadic = variadic;
        return type;
    }

    /** Creates an array after checking its count and maximum 32 MiB object size. */
    public static CType array(CType element, int count) {
        long bytes = (long) element.size * count;
        if (element.kind == Kind.VOID || element.kind == Kind.FUNCTION
                || count < 0 || bytes > 32 * 1024 * 1024) {
            throw new IllegalArgumentException("Array size is out of range.");
        }
        return new CType(Kind.ARRAY, element.name + "[" + count + "]",
                element.size * count, true, element, count);
    }

    /** Creates an incomplete struct or union that can be defined once. */
    public static CType aggregate(String name, boolean union) {
        return new CType(union ? Kind.UNION : Kind.STRUCT, name, 0, false, null, 0);
    }

    /** Defines aggregate members, computing aligned offsets and total size. */
    public void define(List<Field> declarations) {
        if (unqualified != null) {
            unqualified.define(declarations);
            return;
        }
        if (!aggregate()) {
            throw new IllegalArgumentException("Cannot define non-aggregate type " + name);
        }
        if (aggregateDefined) {
            throw new IllegalArgumentException("Duplicate definition of " + name);
        }

        List<Field> laidOutFields = new ArrayList<>();
        Set<String> names = new HashSet<>();
        int offset = 0;
        int alignment = 1;
        for (Field field : declarations) {
            if (field.type.size == 0) {
                throw new IllegalArgumentException("Incomplete field type " + field.type.name);
            }
            if (!names.add(field.name)) {
                throw new IllegalArgumentException("Duplicate field " + field.name);
            }
            int fieldAlignment = field.type.alignment();
            alignment = Math.max(alignment, fieldAlignment);
            int fieldOffset = kind == Kind.UNION ? 0 : align(offset, fieldAlignment);
            laidOutFields.add(new Field(field.name, field.type, fieldOffset));
            offset = kind == Kind.UNION ? Math.max(offset, field.type.size) : fieldOffset + field.type.size;
        }

        aggregateAlignment = alignment;
        size = align(offset, alignment);
        fields = List.copyOf(laidOutFields);
        aggregateDefined = true;
        for (CType view : qualifiedViews) {
            view.size = size;
            view.fields = fields;
            view.aggregateAlignment = alignment;
        }
    }

    /** Returns the target alignment in bytes. */
    public int alignment() {
        if (aggregate()) {
            return aggregateAlignment;
        }
        if (kind == Kind.ARRAY) {
            return element.alignment();
        }
        return Math.min(8, Integer.highestOneBit(Math.max(1, size)));
    }

    /** Returns whether this type is a struct or union. */
    public boolean aggregate() {
        return kind == Kind.STRUCT || kind == Kind.UNION;
    }

    /** Returns whether this type can be used as a scalar value. */
    public boolean scalar() {
        return kind == Kind.INTEGER || kind == Kind.FLOAT || kind == Kind.POINTER;
    }

    /** Applies the array or function conversion used in expression contexts. */
    public CType decay() {
        if (kind == Kind.ARRAY) {
            return pointer(element);
        }
        if (kind == Kind.FUNCTION) {
            return pointer(this);
        }
        return this;
    }

    /** Returns a named member or reports the missing member and containing type. */
    public Field field(String name) {
        return fields.stream().filter(field -> field.name.equals(name)).findFirst()
                .orElseThrow(() -> new IllegalArgumentException("Unknown field " + name + " in " + this.name));
    }

    /** Rounds {@code size} up to the next multiple of {@code alignment}. */
    public static int align(int size, int alignment) {
        if (size < 0 || alignment < 1) {
            throw new IllegalArgumentException("Size must be nonnegative and alignment must be positive.");
        }
        long aligned = ((long) size + alignment - 1) / alignment * alignment;
        if (aligned > Integer.MAX_VALUE) {
            throw new IllegalArgumentException("Aligned size exceeds the target's integer range.");
        }
        return (int) aligned;
    }

    /** Returns whether this integer type represents the built-in bool type. */
    public boolean isBoolean() {
        return kind == Kind.INTEGER && name.equals("bool");
    }

    /** Compares non-aggregate types structurally and aggregates by identity. */
    public boolean same(CType other) {
        if (this == other) {
            return true;
        }
        if (unqualified != null) {
            return unqualified.same(unwrap(other));
        }
        if (other != null && other.unqualified != null) {
            return same(other.unqualified);
        }
        if (other == null || aggregate() || other.aggregate()) {
            return false;
        }
        if (kind != other.kind || size != other.size || unsigned != other.unsigned
                || isBoolean() != other.isBoolean()) {
            return false;
        }
        if (element == null ? other.element != null : other.element == null || !element.same(other.element)) {
            return false;
        }
        if (kind != Kind.FUNCTION) {
            return true;
        }
        if (variadic != other.variadic || parameters.size() != other.parameters.size()) {
            return false;
        }
        for (int index = 0; index < parameters.size(); index++) {
            if (!parameters.get(index).same(other.parameters.get(index))) {
                return false;
            }
        }
        return true;
    }

    /** Compares declaration types, allowing incomplete arrays and array qualifiers propagated to elements. */
    public boolean sameDeclaration(CType other) {
        return sameDeclaration(this, other, false);
    }

    /** Compares parameter types while ignoring only each parameter object's top-level qualifiers. */
    public boolean sameParameterDeclaration(CType other) {
        return sameDeclaration(this, other, true);
    }

    private static boolean sameDeclaration(CType left, CType right, boolean ignoreRootQualifier) {
        if (left == right) {
            return true;
        }
        if (left == null || right == null) {
            return false;
        }
        if (ignoreRootQualifier) {
            left = unwrap(left);
            right = unwrap(right);
        }
        if (left == right) {
            return true;
        }
        if (left.kind != right.kind || left.unsigned != right.unsigned
                || left.isBoolean() != right.isBoolean()) {
            return false;
        }
        if (left.kind == Kind.ARRAY) {
            if (left.count != 0 && right.count != 0 && left.count != right.count) {
                return false;
            }
        } else if (left.volatileQualified != right.volatileQualified || left.size != right.size
                || left.count != right.count) {
            return false;
        }
        if (left.aggregate() || right.aggregate()) {
            return unwrap(left) == unwrap(right);
        }
        if (left.element == null ? right.element != null
                : right.element == null || !sameDeclaration(left.element, right.element, false)) {
            return false;
        }
        if (left.kind != Kind.FUNCTION) {
            return true;
        }
        if (left.variadic != right.variadic || left.parameters.size() != right.parameters.size()) {
            return false;
        }
        for (int index = 0; index < left.parameters.size(); index++) {
            if (!sameDeclaration(left.parameters.get(index), right.parameters.get(index), true)) {
                return false;
            }
        }
        return true;
    }

    /** Combines compatible declarations, retaining a known bound when either array bound is incomplete. */
    CType compositeDeclaration(CType other) {
        if (!sameDeclaration(other)) {
            throw new IllegalArgumentException("Incompatible declaration types.");
        }
        return compositeDeclaration(this, other);
    }

    private static CType compositeDeclaration(CType left, CType right) {
        if (left.kind == Kind.ARRAY) {
            int count = left.count == 0 ? right.count : left.count;
            CType element = compositeDeclaration(left.element, right.element);
            CType composite = CType.array(element, count);
            return left.volatileQualified || right.volatileQualified ? composite.asVolatile() : composite;
        }
        if (left.kind == Kind.POINTER) {
            CType composite = CType.pointer(compositeDeclaration(left.element, right.element));
            return left.volatileQualified || right.volatileQualified ? composite.asVolatile() : composite;
        }
        if (left.kind == Kind.FUNCTION) {
            CType result = compositeDeclaration(left.element, right.element);
            List<CType> parameters = new ArrayList<>(left.parameters.size());
            for (int index = 0; index < left.parameters.size(); index++) {
                CType leftParameter = unwrap(left.parameters.get(index));
                CType rightParameter = unwrap(right.parameters.get(index));
                parameters.add(compositeDeclaration(leftParameter, rightParameter));
            }
            CType composite = CType.function(result, parameters, left.variadic);
            return left.volatileQualified || right.volatileQualified ? composite.asVolatile() : composite;
        }
        return left;
    }

    private static CType unwrap(CType type) {
        return type == null || type.unqualified == null ? type : type.unqualified;
    }

    /** Computes the target's common arithmetic or pointer type after decay. */
    public static CType common(CType left, CType right) {
        left = left.decay();
        right = right.decay();
        if (left.aggregate() || right.aggregate()) {
            if (left.same(right)) {
                return left;
            }
            throw new IllegalArgumentException("Incompatible aggregate types.");
        }
        if (left.kind == Kind.FLOAT || right.kind == Kind.FLOAT) {
            return (left.kind == Kind.FLOAT && left.size == 8)
                    || (right.kind == Kind.FLOAT && right.size == 8) ? DOUBLE : FLOAT;
        }
        if (left.kind == Kind.POINTER) {
            return left;
        }
        if (right.kind == Kind.POINTER) {
            return right;
        }
        int bytes = Math.max(4, Math.max(left.size, right.size));
        boolean unsigned = (left.unsigned && left.size >= bytes)
                || (right.unsigned && right.size >= bytes);
        return integer((unsigned ? "uint" : "int") + bytes * 8, bytes, unsigned);
    }

    /** Returns a conditional pointer type from compatible composite targets and immediate volatile qualification. */
    static CType conditionalCommon(CType left, CType right) {
        left = left.decay();
        right = right.decay();
        if (left.kind == Kind.POINTER && right.kind == Kind.POINTER) {
            CType element = commonImmediateVolatile(left.element, right.element);
            if (element != null) {
                return pointer(element);
            }
            if (left.same(right)) {
                throw new IllegalArgumentException("Cannot implicitly discard volatile across nested pointer or array qualification in a conditional expression. Use an explicit cast if this is intended.");
            }
            if (left.element.kind == Kind.VOID || right.element.kind == Kind.VOID) {
                CType otherElement = left.element.kind == Kind.VOID ? right.element : left.element;
                if (otherElement.kind != Kind.FUNCTION) {
                    CType voidElement = left.element.volatileQualified || right.element.volatileQualified ? VOID.asVolatile() : VOID;
                    return pointer(voidElement);
                }
            }
            throw new IllegalArgumentException("Incompatible conditional pointer types.");
        }
        return common(left, right);
    }

    private static CType commonImmediateVolatile(CType left, CType right) {
        boolean leftQualified = left.kind == Kind.ARRAY ? arrayHasVolatile(left) : left.volatileQualified;
        boolean rightQualified = right.kind == Kind.ARRAY ? arrayHasVolatile(right) : right.volatileQualified;
        CType leftBase = left.kind == Kind.ARRAY ? unqualifiedArray(left) : unwrap(left);
        CType rightBase = right.kind == Kind.ARRAY ? unqualifiedArray(right) : unwrap(right);
        if (!leftBase.sameDeclaration(rightBase)) {
            return null;
        }
        CType composite = leftBase.compositeDeclaration(rightBase);
        return leftQualified || rightQualified ? composite.asVolatile() : composite;
    }

    private static boolean arrayHasVolatile(CType type) {
        return type.volatileQualified || type.kind == Kind.ARRAY
                && (type.element.kind == Kind.ARRAY ? arrayHasVolatile(type.element) : type.element.volatileQualified);
    }

    private static CType unqualifiedArray(CType type) {
        CType element = type.element.kind == Kind.ARRAY ? unqualifiedArray(type.element) : unwrap(type.element);
        return CType.array(element, type.count);
    }

    private static boolean sameExactly(CType left, CType right) {
        if (left == right) {
            return true;
        }
        if (left == null || right == null || left.volatileQualified != right.volatileQualified
                || left.kind != right.kind || left.size != right.size || left.count != right.count
                || left.unsigned != right.unsigned || left.isBoolean() != right.isBoolean()) {
            return false;
        }
        if (left.aggregate() || right.aggregate()) {
            return false;
        }
        if (left.element == null ? right.element != null : right.element == null || !sameExactly(left.element, right.element)) {
            return false;
        }
        if (left.kind != Kind.FUNCTION) {
            return true;
        }
        if (left.variadic != right.variadic || left.parameters.size() != right.parameters.size()) {
            return false;
        }
        for (int index = 0; index < left.parameters.size(); index++) {
            if (!sameExactly(left.parameters.get(index), right.parameters.get(index))) {
                return false;
            }
        }
        return true;
    }

    private String parameterDescription() {
        String description = String.join(", ", parameters.stream().map(CType::toString).toList());
        return variadic ? description + (parameters.isEmpty() ? "..." : ", ...") : description;
    }

    /** Returns the C spelling of this type, including qualifiers and declarator shape. */
    @Override
    public String toString() {
        if (volatileQualified) {
            return unqualified + " volatile";
        }
        if (kind == Kind.FUNCTION) {
            return element + " (" + parameterDescription() + ")";
        }
        if (kind == Kind.POINTER && element.kind == Kind.FUNCTION) {
            return element.element + " (*)(" + element.parameterDescription() + ")";
        }
        if (kind == Kind.POINTER) {
            return element + "*";
        }
        if (kind == Kind.ARRAY) {
            return element + "[" + count + "]";
        }
        return unsigned && (name.equals("long") || name.equals("short"))
                ? "unsigned " + name : name;
    }
}
