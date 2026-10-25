package C8080;

import Intel8080.assembler.Assembler;
import static C8080.Parser.*;
import static C8080.Token.TokenType.*;

import java.math.BigInteger;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;

/** Lowers parsed C translation units into Intel 8080 assembly with stack-frame and runtime support. */
final class CodeGenerator {
    private static final Pattern INLINE_LAYOUT_DIRECTIVE = Pattern.compile(
            "(?i)^\\s*(?:(?:[A-Za-z_$][A-Za-z_$0-9]*)\\s*:\\s*)?(?:\\.?\\s*(?:TEXT|CODE|DATA|SECTION|ORG|DB|DW|DD|DQ|DS|END|PUBLIC|GLOBAL|EXTERN|EQU)\\b|[A-Za-z_$][A-Za-z_$0-9]*\\s+EQU\\b).*");
    private static final Pattern INLINE_LABEL = Pattern.compile("^\\s*([A-Za-z_$][A-Za-z_$0-9]*)\\s*:");
    private static final Pattern INLINE_SYMBOL = Pattern.compile("\\$([A-Za-z_][A-Za-z_0-9]*)");
    private static final Pattern INLINE_BRANCH_TARGET = Pattern.compile(
            "(?i)^(\\s*(?:(?:[A-Za-z_$][A-Za-z_$0-9]*)\\s*:\\s*)?(?:JMP|JNZ|JZ|JNC|JC|JPO|JPE|JP|JM)\\s+)([A-Za-z_$][A-Za-z_$0-9]*)(\\s*)$");
    private static final Set<String> INLINE_BRANCHES = Set.of("JMP", "JNZ", "JZ", "JNC", "JC", "JPO", "JPE", "JP", "JM");
    /** Storage location: a global label, or a BC frame offset when the label is null. */
    record Slot(String label, int offset) {
        Slot at(int delta) {
            return new Slot(label, offset + delta);
        }
    }
    /** A typed value held in a storage slot. */
    record Value(CType type, Slot slot) {}
    /** An assignable location, addressed directly by slot or indirectly through a pointer value. */
    record LValue(CType type, Slot slot, Value pointer) {}
    private record Binding(CType type, Slot slot) {}
    private record NarrowedCounter(CType storedType, boolean descending, BigInteger bias) {}
    private record NarrowedLoop(DeclStmt declaration, CType counterType, BigInteger count, boolean descending,
                                BigInteger bias) {}
    private final String namespace;
    private final Map<Object, Token> positions;
    private final BooleanSupplier cancelled;
    private boolean optimized;
    private Token diagnosticToken = new Token(EOF, "", 1, 1);
    private final Map<String, Binding> globals = new LinkedHashMap<>();
    private final Map<String, Slot> stringConstants = new LinkedHashMap<>();
    private final Map<String, Function> functions = new LinkedHashMap<>();
    private List<String> inlineAssemblySources = List.of();
    private final Map<String, Set<String>> declaredAtDefinition = new LinkedHashMap<>();
    private Set<String> visibleFunctions = Set.of();
    private final Map<String, String> functionLabels = new LinkedHashMap<>();
    private final Deque<Map<String, Binding>> scopes = new ArrayDeque<>();
    private final Map<Slot, NarrowedCounter> narrowedCounters = new HashMap<>();
    private final StringBuilder declarations = new StringBuilder(), data = new StringBuilder(),
                                text = new StringBuilder();
    private StringBuilder code = new StringBuilder();
    private Function function;
    private String exit, breakLabel, continueLabel;
    private int next, peak, label, dataBytes;
    private final RuntimeLibrary runtime = new RuntimeLibrary();

    private String inlineRuntime = "";
    private String runtimePrefix;
    CodeGenerator() {
        this("UNIT", Map.of());
    }
    CodeGenerator(String namespace, Map<Object, Token> positions) {
        this(namespace, positions, false, () -> false);
    }
    CodeGenerator(String namespace, Map<Object, Token> positions, boolean optimized) {
        this(namespace, positions, optimized, () -> false);
    }
    CodeGenerator(String namespace, Map<Object, Token> positions, boolean optimized, BooleanSupplier cancelled) {
        this.namespace = namespace;
        this.positions = positions;
        this.optimized = optimized;
        this.cancelled = cancelled == null ? () -> false : cancelled;
    }
    String generate(Unit unit) {
        checkCancelled();
        inlineAssemblySources = collectInlineAssemblySources(unit.functions());
        runtimePrefix = "_VCC_RT_" + namespace + "_";
        while (hasRuntimePrefixConflict(unit.functions())) runtimePrefix += "R_";
        Set<String> declared = new LinkedHashSet<>();
        for (Function fn : unit.functions()) {
            checkCancelled();
            declared.add(fn.name());
            if (fn.body() != null)
                declaredAtDefinition.put(fn.name(), Set.copyOf(declared));
            diagnosticToken = positions.getOrDefault(fn, diagnosticToken);
            Function previous = functions.get(fn.name());
            if (previous != null) {
                if (previous.storage() == Storage.STATIC && fn.storage() != Storage.STATIC)
                    fn = new Function(fn.type(), fn.name(), fn.parameters(), fn.variadic(), Storage.STATIC, fn.body());
                if (!previous.type().sameDeclaration(fn.type()) || previous.parameters().size() != fn.parameters().size()
                        || previous.variadic() != fn.variadic())
                    fail("Conflicting declaration for " + fn.name() + ".\nExpected: " + signature(previous)
                            + "\nPresented: " + signature(fn));
                for (int n = 0; n < fn.parameters().size(); n++)
                    if (!previous.parameters().get(n).type().sameParameterDeclaration(fn.parameters().get(n).type()))
                        fail("Conflicting parameter " + (n + 1) + " for " + fn.name()
                                + ".\nExpected: " + signature(previous) + "\nPresented: " + signature(fn));
                if (previous.body() != null && fn.body() != null)
                    fail("Duplicate function definition " + fn.name());
            }
            if (previous != null && previous.storage() == Storage.STATIC && fn.storage() != Storage.STATIC) {
                Token at = positions.get(fn);
                fn = new Function(fn.type(), fn.name(), fn.parameters(), fn.variadic(), Storage.STATIC, fn.body());
                if (at != null)
                    positions.put(fn, at);
            } else if (previous != null && previous.storage() != Storage.STATIC && fn.storage() == Storage.STATIC)
                fail("A function already declared with external linkage cannot later become static.");
            if (previous == null || fn.body() != null)
                functions.put(fn.name(), fn);
            if (!functionLabels.containsKey(fn.name()))
                functionLabels.put(fn.name(),
                        fn.storage() == Storage.STATIC ? fresh("static_" + fn.name()) : functionLabel(fn.name()));
        }
        for (DeclStmt declaration : unit.globals()) {
            checkCancelled();
            diagnosticToken = positions.getOrDefault(declaration, diagnosticToken);
            Binding previous = globals.get(declaration.name());
            if (previous != null && !previous.type.sameDeclaration(declaration.type()))
                fail("Conflicting declaration for " + declaration.name() + ".\nExpected: " + previous.type + " "
                        + declaration.name() + "\nPresented: " + declaration.type() + " " + declaration.name());
            CType type = previous == null ? declaration.type() : previous.type.compositeDeclaration(declaration.type());
            String symbol = declaration.storage() == Storage.STATIC ? fresh("static_" + declaration.name())
                                                                    : symbol("G", declaration.name());
            if (previous != null)
                symbol = previous.slot.label;
            globals.put(declaration.name(), new Binding(type, new Slot(symbol, 0)));
        }
        Map<String, DeclStmt> definitions = new LinkedHashMap<>();
        for (DeclStmt declaration : unit.globals()) {
            checkCancelled();
            diagnosticToken = positions.getOrDefault(declaration, diagnosticToken);
            Binding binding = globals.get(declaration.name());
            if (declaration.storage() == Storage.EXTERN && declaration.initializer() == null) {
                declarations.append("extern ").append(binding.slot.label).append('\n');
                continue;
            }
            DeclStmt previous = definitions.get(declaration.name());
            if (previous != null && previous.initializer() != null && declaration.initializer() != null)
                fail("Duplicate global definition " + declaration.name());
            if (previous == null || declaration.initializer() != null)
                definitions.put(declaration.name(), declaration);
        }
        for (DeclStmt declaration : definitions.values()) {
            checkCancelled();
            visibleFunctions = unit.visibleAtGlobal().getOrDefault(declaration, Set.of());
            diagnosticToken = positions.getOrDefault(declaration, diagnosticToken);
            Binding binding = globals.get(declaration.name());
            if (declaration.storage() != Storage.STATIC)
                declarations.append("public ").append(binding.slot.label).append('\n');
            staticData(binding.slot.label, binding.type, declaration.initializer());
        }
        for (Function fn : functions.values()) {
            checkCancelled();
            String symbol = functionLabels.get(fn.name());
            if (fn.body() == null)
                declarations.append("extern ").append(symbol).append('\n');
            else {
                if (fn.storage() != Storage.STATIC)
                    declarations.append("public ").append(symbol).append('\n');
                emitFunction(fn);
            }
        }
        String entryName = functions.containsKey("main") && functions.get("main").body() != null ? "main"
                : functions.containsKey("_start") && functions.get("_start").body() != null ? "_start" : null;
        if (entryName != null) {
            Function entry = functions.get(entryName);
            diagnosticToken = positions.getOrDefault(entry, diagnosticToken);
            if (!entry.parameters().isEmpty())
                fail(entryName + " currently takes no arguments.");
            if (entryName.equals("main") && !entry.type().same(CType.INT))
                fail("main must return int.");
            if (entryName.equals("_start") && !entry.type().same(CType.INT) && entry.type().kind != CType.Kind.VOID)
                fail("_start must return int or void.");
            text.insert(0,
                    "global $start\n$start:\n    LXI SP, 0x100000000\n    CALL " + functionLabels.get(entryName)
                            + "\n    STOP\n");
        }
        String usedCode = text.toString() + data;
        StringBuilder usedDeclarations = new StringBuilder();
        for (String line : declarations.toString().split("\n")) {
            checkCancelled();
            if (line.startsWith("extern ")) {
                String external = line.substring(7).trim();
                if (!java.util.regex.Pattern
                                .compile("(?<![A-Za-z_0-9])" + java.util.regex.Pattern.quote(external)
                                        + "(?![A-Za-z_0-9])")
                                .matcher(usedCode)
                                .find())
                    continue;
            }
            usedDeclarations.append(line).append('\n');
        }
        String runtimeAssembly = runtime.assembly(runtimePrefix, cancelled);
        checkCancelled();
        String assembly = "; VCC_ABI64\n" + usedDeclarations + ".text\n" + text + runtimeAssembly + ".data\n" + data;
        checkCancelled();
        return assembly;
    }
    private void checkCancelled() {
        if (cancelled.getAsBoolean()) throw new CancellationException("Code generation was cancelled.");
    }
    private boolean hasRuntimePrefixConflict(List<Function> functions) {
        for (Function candidate : functions) {
            checkCancelled();
            if (candidate.name().startsWith(runtimePrefix)) return true;
        }
        return false;
    }
    private static String functionLabel(String name) {
        return name.equals("printf") || name.equals("putchar") || name.equals("memcpy") ? name.toUpperCase(Locale.ROOT)
                                                                                        : name;
    }
    private static String symbol(String kind, String name) {
        StringBuilder out = new StringBuilder("_VCC_").append(kind);
        name.codePoints().forEach(c -> out.append('_').append(Integer.toHexString(c).toUpperCase(Locale.ROOT)));
        return out.toString();
    }
    private String fresh(String purpose) {
        return ("_VCC_" + namespace + "_" + (function == null ? "" : function.name() + "_") + purpose + "_" + label++)
                .replaceAll("[^A-Za-z_0-9]", "_");
    }
    private void emit(String instruction) {
        checkCancelled();
        code.append(ByteAssembly.lower(instruction, fresh("byte")));
    }
    private void nativeEmit(String instruction) {
        checkCancelled();
        code.append("    ").append(instruction).append('\n');
    }

    private void inlineAssembly(AsmStmt statement) {
        String source = resolveInlineSymbols(statement.source());
        validateInlineAssembly(source);
        if (source.isBlank()) return;
        String marker = freshInlineAssemblyMarker();
        nativeEmit("PUSH B");
        nativeEmit(AssemblyOptimizer.inlineBegin(marker));
        code.append(source);
        if (source.charAt(source.length() - 1) != '\n' && source.charAt(source.length() - 1) != '\r')
            code.append('\n');
        nativeEmit(AssemblyOptimizer.inlineEnd(marker));
        nativeEmit("POP B");
    }

    private String resolveInlineSymbols(String source) {
        Map<String, String> localLabels = new LinkedHashMap<>();
        String[] lines = source.split("(?<=\\n)|(?<=\\r)(?!\\n)", -1);
        for (String line : lines) {
            int comment = line.indexOf(';');
            Matcher label = INLINE_LABEL.matcher(comment < 0 ? line : line.substring(0, comment));
            if (label.find()) {
                String name = inlineLabelName(label.group(1));
                localLabels.putIfAbsent(name, name);
            }
        }
        String prefix = localLabels.isEmpty() ? "" : fresh("inline_asm");
        localLabels.replaceAll((name, label) -> prefix + "_" + name.replaceAll("[^A-Za-z_0-9]", "_"));
        StringBuilder resolved = new StringBuilder(source.length());
        for (String line : lines) {
            int contentEnd = line.length();
            while (contentEnd > 0 && (line.charAt(contentEnd - 1) == '\r' || line.charAt(contentEnd - 1) == '\n'))
                contentEnd--;
            String content = line.substring(0, contentEnd);
            String lineEnding = line.substring(contentEnd);
            int comment = content.indexOf(';');
            String instruction = comment < 0 ? content : content.substring(0, comment);
            String suffix = comment < 0 ? "" : content.substring(comment);
            Matcher label = INLINE_LABEL.matcher(instruction);
            if (label.find()) {
                String local = localLabels.get(inlineLabelName(label.group(1)));
                if (local != null) instruction = instruction.substring(0, label.start(1)) + local
                        + instruction.substring(label.end(1));
            }
            instruction = resolveInlineDollarSymbols(instruction, localLabels);
            Matcher branch = INLINE_BRANCH_TARGET.matcher(instruction);
            if (branch.matches()) {
                String local = localLabels.get(inlineLabelName(branch.group(2)));
                if (local != null) instruction = branch.group(1) + local + branch.group(3);
            }
            resolved.append(instruction).append(suffix).append(lineEnding);
        }
        return resolved.toString();
    }

    private String resolveInlineDollarSymbols(String instruction, Map<String, String> localLabels) {
        Matcher symbol = INLINE_SYMBOL.matcher(instruction);
        StringBuffer resolved = new StringBuffer(instruction.length());
        while (symbol.find()) {
            String name = symbol.group(1);
            String replacement = localLabels.get(name);
            if (replacement == null) {
                Binding global = globals.get(name);
                replacement = global == null ? symbol.group() : global.slot.label;
            }
            symbol.appendReplacement(resolved, Matcher.quoteReplacement(replacement));
        }
        symbol.appendTail(resolved);
        return resolved.toString();
    }

    private static String inlineLabelName(String label) {
        return label.startsWith("$") ? label.substring(1) : label;
    }

    private String freshInlineAssemblyMarker() {
        String marker;
        boolean collision;
        do {
            marker = fresh("inline_marker");
            String begin = AssemblyOptimizer.inlineBegin(marker);
            String end = AssemblyOptimizer.inlineEnd(marker);
            collision = false;
            for (String source : inlineAssemblySources) {
                if (source.contains(begin) || source.contains(end)) {
                    collision = true;
                    break;
                }
            }
        } while (collision);
        return marker;
    }

    private List<String> collectInlineAssemblySources(List<Function> candidates) {
        List<String> sources = new ArrayList<>();
        for (Function candidate : candidates) collectInlineAssemblySources(candidate.body(), sources);
        return List.copyOf(sources);
    }

    private void collectInlineAssemblySources(Stmt statement, List<String> sources) {
        checkCancelled();
        if (statement == null) return;
        if (statement instanceof AsmStmt assembly) sources.add(assembly.source());
        else if (statement instanceof BlockStmt block) block.statements().forEach(child -> collectInlineAssemblySources(child, sources));
        else if (statement instanceof IfStmt conditional) {
            collectInlineAssemblySources(conditional.yes(), sources);
            collectInlineAssemblySources(conditional.no(), sources);
        } else if (statement instanceof WhileStmt loop) collectInlineAssemblySources(loop.body(), sources);
        else if (statement instanceof DoWhileStmt loop) collectInlineAssemblySources(loop.body(), sources);
        else if (statement instanceof ForStmt loop) {
            collectInlineAssemblySources(loop.init(), sources);
            collectInlineAssemblySources(loop.body(), sources);
        } else if (statement instanceof SwitchStmt selection) {
            for (SwitchCase branch : selection.cases())
                branch.statements().forEach(child -> collectInlineAssemblySources(child, sources));
        }
    }

    private void validateInlineAssembly(String source) {
        for (String line : source.split("\\R", -1)) {
            int comment = line.indexOf(';');
            String instruction = (comment < 0 ? line : line.substring(0, comment)).strip();
            if (INLINE_LAYOUT_DIRECTIVE.matcher(instruction).matches())
                fail("Inline asm supports instructions and labels only; section and layout directives are not allowed.");
        }

        Assembler.ObjectCode parsed;
        try {
            parsed = Assembler.assembleRelocatable(source);
        } catch (RuntimeException error) {
            fail("Invalid inline assembly: " + error.getMessage());
            return;
        }
        if (!parsed.equates().isEmpty())
            fail("Inline asm supports instructions and labels only; equates are not allowed.");

        Set<String> labels = new HashSet<>();
        for (Assembler.ObjectAtom atom : parsed.atoms()) labels.addAll(atom.labels());
        for (Assembler.ObjectAtom atom : parsed.atoms()) {
            if (!atom.section().equals(".text") || atom.origin())
                fail("Inline asm supports instructions and labels only; section and layout directives are not allowed.");
            String mnemonic = atom.mnemonic().toUpperCase(Locale.ROOT);
            if (mnemonic.isEmpty()) {
                if (atom.bytes().length != 0 || atom.labels().isEmpty())
                    fail("Inline asm supports instructions and labels only.");
                continue;
            }
            if (mnemonic.equals("RET") || mnemonic.equals("PCHL") || mnemonic.equals("HLT")
                    || mnemonic.equals("MOV M, M") || mnemonic.equals("STOP") || mnemonic.startsWith("RST "))
                fail("Inline asm control flow must stay within the block and return to C.");
            if (INLINE_BRANCHES.contains(mnemonic) && !labels.contains(atom.operand().strip()))
                fail("Inline asm jump targets must be labels defined in the same block.");
        }
    }

    private void mark(String name) {
        checkCancelled();
        code.append(name).append(":\n");
    }
    private Slot allocate(int size) {
        if (size <= 0)
            fail("Object has incomplete or void type.");
        next += size;
        peak = Math.max(peak, next);
        if (peak > MemoryLimit.STACK_BYTES)
            fail("Stack frame exceeds the reserved 4 KiB stack.");
        return new Slot(null, -16 - next);
    }
    private static final class MemoryLimit {
        static final int STACK_BYTES = 3900;
    }
    private Value temp(CType type) {
        return new Value(type, allocate(Math.max(1, type.size)));
    }
    private Value integer(BigInteger value, CType type) {
        if (type.kind == CType.Kind.FLOAT) {
            Value result = temp(type);
            storeConstant(result.slot, type.size, value);
            return result;
        }
        if (type.scalar() && type.size >= 8 && type.size % 4 == 0
                && (value.signum() == 0 || value.equals(BigInteger.valueOf(-1)))) {
            Value result = temp(type);
            runtime.require("FILL_WORDS");
            emit("PUSH PSW");
            frameAddress(result.slot.offset);
            emit("PUSH B");
            nativeEmit("MVI B, " + type.size / 4);
            nativeEmit("MVI A, " + (value.signum() == 0 ? 0 : 0xffffffffL));
            wordCall("FILL_WORDS");
            emit("POP B");
            emit("POP PSW");
            return result;
        }
        if (type.scalar() && type.size % 4 == 0) {
            Value result = temp(type);
            storeConstant(result.slot, type.size, value);
            return result;
        }
        if (type.size >= 8 && type.size <= 255 && (value.signum() == 0 || value.equals(BigInteger.valueOf(-1)))) {
            Value result = temp(type);
            runtime.require("FILL_BYTES");
            emit("PUSH PSW");
            frameAddress(result.slot.offset);
            emit("PUSH B");
            emit("MVI B, " + type.size);
            emit("MVI A, " + (value.signum() == 0 ? 0 : 255));
            emit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + "FILL_BYTES");
            emit("POP B");
            emit("POP PSW");
            return result;
        }
        Value result = temp(type);
        emit("PUSH PSW");
        frameAddress(result.slot.offset);
        emit("POP PSW");
        for (int n = 0; n < type.size; n++) {
            emit("MVI M, " + value.shiftRight(n * 8).and(BigInteger.valueOf(255)));
            if (n + 1 < type.size)
                emit("INX H");
        }
        return result;
    }
    private Value integer(long value, CType type) {
        return integer(BigInteger.valueOf(value), type);
    }
    private void frameAddress(int offset) {
        emit("LXI H, " + offset);
        emit("DAD B");
    }
    private void address(Slot slot) {
        if (slot.label == null)
            frameAddress(slot.offset);
        else
            emit("LXI H, " + (slot.offset == 0 ? slot.label : "(" + slot.label + "+" + slot.offset + ")"));
    }

    private void load(Slot slot) {
        if (slot.label == null) {
            emit("LDBC " + slot.offset);
            return;
        }
        address(slot);
        emit("MOV A, M");
    }

    private void store(Slot slot) {
        if (slot.label == null) {
            emit("STBC " + slot.offset);
            return;
        }
        address(slot);
        emit("MOV M, A");
    }

    private Value addressValue(Slot slot, CType type) {
        address(slot);
        Value result = temp(CType.pointer(type));
        registerPointer(result);
        return result;
    }
    private void registerPointer(Value result) {
        emit("PUSH H");
        emit("POP D");
        emit("MOV A, E");
        storeWord(result.slot, Math.min(4, result.type.size));
        if (result.type.size > 4) {
            emit("MOV A, D");
            storeWord(result.slot.at(4), Math.min(4, result.type.size - 4));
        }
    }

    private void pointerRegisters(Value pointer) {
        emit("PUSH D");
        loadWord(pointer.slot, Math.min(4, pointer.type.size));
        emit("MOV E, A");
        if (pointer.type.size > 4)
            loadWord(pointer.slot.at(4), Math.min(4, pointer.type.size - 4));
        else
            emit("MVI A, 0");
        emit("MOV D, A");
        emit("PUSH D");
        emit("POP H");
        emit("POP D");
    }
    private void wordCall(String name) {
        runtime.require(name);
        nativeEmit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + name);
    }
    private void loadWord(Slot slot, int bytes) {
        if (bytes == 4) {
            if (slot.label == null) {
                emit("LDBC32 " + slot.offset);
                return;
            }
            address(slot);
            wordCall("LOAD32");
            return;
        }
        if (bytes == 1) {
            load(slot);
            return;
        }
        emit("PUSH D");
        emit("MVI E, 0");
        for (int n = bytes - 1; n >= 0; n--) {
            emit("MOV A, E");
            nativeEmit("RLC 8");
            emit("MOV E, A");
            load(slot.at(n));
            nativeEmit("ORA E");
            emit("MOV E, A");
        }
        emit("MOV A, E");
        emit("POP D");
    }
    private void storeWord(Slot slot, int bytes) {
        if (bytes == 4) {
            if (slot.label == null) {
                emit("STBC32 " + slot.offset);
                return;
            }
            address(slot);
            wordCall("STORE32");
            return;
        }
        for (int n = 0; n < bytes; n++) {
            store(slot.at(n));
            nativeEmit("RRC 8");
        }
    }
    private void storeConstant(Slot slot, int size, BigInteger value) {
        emit("PUSH PSW");
        if (size >= 4) {
            int n = 0;
            for (; n + 4 <= size; n += 4) {
                if ((n & 255) == 0)
                    checkCancelled();
                nativeEmit("MVI A, " + value.shiftRight(n * 8).and(BigInteger.valueOf(0xffffffffL)));
                storeWord(slot.at(n), 4);
            }
            for (; n < size; n++) {
                nativeEmit("MVI A, " + value.shiftRight(n * 8).and(BigInteger.valueOf(255)));
                nativeEmit("STBC " + (slot.offset + n));
            }
        } else {
            frameAddress(slot.offset);
            emit("POP PSW");
            for (int n = 0; n < size; n++) {
                if ((n & 255) == 0)
                    checkCancelled();
                nativeEmit("MVI M, " + value.shiftRight(n * 8).and(BigInteger.valueOf(255)));
                if (n + 1 < size)
                    emit("INX H");
            }
            return;
        }
        emit("POP PSW");
    }
    private void storeBytes(Slot slot, byte[] bytes) {
        emit("PUSH PSW");
        int n = 0;
        for (; n + 4 <= bytes.length; n += 4) {
            if ((n & 255) == 0)
                checkCancelled();
            long word = (bytes[n] & 255L) | (bytes[n + 1] & 255L) << 8
                    | (bytes[n + 2] & 255L) << 16 | (bytes[n + 3] & 255L) << 24;
            nativeEmit("MVI A, " + word);
            storeWord(slot.at(n), 4);
        }
        for (; n < bytes.length; n++) {
            nativeEmit("MVI A, " + (bytes[n] & 255));
            nativeEmit("STBC " + (slot.offset + n));
        }
        emit("POP PSW");
    }

    private void copy(Value target, Value source) {
        if (target.slot.equals(source.slot) && target.type.size == source.type.size)
            return;
        if (target.type.scalar() && source.type.scalar() && target.type.size % 4 == 0) {
            emit("PUSH PSW");
            boolean backward = target.slot.label == null && source.slot.label == null
                    && target.slot.offset > source.slot.offset
                    && target.slot.offset < source.slot.offset + source.type.size;
            for (int step = 0; step < target.type.size; step += 4) {
                int n = backward ? target.type.size - 4 - step : step;
                if (n < source.type.size) {
                    int bytes = Math.min(4, source.type.size - n);
                    loadWord(source.slot.at(n), bytes);
                    if (bytes < 4 && !source.type.unsigned&& source.type.kind == CType.Kind.INTEGER) {
                        String positive = fresh("word_positive"), done = fresh("word_signed");
                        emit("MOV D, A");
                        nativeEmit("ANI " + (1L << (bytes * 8 - 1)));
                        emit("JZ " + positive);
                        emit("MOV A, D");
                        nativeEmit("ORI " + (0xffffffffL << bytes * 8 & 0xffffffffL));
                        emit("JMP " + done);
                        mark(positive);
                        emit("MOV A, D");
                        mark(done);
                    }
                } else if (source.type.unsigned || source.type.kind == CType.Kind.POINTER
                        || source.type.kind == CType.Kind.FLOAT)
                    nativeEmit("MVI A, 0");
                else {
                    int at = Math.max(0, source.type.size - 4), bytes = Math.min(4, source.type.size);
                    loadWord(source.slot.at(at), bytes);
                    nativeEmit("RLC " + (33 - bytes * 8));
                    nativeEmit("SBB A");
                }
                storeWord(target.slot.at(n), 4);
            }
            emit("POP PSW");
            return;
        }
        if (target.slot.label == null && source.slot.label == null && target.type.size == source.type.size) {
            if (target.type.aggregate() || source.type.aggregate())
                if (!target.type.same(source.type))
                    fail("Incompatible aggregate assignment.");
            boolean backward = target.slot.offset > source.slot.offset
                    && target.slot.offset < source.slot.offset + source.type.size;
            if (!backward && source.type.size >= 8 && source.type.size <= 255) {
                runtime.require("COPY_BYTES");
                emit("PUSH D");
                emit("PUSH PSW");
                frameAddress(source.slot.offset);
                emit("XCHG");
                frameAddress(target.slot.offset);
                emit("PUSH B");
                emit("MVI B, " + source.type.size);
                emit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + "COPY_BYTES");
                emit("POP B");
                emit("POP PSW");
                emit("POP D");
                return;
            }
            int first = backward ? source.type.size - 1 : 0;
            emit("PUSH D");
            emit("PUSH PSW");
            frameAddress(source.slot.offset + first);
            emit("XCHG");
            frameAddress(target.slot.offset + first);
            emit("POP PSW");
            for (int n = 0; n < source.type.size; n++) {
                emit("LDAX D");
                emit("MOV M, A");
                if (n + 1 < source.type.size) {
                    emit((backward ? "DCX" : "INX") + " D");
                    emit((backward ? "DCX" : "INX") + " H");
                }
            }
            emit("POP D");
            return;
        }
        if (target.type.aggregate() || source.type.aggregate()) {
            if (!target.type.same(source.type))
                fail("Incompatible aggregate assignment.");
        }
        for (int n = 0; n < target.type.size; n++) {
            if (n < source.type.size)
                load(source.slot.at(n));
            else if (source.type.unsigned || source.type.kind == CType.Kind.POINTER)
                emit("MVI A, 0");
            else {
                load(source.slot.at(source.type.size - 1));
                emit("RLC 1");
                emit("SBB A");
            }
            store(target.slot.at(n));
        }
    }
    private void requireImplicitConversion(CType source, CType destination) {
        CType sourceValue = source.decay();
        CType destinationValue = destination.decay();
        if (sourceValue.kind == CType.Kind.POINTER && destinationValue.kind == CType.Kind.POINTER
                && discardsVolatilePointee(sourceValue.element, destinationValue.element))
            fail("Cannot implicitly discard volatile from " + sourceValue.element + " through pointer conversion to "
                    + destinationValue + ". Use an explicit cast if discarding volatile is intended.");
        if (destination.kind == CType.Kind.INTEGER && !destination.isBoolean()
                && source.kind == CType.Kind.FLOAT)
            fail("This expression has type " + source + ", but the destination needs " + destination
                    + (".\nA floating value can lose its fractional part when stored as an integer. Use a floating "
                       + "destination, or an explicit (")
                    + destination + ") cast if truncation is intended.");
    }
    private boolean discardsVolatilePointee(CType source, CType destination) {
        if (source.volatileQualified && !destination.volatileQualified)
            return true;
        if (source.kind != destination.kind)
            return false;
        return (source.kind == CType.Kind.POINTER || source.kind == CType.Kind.ARRAY)
                && discardsVolatilePointee(source.element, destination.element);
    }
    private Value implicitConvert(Value source, CType destination) {
        requireImplicitConversion(source.type, destination);
        return convert(source, destination);
    }
    private Value convert(Value source, CType type) {
        if (type.kind == CType.Kind.VOID)
            return new Value(CType.VOID, source.slot);
        if (source.type.kind == CType.Kind.VOID)
            fail("A void expression has no value.");
        if (type.same(source.type))
            return new Value(type, source.slot);
        if (type.isBoolean()) {
            Value result = integer(0, type);
            String zero = fresh("bool_zero");
            test(source);
            emit("JZ " + zero);
            emit("MVI A,1");
            store(result.slot);
            mark(zero);
            return result;
        }
        if (type.kind == CType.Kind.FLOAT || source.type.kind == CType.Kind.FLOAT)
            return floatingConvert(source, type);
        if (!type.scalar() && !type.aggregate())
            fail("Invalid conversion to " + type);
        Value result = temp(type);
        copy(result, source);
        return result;
    }
    private Binding binding(String name) {
        for (Map<String, Binding> scope : scopes) {
            Binding found = scope.get(name);
            if (found != null)
                return found;
        }
        Binding found = globals.get(name);
        if (found == null)
            fail("Unknown variable " + name);
        return found;
    }
    private boolean hasVariable(String name) {
        for (var scope : scopes)
            if (scope.containsKey(name))
                return true;
        return globals.containsKey(name);
    }
    private CType functionType(Function fn) {
        return CType.function(fn.type(), fn.parameters().stream().map(DeclStmt::type).toList(), fn.variadic());
    }
    private static String signature(Function fn) {
        return signature(fn, fn.name(), false);
    }
    private static String signature(Function fn, String name, boolean functionPointer) {
        List<String> parameters = new ArrayList<>(fn.parameters().stream().map(parameter -> {
            String parameterName = parameter.name();
            return parameter.type() + (parameterName == null || parameterName.isBlank() || parameterName.startsWith("_argument_") || parameterName.startsWith("_parameter_")
                    ? "" : " " + parameterName);
        }).toList());
        if (parameters.isEmpty() && !fn.variadic()) parameters.add("void");
        if (fn.variadic()) parameters.add("...");
        String declarator = functionPointer ? "(*" + name + ")" : name;
        return fn.type() + " " + declarator + "(" + String.join(", ", parameters) + ")";
    }
    private CType typeOf(Expr expression) {
        if (expression instanceof NumberExpr n)
            return n.type();
        if (expression instanceof FloatExpr n)
            return n.type();
        if (expression instanceof StringExpr s)
            return CType.array(CType.CHAR, s.value().length() + 1);
        if (expression instanceof VariableExpr v) {
            if (functions.containsKey(v.name()) && !hasVariable(v.name())) {
                requireVisibleFunction(v.name());
                return functionType(functions.get(v.name()));
            }
            return binding(v.name()).type;
        }
        if (expression instanceof MemberExpr m) {
            CType base = typeOf(m.base());
            if (m.pointer())
                base = base.decay().element;
            if (base == null || !base.aggregate())
                fail("Member access requires an aggregate.");
            CType member = base.field(m.name()).type();
            return base.volatileQualified ? member.asVolatile() : member;
        }
        if (expression instanceof IndexExpr index) {
            CType type = typeOf(index.base()).decay();
            if (type.kind != CType.Kind.POINTER)
                fail("Indexing requires an array or pointer.\nPresented: " + type
                        + (". Each comma declarator has its own '*': uint8 *a, b declares pointer a and scalar b; use "
                           + "uint8 *a, *b for two pointers."));
            return type.element;
        }
        if (expression instanceof UnaryExpr unary) {
            CType type = typeOf(unary.value());
            if (unary.op() == AMP)
                return CType.pointer(type);
            if (unary.op() == STAR) {
                if (type.decay().kind != CType.Kind.POINTER)
                    fail("Dereference requires a pointer.");
                return type.decay().element;
            }
            return unary.op() == BANG ? CType.INT : CType.common(type, CType.INT);
        }
        if (expression instanceof BinaryExpr binary) {
            CType left = typeOf(binary.left()).decay(), right = typeOf(binary.right()).decay();
            if (isComparison(binary.op()) || binary.op() == AND_AND || binary.op() == OR_OR)
                return CType.INT;
            if (binary.op() == MINUS && left.kind == CType.Kind.POINTER && right.kind == CType.Kind.POINTER)
                return CType.LONG;
            if (binary.op() == SHIFT_LEFT || binary.op() == SHIFT_RIGHT)
                return CType.common(left, CType.INT);
            return CType.common(left, right);
        }
        if (expression instanceof AssignExpr assign)
            return typeOf(assign.target());
        if (expression instanceof UpdateExpr update)
            return typeOf(update.target());
        if (expression instanceof CastExpr cast)
            return cast.type();
        if (expression instanceof SizeofExpr)
            return CType.UINT;
        if (expression instanceof ConditionalExpr conditional) {
            CType yes = typeOf(conditional.yes()), no = typeOf(conditional.no());
            if (yes.kind == CType.Kind.VOID || no.kind == CType.Kind.VOID) {
                if (yes.kind != no.kind)
                    fail("Conditional branches must both have void type or both supply values.");
                return CType.VOID;
            }
            diagnosticToken = positions.getOrDefault(conditional, diagnosticToken);
            try {
                return CType.conditionalCommon(yes, no);
            } catch (IllegalArgumentException incompatible) {
                fail(incompatible.getMessage());
            }
            return CType.VOID;
        }
        if (expression instanceof CommaExpr comma)
            return typeOf(comma.right());
        if (expression instanceof CallExpr call)
            return calledFunction(call).type();
        fail("Expression has no scalar type.");
        return CType.VOID;
    }
    private boolean directCall(CallExpr call) {
        return call.callee() instanceof VariableExpr variable && functions.containsKey(variable.name())
                && !hasVariable(variable.name());
    }
    private void requireVisibleFunction(String name) {
        if (!visibleFunctions.contains(name))
            fail("Function '" + name
                    + ("' has not been declared before this use. Add its header or a matching prototype before using "
                       + "it."));
    }
    private Function calledFunction(CallExpr call) {
        diagnosticToken = positions.getOrDefault(call, diagnosticToken);
        if (call.callee() instanceof VariableExpr name && !visibleFunctions.contains(name.name())
                && !hasVariable(name.name()))
            fail("Function '" + name.name()
                    + ("' has not been declared in this file.\nInclude the header declaring it (for example #include "
                       + "\"add.h\"), or write a matching function prototype before calling it. A definition in "
                       + "another .c file supplies code only after linking; it does not declare the function here."));
        if (directCall(call))
            return functions.get(((VariableExpr) call.callee()).name());
        CType type = typeOf(call.callee()).decay();
        if (type.kind != CType.Kind.POINTER || type.element.kind != CType.Kind.FUNCTION)
            fail("Call requires a function or function pointer.");
        CType signature = type.element;
        List<DeclStmt> parameters = new ArrayList<>();
        for (int n = 0; n < signature.parameters.size(); n++)
            parameters.add(new DeclStmt(signature.parameters.get(n), "_argument_" + n, null, Storage.AUTO));
        return new Function(signature.element, "<indirect>", parameters, signature.variadic, Storage.AUTO, null);
    }
    private LValue lvalue(Expr expression) {
        if (expression instanceof VariableExpr variable) {
            Binding binding = binding(variable.name());
            return new LValue(binding.type, binding.slot, null);
        }
        if (expression instanceof UnaryExpr unary && unary.op() == STAR) {
            Value pointer = expression(unary.value());
            if (pointer.type.kind != CType.Kind.POINTER)
                fail("Dereference requires a pointer.");
            return new LValue(pointer.type.element, null, pointer);
        }
        if (expression instanceof MemberExpr member) {
            CType base = typeOf(member.base());
            Value pointer;
            if (member.pointer()) {
                pointer = expression(member.base());
                base = base.decay().element;
            } else
                pointer = pointer(lvalue(member.base()));
            if (base == null || !base.aggregate())
                fail("Member access requires a struct or union.");
            CType.Field field = base.field(member.name());
            pointer = addPointer(pointer, integer(field.offset(), CType.UINT), false, 1);
            return new LValue(base.volatileQualified ? field.type().asVolatile() : field.type(), null, pointer);
        }
        if (expression instanceof IndexExpr index) {
            Value pointer = expression(index.base());
            if (pointer.type.kind != CType.Kind.POINTER)
                fail("Indexing requires an array or pointer.");
            pointer = addPointer(pointer, expression(index.index()), false, pointer.type.element.size);
            return new LValue(pointer.type.element, null, pointer);
        }
        fail("Assignment requires a modifiable object.");
        return null;
    }
    private Value pointer(LValue value) {
        return value.slot != null ? addressValue(value.slot, value.type) : value.pointer;
    }
    private Value read(LValue value) {
        if (value.type.size == 0)
            fail("Cannot read an incomplete or void object.");
        if (value.type.kind == CType.Kind.ARRAY) {
            Value address = pointer(value);
            return new Value(CType.pointer(value.type.element), address.slot);
        }
        Value result = temp(value.type);
        if (value.slot != null) {
            copy(result, new Value(value.type, value.slot));
            return result;
        }
        transferIndirect(value.pointer, result.slot, value.type.size, false);
        return result;
    }
    private void write(LValue target, Value value) {
        requireImplicitConversion(value.type, target.type);
        if (target.type.kind == CType.Kind.ARRAY)
            fail("Arrays cannot be assigned.");
        value = convert(value, target.type);
        if (target.slot != null) {
            copy(new Value(target.type, target.slot), value);
            return;
        }
        transferIndirect(target.pointer, value.slot, target.type.size, true);
    }

    private void transferIndirect(Value pointer, Slot local, int size, boolean writing) {
        emit("PUSH D");
        emit("PUSH PSW");
        pointerRegisters(pointer);
        emit("XCHG");
        address(local);
        if (writing)
            emit("XCHG");
        if (size >= 8 && size <= 255) {
            runtime.require("COPY_BYTES");
            emit("PUSH B");
            emit("MVI B, " + size);
            emit("CALL " + runtimePrefix + "COPY_BYTES");
            emit("POP B");
        } else
            for (int n = 0; n < size; n++) {
                emit("LDAX D");
                emit("MOV M, A");
                if (n + 1 < size) {
                    emit("INX D");
                    emit("INX H");
                }
            }
        emit("POP PSW");
        emit("POP D");
    }
    private Value expression(Expr expression) {
        diagnosticToken = positions.getOrDefault(expression, diagnosticToken);
        if (optimized && (expression instanceof BinaryExpr || expression instanceof UnaryExpr
                || expression instanceof CastExpr || expression instanceof ConditionalExpr)) {
            Value folded = foldConstant(expression);
            if (folded != null)
                return folded;
        }
        if (expression instanceof CommaExpr comma) {
            expression(comma.left());
            return expression(comma.right());
        }
        if (expression instanceof NumberExpr n)
            return integer(n.value(), n.type());
        if (expression instanceof FloatExpr n)
            return floatConstant(n.value(), n.type());
        if (expression instanceof StringExpr string)
            return addressValue(stringConstant(string), CType.CHAR);
        if (expression instanceof VariableExpr variable && functions.containsKey(variable.name())
                && !hasVariable(variable.name())) {
            requireVisibleFunction(variable.name());
            return addressValue(
                    new Slot(functionLabels.get(variable.name()), 0), functionType(functions.get(variable.name())));
        }
        if (expression instanceof VariableExpr variable && hasVariable(variable.name())) {
            Binding local = binding(variable.name());
            NarrowedCounter counter = narrowedCounters.get(local.slot());
            if (counter != null) {
                Value raw = read(new LValue(counter.storedType(), local.slot(), null));
                Value original = convert(raw, local.type());
                if (counter.bias().signum() == 0 && !counter.descending())
                    return original;
                Value bias = integer(counter.bias(), local.type());
                return counter.descending() ? binaryValues(bias, MINUS, original)
                        : binaryValues(original, PLUS, bias);
            }
        }
        if (expression instanceof VariableExpr || expression instanceof MemberExpr || expression instanceof IndexExpr)
            return read(lvalue(expression));
        if (expression instanceof CastExpr cast) {
            Value converted = convert(expression(cast.value()), cast.type());
            return new Value(cast.type(), converted.slot);
        }
        if (expression instanceof SizeofExpr size) {
            CType type = size.type() != null ? size.type() : typeOf(size.value());
            if (type.size == 0)
                fail("sizeof requires a complete object type.");
            return integer(type.size, CType.UINT);
        }
        if (expression instanceof AssignExpr assign) {
            LValue target = lvalue(assign.target());
            Value value;
            if (assign.op() == EQUALS)
                value = expression(assign.value());
            else
                value = binaryValues(read(target), assignmentOperator(assign.op()), expression(assign.value()));
            write(target, value);
            Value assigned = convert(value, target.type);
            return new Value(target.type, assigned.slot);
        }
        if (expression instanceof UpdateExpr update) {
            LValue target = lvalue(update.target());
            Value before = read(target);
            Value after = binaryValues(before, update.amount() > 0 ? PLUS : MINUS, integer(1, CType.INT));
            write(target, after);
            return update.prefix() ? convert(after, target.type) : before;
        }
        if (expression instanceof UnaryExpr unary) {
            if (unary.op() == AMP) {
                if (typeOf(unary.value()).kind == CType.Kind.FUNCTION)
                    return expression(unary.value());
                return pointer(lvalue(unary.value()));
            }
            if (unary.op() == STAR) {
                if (typeOf(unary).kind == CType.Kind.FUNCTION)
                    return expression(unary.value());
                return read(lvalue(unary));
            }
            Value value = expression(unary.value());
            if (unary.op() == BANG) {
                Value result = integer(0, CType.INT);
                String nonzero = fresh("not_end");
                test(value);
                emit("JNZ " + nonzero);
                emit("MVI A, 1");
                store(result.slot);
                mark(nonzero);
                return result;
            }
            value = convert(value, typeOf(unary));
            if (unary.op() == PLUS)
                return value;
            if (value.type.kind == CType.Kind.FLOAT)
                return floatingUnary(value, unary.op());
            Value result = temp(value.type);
            copy(result, value);
            if (unary.op() == MINUS)
                negate(result);
            else if (unary.op() == TILDE)
                for (int n = 0; n < result.type.size; n++) {
                    load(result.slot.at(n));
                    emit("CMA");
                    store(result.slot.at(n));
                }
            return result;
        }
        if (expression instanceof BinaryExpr binary) {
            if (binary.op() == AND_AND || binary.op() == OR_OR) {
                Value result = integer(binary.op() == OR_OR ? 1 : 0, CType.INT);
                String end = fresh("logical_end");
                test(expression(binary.left()));
                emit((binary.op() == AND_AND ? "JZ " : "JNZ ") + end);
                test(expression(binary.right()));
                emit((binary.op() == AND_AND ? "JZ " : "JNZ ") + end);
                emit("MVI A, " + (binary.op() == AND_AND ? 1 : 0));
                store(result.slot);
                mark(end);
                return result;
            }
            if (optimized
                    && (binary.op() == F_SLASH || binary.op() == PERCENT || binary.op() == STAR || binary.op() == PLUS
                            || binary.op() == MINUS || binary.op() == AMP || binary.op() == PIPE
                            || binary.op() == CARET)) {
                CType common = CType.common(typeOf(binary.left()), typeOf(binary.right()));
                ConstantEvaluator.Value constant = null;
                try {
                    constant = ConstantEvaluator.evaluate(binary.right(), this::typeOf).convert(common);
                } catch (IllegalArgumentException ignored) {
                }
                if (common.kind == CType.Kind.INTEGER && (common.size == 4 || common.size == 8) && constant != null) {
                    BigInteger number = constant.integer();
                    if (number.signum() == 0
                            && (binary.op() == PLUS || binary.op() == MINUS || binary.op() == PIPE
                                    || binary.op() == CARET))
                        return convert(expression(binary.left()), common);
                    if (binary.op() == AMP && number.signum() == 0) {
                        expression(binary.left());
                        return integer(BigInteger.ZERO, common);
                    }
                    if (binary.op() == PIPE && (number.equals(BigInteger.ONE.negate())
                            || number.equals(BigInteger.ONE.shiftLeft(common.size * 8).subtract(BigInteger.ONE)))) {
                        expression(binary.left());
                        return integer(number, common);
                    }
                    if (binary.op() == AMP
                            && (number.equals(BigInteger.valueOf(-1))
                                    || number.equals(
                                            BigInteger.ONE.shiftLeft(common.size * 8).subtract(BigInteger.ONE))))
                        return convert(expression(binary.left()), common);
                    if (binary.op() == CARET
                            && (number.equals(BigInteger.valueOf(-1))
                                    || number.equals(
                                            BigInteger.ONE.shiftLeft(common.size * 8).subtract(BigInteger.ONE)))) {
                        Value value = convert(expression(binary.left()), common);
                        Value result = temp(common);
                        byteKernel("NOT_COPY_BYTES", result, value);
                        return result;
                    }
                    if (binary.op() == STAR) {
                        Value value = convert(expression(binary.left()), common);
                        if (number.signum() == 0)
                            return integer(BigInteger.ZERO, common);
                        if (number.equals(BigInteger.ONE))
                            return value;
                        if (number.equals(BigInteger.ONE.negate())
                                || number.equals(BigInteger.ONE.shiftLeft(common.size * 8).subtract(BigInteger.ONE))) {
                            Value result = temp(common);
                            copy(result, value);
                            negate(result);
                            return result;
                        }
                        boolean powerOfTwo = number.signum() > 0 && number.bitCount() == 1;
                        int shift = number.getLowestSetBit();
                        if (powerOfTwo && (common.size == 8 || shift >= 8 && shift % 8 == 0))
                            return fixedShift(value, shift);
                        if (common.size == 4)
                            return multiplyConstant(value, number.longValue() & 0xffffffffL, false);
                        return new Value(common, multiplyConstantWide(value, number).slot);
                    }
                    if ((binary.op() == F_SLASH || binary.op() == PERCENT) && number.signum() != 0)
                        return divideConstant(
                                convert(expression(binary.left()), common), number, binary.op() == PERCENT);
                }
            }
            BigInteger constantShift = binary.op() == SHIFT_LEFT || binary.op() == SHIFT_RIGHT
                    ? optimized ? constantInteger(binary.right())
                            : binary.right() instanceof NumberExpr count ? count.value() : null
                    : null;
            if ((binary.op() == SHIFT_LEFT || binary.op() == SHIFT_RIGHT) && constantShift != null) {
                if (typeOf(binary.left()).kind != CType.Kind.INTEGER)
                    fail("Shift operands must be integers.");
                int distance = constantShift.intValueExact();
                if (distance < 0)
                    fail("Negative shift count.");
                Value left = convert(expression(binary.left()), CType.common(typeOf(binary.left()), CType.INT));
                if (optimized && distance == 0)
                    return left;
                return fixedShift(left, binary.op() == SHIFT_LEFT ? distance : -distance);
            }
            Value left = arithmeticOperand(binary.left(), !hasEffects(binary.right()));
            return binaryValues(left, binary.op(), arithmeticOperand(binary.right(), true));
        }
        if (expression instanceof ConditionalExpr conditional) {
            CType type = typeOf(conditional);
            Value result = temp(type);
            String no = fresh("conditional_no"), end = fresh("conditional_end");
            if (type.kind == CType.Kind.VOID) {
                test(expression(conditional.condition()));
                emit("JZ " + no);
                expression(conditional.yes());
                emit("JMP " + end);
                mark(no);
                expression(conditional.no());
                mark(end);
                return result;
            }
            test(expression(conditional.condition()));
            emit("JZ " + no);
            Value yes = expression(conditional.yes());
            requireImplicitConversion(yes.type, type);
            copy(result, convert(yes, type));
            emit("JMP " + end);
            mark(no);
            Value noValue = expression(conditional.no());
            requireImplicitConversion(noValue.type, type);
            copy(result, convert(noValue, type));
            mark(end);
            return result;
        }
        if (expression instanceof CallExpr call)
            return call(call);
        fail("Invalid expression.");
        return null;
    }

    private Value arithmeticOperand(Expr expression, boolean stable) {
        if (stable && expression instanceof VariableExpr variable && hasVariable(variable.name())) {
            Binding value = binding(variable.name());
            if (narrowedCounters.containsKey(value.slot()))
                return expression(expression);
            if (value.slot.label == null && value.type.scalar() && !value.type.volatileQualified)
                return new Value(value.type, value.slot);
        }
        return expression(expression);
    }
    private static Token.TokenType assignmentOperator(Token.TokenType op) {
        return switch (op) {
            case PLUS_EQUALS -> PLUS;
            case MINUS_EQUALS -> MINUS;
            case STAR_EQUALS -> STAR;
            case DIV_EQUALS -> F_SLASH;
            case MOD_EQUALS -> PERCENT;
            case AMP_EQUALS -> AMP;
            case PIPE_EQUALS -> PIPE;
            case CARET_EQUALS -> CARET;
            case SHIFT_LEFT_EQUALS -> SHIFT_LEFT;
            case SHIFT_RIGHT_EQUALS -> SHIFT_RIGHT;
            default -> throw new IllegalArgumentException("Invalid assignment operator.");
        };
    }
    private static boolean isComparison(Token.TokenType op) {
        return switch (op) {
            case LESS, LESS_EQUAL, GREATER, GREATER_EQUAL, EQUAL_EQUAL, NOT_EQUAL -> true;
            default -> false;
        };
    }
    private Value addPointer(Value pointer, Value count, boolean subtract, int scale) {
        if (scale <= 0)
            fail("Pointer arithmetic requires a complete object type.");
        if (count.type.kind != CType.Kind.INTEGER)
            fail("Array index must be an integer; the array element type does not change the index type. Use 9 rather "
                 + "than 9.0, or an explicit integer cast.");
        count = convert(count, CType.integer("uint64", 8, true));
        if (scale != 1) {
            pointerRegisters(count);
            emit("PUSH H");
            emit("POP D");
            emit("LXI H, 0");
            for (int bit = 31 - Integer.numberOfLeadingZeros(scale); bit >= 0; bit--) {
                if (bit != 31 - Integer.numberOfLeadingZeros(scale))
                    emit("DAD H");
                if ((scale & (1 << bit)) != 0)
                    emit("DAD D");
            }
            Value scaled = temp(count.type);
            registerPointer(scaled);
            count = scaled;
        }
        Value numeric = new Value(CType.integer("uint64", 8, true), pointer.slot);
        Value result = integerOperation(numeric, subtract ? MINUS : PLUS, count);
        return new Value(pointer.type, result.slot);
    }
    private Value binaryValues(Value left, Token.TokenType op, Value right) {
        if (!left.type.scalar() || !right.type.scalar())
            fail("Binary operators require scalar operands.");
        if (op == SHIFT_LEFT || op == SHIFT_RIGHT) {
            if (left.type.kind != CType.Kind.INTEGER || right.type.kind != CType.Kind.INTEGER)
                fail("Shift operands must be integers.");
            return shift(convert(left, CType.common(left.type, CType.INT)), op, convert(right, CType.UINT));
        }
        if ((op == PLUS || op == MINUS) && left.type.kind == CType.Kind.POINTER
                && right.type.kind != CType.Kind.POINTER)
            return addPointer(left, right, op == MINUS, left.type.element.size);
        if (op == PLUS && right.type.kind == CType.Kind.POINTER && left.type.kind != CType.Kind.POINTER)
            return addPointer(right, left, false, right.type.element.size);
        if (op == MINUS && left.type.kind == CType.Kind.POINTER && right.type.kind == CType.Kind.POINTER) {
            if (left.type.element.size <= 0 || !left.type.element.same(right.type.element))
                fail("Pointer subtraction requires compatible complete object types.");
            Value result = integerOperation(new Value(CType.LONG, left.slot), MINUS, new Value(CType.LONG, right.slot));
            return integerOperation(result, F_SLASH, integer(left.type.element.size, CType.LONG));
        }
        if ((left.type.kind == CType.Kind.POINTER || right.type.kind == CType.Kind.POINTER) && !isComparison(op))
            fail("Invalid pointer operator " + op);
        CType type = CType.common(left.type, right.type);
        left = convert(left, type);
        right = convert(right, type);
        if (type.kind == CType.Kind.FLOAT)
            return floatingBinary(left, op, right);
        return integerOperation(left, op, right);
    }
    private void test(Value value) {
        if (!value.type.scalar())
            fail("A condition requires a scalar value.");
        if (value.type.kind != CType.Kind.FLOAT && value.type.size > 1 && kernelValue(value)) {
            byteKernel("TEST_BYTES", value, null);
            return;
        }
        emit("MVI D, 0");
        for (int n = 0; n < value.type.size; n++) {
            load(value.slot.at(n));
            if (value.type.kind == CType.Kind.FLOAT && n == value.type.size - 1)
                emit("ANI 127");
            emit("ORA D");
            emit("MOV D, A");
        }
        emit("ORA A");
    }
    private void add(Value result, Value left, Value right, boolean subtract) {
        if (result.type.size > 1 && kernelValue(result) && kernelValue(left) && kernelValue(right)) {
            if (result.slot.equals(right.slot) && !result.slot.equals(left.slot)) {
                Value saved = temp(right.type);
                copy(saved, right);
                right = saved;
            }
            copy(result, left);
            byteKernel(subtract ? "SUB_BYTES" : "ADD_BYTES", result, right);
            return;
        }
        for (int n = 0; n < result.type.size; n++) {
            load(right.slot.at(n));
            emit("MOV D, A");
            load(left.slot.at(n));
            emit((subtract ? (n == 0 ? "SUB D" : "SBB D") : (n == 0 ? "ADD D" : "ADC D")));
            store(result.slot.at(n));
        }
    }
    private void negate(Value value) {
        if (value.type.size > 1 && kernelValue(value)) {
            byteKernel("NEG_BYTES", value, null);
            return;
        }
        for (int n = 0; n < value.type.size; n++) {
            load(value.slot.at(n));
            emit("CMA");
            emit(n == 0 ? "ADI 1" : "ACI 0");
            store(value.slot.at(n));
        }
    }
    private void shiftOne(Value value, boolean left, boolean signed) {
        if (value.type.size > 1 && kernelValue(value)) {
            byteKernel(left ? "SHL_BYTES" : signed ? "SAR_BYTES" : "SHR_BYTES", value, null);
            return;
        }
        if (signed&& !left) {
            load(value.slot.at(value.type.size - 1));
            emit("RLC 1");
        } else {
            emit("XRA A");
        }
        for (int i = 0; i < value.type.size; i++) {
            int n = left ? i : value.type.size - 1 - i;
            load(value.slot.at(n));
            emit(left ? "RAL 1" : "RAR 1");
            store(value.slot.at(n));
        }
    }
    private void unsignedBranch(Value left, Value right, String less, String equal, String greater) {
        if (wordValue(left) && wordValue(right)) {
            byteKernel("CMP_BYTES", left, right);
            nativeEmit("CPI 2");
            emit("JC " + less);
            emit("JZ " + equal);
            emit("JMP " + greater);
            return;
        }
        for (int n = left.type.size - 1; n >= 0; n--) {
            load(right.slot.at(n));
            emit("MOV D, A");
            load(left.slot.at(n));
            emit("CMP D");
            emit("JC " + less);
            emit("JNZ " + greater);
        }
        emit("JMP " + equal);
    }
    private Value comparison(Value left, Token.TokenType op, Value right) {
        if (left.type.size > 1 && kernelValue(left) && kernelValue(right)) {
            Value result = integer(0, CType.INT);
            byteKernel(left.type.unsigned ? "CMP_BYTES" : "SCMP_BYTES", left, right);
            int mask = switch (op) {
                case LESS -> 1;
                case EQUAL_EQUAL -> 2;
                case GREATER -> 4;
                case LESS_EQUAL -> 3;
                case GREATER_EQUAL -> 6;
                default -> 5;
            };
            nativeEmit("ANI " + mask);
            nativeEmit("SUI 1");
            nativeEmit("SBB A");
            nativeEmit("INR A");
            storeWord(result.slot, 4);
            return result;
        }
        Value result = integer(0, CType.INT);
        String less = fresh("cmp_less"), equal = fresh("cmp_equal"), greater = fresh("cmp_greater"),
               end = fresh("cmp_end");
        if (!left.type.unsigned) {
            load(left.slot.at(left.type.size - 1));
            emit("MOV D, A");
            load(right.slot.at(right.type.size - 1));
            emit("XRA D");
            emit("ANI 128");
            String same = fresh("cmp_sign");
            emit("JZ " + same);
            load(left.slot.at(left.type.size - 1));
            emit("ANI 128");
            emit("JNZ " + less);
            emit("JMP " + greater);
            mark(same);
        }
        unsignedBranch(left, right, less, equal, greater);
        mark(less);
        emit("MVI A, " + ((op == LESS || op == LESS_EQUAL || op == NOT_EQUAL) ? 1 : 0));
        emit("JMP " + end);
        mark(equal);
        emit("MVI A, " + ((op == EQUAL_EQUAL || op == LESS_EQUAL || op == GREATER_EQUAL) ? 1 : 0));
        emit("JMP " + end);
        mark(greater);
        emit("MVI A, " + ((op == GREATER || op == GREATER_EQUAL || op == NOT_EQUAL) ? 1 : 0));
        mark(end);
        store(result.slot);
        return result;
    }
    private Value integerOperation(Value left, Token.TokenType op, Value right) {
        if (left.type.size == 4 && !left.type.aggregate() && !isComparison(op)
                && (op == PLUS || op == MINUS || op == AMP || op == PIPE || op == CARET || op == STAR
                        || !inlineRuntime.endsWith("DIVMOD32"))) {
            Value result = temp(left.type);
            loadWord(left.slot, 4);
            emit("MOV D, A");
            loadWord(right.slot, 4);
            emit("MOV E, A");
            emit("PUSH B");
            emit("MOV B, D");
            emit("MOV C, E");
            if (op == PLUS || op == MINUS || op == AMP || op == PIPE || op == CARET) {
                nativeEmit("MOV A, B");
                nativeEmit(switch (op) {
                    case PLUS -> "ADD C";
                    case MINUS -> "SUB C";
                    case AMP -> "ANA C";
                    case PIPE -> "ORA C";
                    default -> "XRA C";
                });
            } else {
                String name =
                        op == STAR ? "mul32" : (left.type.unsigned ? "u" : "s") + (op == PERCENT ? "mod32" : "div32");
                runtime.require(name);
                nativeEmit("CALL " + runtimePrefix + name);
            }
            emit("POP B");
            storeWord(result.slot, 4);
            return result;
        }
        String helper = integerHelper(left.type, op);
        if (helper != null && !helper.equals(inlineRuntime)) {
            if (op == F_SLASH || op == PERCENT) {
                Value pair = runtimeCall(helper, CType.integer("divmod", left.type.size * 2, true), left, right);
                return new Value(left.type, pair.slot.at(op == PERCENT ? left.type.size : 0));
            }

            return runtimeCall(helper, isComparison(op) ? CType.INT : left.type, left, right);
        }
        if (isComparison(op))
            return comparison(left, op, right);
        Value result = temp(left.type);
        if (op == PLUS || op == MINUS) {
            add(result, left, right, op == MINUS);
            return result;
        }
        if (op == AMP || op == PIPE || op == CARET) {
            if (left.type.size > 1 && kernelValue(left) && kernelValue(right)) {
                copy(result, left);
                byteKernel(op == AMP ? "AND_BYTES" : op == PIPE ? "OR_BYTES" : "XOR_BYTES", result, right);
                return result;
            }
            for (int n = 0; n < left.type.size; n++) {
                load(right.slot.at(n));
                emit("MOV D, A");
                load(left.slot.at(n));
                emit(op == AMP ? "ANA D" : op == PIPE ? "ORA D" : "XRA D");
                store(result.slot.at(n));
            }
            return result;
        }
        if (op == STAR) {
            Value multiplicand = temp(left.type), multiplier = temp(right.type);
            copy(multiplicand, left);
            copy(multiplier, right);
            copy(result, integer(0, left.type));
            String loop = fresh("mul_loop"), skip = fresh("mul_skip"), done = fresh("mul_done");
            mark(loop);
            test(multiplier);
            emit("JZ " + done);
            load(multiplier.slot);
            emit("ANI 1");
            emit("JZ " + skip);
            add(result, result, multiplicand, false);
            mark(skip);
            shiftOne(multiplicand, true, false);
            shiftOne(multiplier, false, false);
            emit("JMP " + loop);
            mark(done);
            return result;
        }
        if (op == F_SLASH || op == PERCENT)
            return divide(left, right, op == PERCENT);
        fail("Unsupported integer operator " + op);
        return null;
    }

    /** Returns the requested half of a 32-bit value multiplied by an unsigned constant. */
    private Value multiplyConstant(Value value, long factor, boolean high) {
        if (factor == 0) return integer(BigInteger.ZERO, value.type);
        Value result = temp(value.type);
        loadWord(value.slot, 4);
        emitShiftAddMultiply(factor);
        emit("MOV A, " + (high ? "H" : "L"));
        storeWord(result.slot, 4);
        return result;
    }
    /** Multiplies the zero-extended low 32 bits of A by a nonzero constant into HL with shift-and-add steps. */
    private void emitShiftAddMultiply(long factor) {
        emit("MVI D, 0");
        emit("MOV E, A");
        if (factor > 1) {
            emit("MOV H, D");
            emit("MOV L, E");
        } else {
            emit("LXI H, 0");
        }
        int top = 63 - Long.numberOfLeadingZeros(factor);
        for (int bit = top; bit >= 0; bit--) {
            if (bit != top)
                emit("DAD H");
            if ((factor & (1L << bit)) != 0 && !(factor > 1 && bit == top))
                emit("DAD D");
        }
    }

    private Value multiplyConstantFull(Value value, long factor) {
        Value result = temp(CType.integer("uint64", 8, true));
        loadWord(value.slot, 4);
        emitShiftAddMultiply(factor);
        registerPointer(result);
        return result;
    }

    private Value multiplyConstantWide(Value value, BigInteger factor) {
        Value result = integer(0, CType.integer("uint128", 16, true));
        long low = factor.and(BigInteger.valueOf(0xffffffffL)).longValue(),
             high = factor.shiftRight(32).and(BigInteger.valueOf(0xffffffffL)).longValue();
        for (int left = 0; left < 2; left++)
            for (int right = 0; right < 2; right++) {
                long limb = right == 0 ? low : high;
                if (limb == 0)
                    continue;
                Value product = multiplyConstantFull(new Value(CType.UINT, value.slot.at(left * 4)), limb);
                int offset = (left + right) * 4;
                CType tail = CType.integer("product tail", 16 - offset, true);
                Value destination = new Value(tail, result.slot.at(offset));
                copy(destination, integerOperation(destination, PLUS, convert(product, tail)));
            }
        return result;
    }

    private Value divideConstant(Value numerator, BigInteger divisor, boolean remainder) {
        CType resultType = numerator.type;
        if (divisor.abs().equals(BigInteger.ONE)) {
            if (remainder)
                return integer(BigInteger.ZERO, resultType);
            if (resultType.unsigned || divisor.signum() > 0)
                return numerator;
            Value negated = temp(resultType);
            copy(negated, numerator);
            negate(negated);
            return negated;
        }
        CType unsigned = CType.integer("unsigned magnitude", resultType.size, true);
        Value magnitude = temp(unsigned);
        copy(magnitude, new Value(unsigned, numerator.slot));
        Value negative = null;
        if (!resultType.unsigned) {
            negative = temp(CType.UINT);
            loadWord(magnitude.slot.at(resultType.size - 4), 4);
            String positive = fresh("constant_positive"), done = fresh("constant_magnitude");
            emit("ORA A");
            emit("JP " + positive);
            negate(magnitude);
            nativeEmit("MVI A, 1");
            emit("JMP " + done);
            mark(positive);
            nativeEmit("MVI A, 0");
            mark(done);
            storeWord(negative.slot, 4);
        }
        BigInteger absolute = divisor.abs();
        long d = absolute.longValue();
        Value quotient, rest;
        if (absolute.bitCount() == 1) {
            quotient = fixedShift(magnitude, -absolute.getLowestSetBit());
            rest = integerOperation(magnitude, AMP, integer(absolute.subtract(BigInteger.ONE), unsigned));
        } else {
            BigInteger magic = BigInteger.ONE.shiftLeft(resultType.size * 8).divide(absolute);
            emit("; reciprocal division by " + absolute + ", multiplier 0x" + magic.toString(16));
            quotient = resultType.size == 4 ? multiplyConstant(magnitude, magic.longValue(), true)
                                            : new Value(unsigned, multiplyConstantWide(magnitude, magic).slot.at(8));
            Value product = resultType.size == 4 ? multiplyConstant(quotient, d, false)
                                                 : new Value(unsigned, multiplyConstantWide(quotient, absolute).slot);
            rest = integerOperation(magnitude, MINUS, product);
            String corrected = fresh("constant_corrected");
            if (resultType.size == 4) {
                loadWord(rest.slot, 4);
                nativeEmit("CPI " + d);
                emit("JC " + corrected);
                nativeEmit("SUI " + d);
                storeWord(rest.slot, 4);
                loadWord(quotient.slot, 4);
                nativeEmit("INR A");
                storeWord(quotient.slot, 4);
            } else {
                Value denominator = integer(absolute, unsigned);
                test(comparison(rest, LESS, denominator));
                emit("JNZ " + corrected);
                copy(rest, integerOperation(rest, MINUS, denominator));
                copy(quotient, integerOperation(quotient, PLUS, integer(1, unsigned)));
            }
            mark(corrected);
        }
        Value result = remainder ? rest : quotient;
        if (negative != null) {
            String positive = fresh("constant_result_positive");
            loadWord(negative.slot, 4);
            nativeEmit("XRI " + (!remainder && divisor.signum() < 0 ? 1 : 0));
            emit("JZ " + positive);
            negate(result);
            mark(positive);
        }
        return new Value(resultType, result.slot);
    }
    private Value divide(Value numerator, Value denominator, boolean remainder) {
        CType type = numerator.type;
        Value dividend = temp(type), divisor = temp(type), rest = integer(0, type), sign = temp(CType.CHAR);
        copy(dividend, numerator);
        copy(divisor, denominator);
        emit("MVI A, 0");
        store(sign.slot);
        if (!type.unsigned) {
            String positive = fresh("div_positive");
            load(dividend.slot.at(type.size - 1));
            emit("ANI 128");
            emit("JZ " + positive);
            negate(dividend);
            emit("MVI A, 3");
            store(sign.slot);
            mark(positive);
            positive = fresh("divisor_positive");
            load(divisor.slot.at(type.size - 1));
            emit("ANI 128");
            emit("JZ " + positive);
            negate(divisor);
            load(sign.slot);
            emit("XRI 1");
            store(sign.slot);
            mark(positive);
        }
        String nonzero = fresh("div_nonzero");
        test(divisor);
        emit("JNZ " + nonzero);
        emit("STOP");
        mark(nonzero);
        Value count = integer(type.size * 8L, CType.UINT), one = integer(1, CType.UINT);
        String loop = fresh("div_loop"), subtract = fresh("div_subtract"), skip = fresh("div_skip"),
               done = fresh("div_done");
        mark(loop);
        shiftOne(dividend, true, false);
        if (wordValue(rest))
            byteKernel("RCL_BYTES", rest, null);
        else
            for (int n = 0; n < type.size; n++) {
                load(rest.slot.at(n));
                emit("RAL 1");
                store(rest.slot.at(n));
            }
        emit("JC " + subtract);
        unsignedBranch(rest, divisor, skip, subtract, subtract);
        mark(subtract);
        add(rest, rest, divisor, true);
        load(dividend.slot);
        emit("ORI 1");
        store(dividend.slot);
        mark(skip);
        add(count, count, one, true);
        test(count);
        emit("JNZ " + loop);
        Value result = remainder ? rest : dividend;
        if (!type.unsigned) {
            load(sign.slot);
            emit(remainder ? "ANI 2" : "ANI 1");
            emit("JZ " + done);
            negate(result);
        }
        mark(done);
        if (inlineRuntime.equals((type.unsigned ? "UDIVMOD" : "SDIVMOD") + type.size * 8)) {
            if (!type.unsigned) {
                String positive = fresh("remainder_positive");
                load(sign.slot);
                emit("ANI 2");
                emit("JZ " + positive);
                negate(rest);
                mark(positive);
            }
            Value pair = temp(CType.integer("divmod", type.size * 2, true));
            copy(new Value(type, pair.slot), dividend);
            copy(new Value(type, pair.slot.at(type.size)), rest);
            return pair;
        }
        return result;
    }
    private Value shift(Value left, Token.TokenType op, Value count) {
        String helper = (op == SHIFT_LEFT ? "SHL" : left.type.unsigned ? "SHR" : "SAR") + left.type.size * 8;
        if (!helper.equals(inlineRuntime))
            return runtimeCall(helper, left.type, left, convert(count, CType.UINT));
        Value result = temp(left.type);
        copy(result, left);
        count = convert(count, CType.UINT);
        Value work = temp(CType.UINT);
        copy(work, count);
        Value one = integer(1, CType.UINT);
        String loop = fresh("shift_loop"), done = fresh("shift_done");
        mark(loop);
        test(work);
        emit("JZ " + done);
        shiftOne(result, op == SHIFT_LEFT, !left.type.unsigned);
        add(work, work, one, true);
        emit("JMP " + loop);
        mark(done);
        return result;
    }

    private boolean largeReturn(CType type) {
        return type.aggregate() || type.size > 8;
    }
    private int argumentSize(CType type) {
        return CType.align(Math.max(8, type.size), 8);
    }
    private void pushValue(Value value, int size) {
        for (int n = size - 8; n >= 0; n -= 8) {
            int high = Math.max(0, Math.min(4, value.type.size - n - 4));
            if (high > 0)
                loadWord(value.slot.at(n + 4), high);
            else
                emit("MVI A, 0");
            emit("MOV D, A");
            int low = Math.max(0, Math.min(4, value.type.size - n));
            if (low > 0)
                loadWord(value.slot.at(n), low);
            else
                emit("MVI A, 0");
            emit("MOV E, A");
            emit("PUSH D");
        }
    }

    private boolean hasEffects(Expr expression) {
        if (expression instanceof VariableExpr variable && hasVariable(variable.name()))
            return binding(variable.name()).type.volatileQualified;
        if (expression instanceof UnaryExpr unary && unary.op() == STAR && typeOf(expression).volatileQualified)
            return true;
        if ((expression instanceof MemberExpr || expression instanceof IndexExpr)
                && typeOf(expression).volatileQualified)
            return true;
        if (expression instanceof CallExpr || expression instanceof AssignExpr || expression instanceof UpdateExpr)
            return true;
        if (expression instanceof BinaryExpr binary)
            return hasEffects(binary.left()) || hasEffects(binary.right());
        if (expression instanceof UnaryExpr unary)
            return hasEffects(unary.value());
        if (expression instanceof CastExpr cast)
            return hasEffects(cast.value());
        if (expression instanceof CommaExpr comma)
            return hasEffects(comma.left()) || hasEffects(comma.right());
        if (expression instanceof ConditionalExpr conditional)
            return hasEffects(conditional.condition()) || hasEffects(conditional.yes()) || hasEffects(conditional.no());
        if (expression instanceof IndexExpr index)
            return hasEffects(index.base()) || hasEffects(index.index());
        if (expression instanceof MemberExpr member)
            return hasEffects(member.base());
        return false;
    }
    private Value call(CallExpr call) {
        return call(call, true);
    }
    private Value call(CallExpr call, boolean used) {
        Function target = calledFunction(call);
        boolean direct = directCall(call);
        int fixed = target.parameters().size(), provided = call.arguments().size();
        if (target.variadic() ? provided < fixed : provided != fixed) {
            String callableName = call.callee() instanceof VariableExpr variable ? variable.name() : target.name();
            String callable = direct ? "Function " + callableName : "Function pointer " + callableName;
            String requirement = target.variadic() ? "requires at least " : "expects ";
            String requiredArguments = fixed + (fixed == 1 ? " argument" : " arguments");
            String suppliedArguments = provided + (provided == 1 ? " argument" : " arguments");
            fail(callable + " " + requirement + requiredArguments
                    + ", but this call provides " + suppliedArguments + ".\nExpected signature: " + signature(target, callableName, !direct) + ".");
        }
        Value result = used || largeReturn(target.type())
                ? temp(target.type().kind == CType.Kind.VOID ? CType.INT : target.type())
                : null;
        Value indirect = direct ? null : expression(call.callee());
        List<Value> arguments = new ArrayList<>();
        Map<Integer, String> stringArguments = new HashMap<>();

        for (int n = 0; n < provided; n++) {
            Expr argument = call.arguments().get(n);
            CType sourceType = typeOf(argument).decay();
            CType type = n < fixed                        ? target.parameters().get(n).type()
                    : sourceType.kind == CType.Kind.FLOAT ? CType.DOUBLE
                                                          : CType.common(sourceType, CType.INT);
            if (argument instanceof StringExpr string && type.kind == CType.Kind.POINTER) {
                stringArguments.put(n, stringConstant(string).label());
                arguments.add(null);
            } else if (argument instanceof VariableExpr variable && hasVariable(variable.name())
                    && binding(variable.name()).type.kind != CType.Kind.ARRAY
                    && !binding(variable.name()).type.volatileQualified && type.same(sourceType)
                    && !narrowedCounters.containsKey(binding(variable.name()).slot)
                    && call.arguments().subList(n + 1, provided).stream().noneMatch(this::hasEffects)) {
                Binding binding = binding(variable.name());
                diagnosticToken = positions.getOrDefault(argument, diagnosticToken);
                requireImplicitConversion(sourceType, type);
                arguments.add(new Value(type, binding.slot));
            } else
                arguments.add(implicitConvert(expression(argument), type));
        }
        int bytes = 0;
        for (int n = provided - 1; n >= 0; n--) {
            if (stringArguments.containsKey(n)) {
                String symbol = stringArguments.get(n);
                emit("LXI D, " + symbol);
                emit("PUSH D");
                bytes += 8;
            } else {
                Value value = arguments.get(n);
                int size = argumentSize(value.type);
                pushValue(value, size);
                bytes += size;
            }
        }
        if (largeReturn(target.type())) {
            pushValue(addressValue(result.slot, target.type()), 8);
            bytes += 8;
        }
        if (indirect == null) {
            boolean integerPrintf = target.name().equals("printf") && target.body() == null && provided > 0
                    && call.arguments().get(0) instanceof StringExpr format && !format.value().matches("(?s).*[fF].*");
            if (integerPrintf)
                declarations.append("extern PRINTF_INTEGER\n");
            emit("CALL " + (integerPrintf ? "PRINTF_INTEGER" : functionLabels.get(target.name())));
        } else {
            String thunk = fresh("indirect_call"), resume = fresh("indirect_resume");
            emit("CALL " + thunk);
            emit("JMP " + resume);
            mark(thunk);
            pointerRegisters(indirect);
            emit("PCHL");
            mark(resume);
        }
        discardArguments(bytes);
        emit("MOV A, L");
        if (used && !largeReturn(target.type()))
            registerPointer(result);
        return !used ? null : target.type().kind == CType.Kind.VOID ? new Value(CType.VOID, result.slot) : result;
    }
    private void emitFunction(Function fn) {
        checkCancelled();
        visibleFunctions = declaredAtDefinition.getOrDefault(fn.name(), Set.of());
        diagnosticToken = positions.getOrDefault(fn, diagnosticToken);
        if (fn.type().kind != CType.Kind.VOID && !returnsValueOnAllPaths(fn.body()))
            fail("Function '" + fn.name() + "' returns " + fn.type()
                    + (" but can reach its end without returning a value.\nAdd an explicit return on every reachable "
                       + "path, including main."));
        function = fn;
        next = peak = 0;
        scopes.clear();
        scopes.push(new LinkedHashMap<>());
        code = new StringBuilder();
        exit = fresh("exit");
        breakLabel = continueLabel = null;
        int offset = largeReturn(fn.type()) ? 8 : 0;
        for (DeclStmt parameter : fn.parameters()) {
            checkCancelled();
            if (scopes.peek().putIfAbsent(parameter.name(), new Binding(parameter.type(), new Slot(null, offset)))
                    != null)
                fail("Duplicate parameter " + parameter.name());
            offset += argumentSize(parameter.type());
        }
        statement(fn.body());
        mark(exit);

        emit("XCHG");
        emit("LXI H, -16");
        emit("DAD B");
        emit("SPHL");
        emit("XCHG");
        emit("POP B");
        emit("RET");
        text.append(functionLabels.get(fn.name()))
                .append(":\n    PUSH B\n    LXI H, 16\n    DAD SP\n    MOV B, H\n    MOV C, L\n");
        if (peak > 0)
            text.append("    LXI H, ").append(-peak).append("\n    DAD SP\n    SPHL\n");
        text.append(code);
    }

    private void discardArguments(int bytes) {
        if (bytes == 0)
            return;
        emit("XCHG");
        emit("LXI H, " + bytes);
        emit("DAD SP");
        emit("SPHL");
        emit("XCHG");
    }

    private boolean returnsValueOnAllPaths(Stmt stmt) {
        return (flow(stmt) & FLOW_NEXT) == 0;
    }
    private static final int FLOW_NEXT = 1, FLOW_RETURN = 2, FLOW_BREAK = 4, FLOW_CONTINUE = 8;

    private int flow(Stmt stmt) {
        checkCancelled();
        if (stmt instanceof ReturnStmt)
            return FLOW_RETURN;
        if (stmt instanceof BreakStmt)
            return FLOW_BREAK;
        if (stmt instanceof ContinueStmt)
            return FLOW_CONTINUE;
        if (stmt instanceof BlockStmt block) {
            int outcomes = FLOW_NEXT;
            for (Stmt child : block.statements())
                if ((outcomes & FLOW_NEXT) != 0)
                    outcomes = (outcomes & ~FLOW_NEXT) | flow(child);
            return outcomes;
        }
        if (stmt instanceof IfStmt branch) {
            int yes = flow(branch.yes()), no = branch.no() == null ? FLOW_NEXT : flow(branch.no());
            return alwaysTrue(branch.condition()) ? yes : alwaysFalse(branch.condition()) ? no : yes | no;
        }
        if (stmt instanceof WhileStmt loop)
            return loopFlow(flow(loop.body()), alwaysTrue(loop.condition()), false);
        if (stmt instanceof ForStmt loop)
            return loopFlow(flow(loop.body()), loop.condition() == null || alwaysTrue(loop.condition()), false);
        if (stmt instanceof DoWhileStmt loop)
            return loopFlow(flow(loop.body()), alwaysTrue(loop.condition()), true);
        if (stmt instanceof SwitchStmt selection) {
            int following = FLOW_NEXT, outcomes = hasDefaultCase(selection.cases()) ? 0 : FLOW_NEXT;
            for (int n = selection.cases().size() - 1; n >= 0; n--) {
                int body = flow(new BlockStmt(selection.cases().get(n).statements()));
                following = (body & ~FLOW_NEXT) | ((body & FLOW_NEXT) != 0 ? following : 0);
                outcomes |= following;
            }
            return (outcomes & ~FLOW_BREAK) | ((outcomes & FLOW_BREAK) != 0 ? FLOW_NEXT : 0);
        }
        return FLOW_NEXT;
    }
    private boolean hasDefaultCase(List<SwitchCase> cases) {
        for (SwitchCase item : cases) {
            checkCancelled();
            if (item.value() == null) return true;
        }
        return false;
    }
    private int loopFlow(int body, boolean infinite, boolean executesOnce) {
        return (body & FLOW_RETURN)
                | ((body & FLOW_BREAK) != 0 || !infinite && (!executesOnce || (body & (FLOW_NEXT | FLOW_CONTINUE)) != 0)
                                ? FLOW_NEXT
                                : 0);
    }
    private boolean alwaysTrue(Expr expression) {
        try {
            return ConstantEvaluator.evaluate(expression, this::typeOf).truth();
        } catch (IllegalArgumentException ignored) {
            return false;
        }
    }
    private boolean alwaysFalse(Expr expression) {
        try {
            return !ConstantEvaluator.evaluate(expression, this::typeOf).truth();
        } catch (IllegalArgumentException ignored) {
            return false;
        }
    }
    private void emitConstantReturn(BigInteger value) {
        if (function.type().size <= 8 && !largeReturn(function.type())) {
            CType type = function.type();
            if (type.isBoolean())
                value = value.signum() == 0 ? BigInteger.ZERO : BigInteger.ONE;
            if (type.kind == CType.Kind.INTEGER) {
                BigInteger modulus = BigInteger.ONE.shiftLeft(type.size * 8);
                value = value.mod(modulus);
                if (!type.unsigned&& value.testBit(type.size * 8 - 1))
                    value = value.subtract(modulus);
            }
            emit("LXI H, 0x" + value.and(BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE)).toString(16));
            emit("MOV A, L");
            emit("JMP " + exit);
        } else
            emitReturn(integer(value, function.type()));
    }

    private void emitReturn(Value value) {
        CType type = function.type();
        if (type.kind == CType.Kind.VOID) {
            emit("MVI A, 0");
            emit("LXI H, 0");
            emit("LXI D, 0");
            emit("JMP " + exit);
            return;
        }
        value = implicitConvert(value, type);
        if (largeReturn(type)) {
            Value pointer = new Value(CType.pointer(type), new Slot(null, 0));
            write(new LValue(type, null, pointer), value);
            pointerRegisters(pointer);
            emit("PUSH H");
            load(value.slot);
            emit("POP H");
            emit("JMP " + exit);
            return;
        }
        Value result = type.kind == CType.Kind.FLOAT
                ? new Value(CType.integer("floating bits", type.size, true), value.slot)
                : convert(value, CType.integer("return bits", 8, value.type.unsigned));
        pointerRegisters(result);
        emit("MOV A, L");
        emit("JMP " + exit);
    }
    private void statement(Stmt statement) {
        checkCancelled();
        diagnosticToken = positions.getOrDefault(statement, diagnosticToken);
        int scratch = next;
        if (statement instanceof EmptyStmt)
            return;
        if (statement instanceof BlockStmt block) {
            scopes.push(new LinkedHashMap<>());
            int saved = next;
            for (Stmt child : block.statements()) statement(child);
            scopes.pop();
            next = saved;
            return;
        }
        if (statement instanceof DeclGroup group) {
            for (DeclStmt declaration : group.declarations()) statement(declaration);
            return;
        }
        if (statement instanceof DeclStmt declaration) {
            Map<String, Binding> scope = scopes.peek();
            if (scope.containsKey(declaration.name()))
                fail("Duplicate variable " + declaration.name());
            Slot slot;
            if (declaration.storage() == Storage.STATIC) {
                String symbol = fresh("static_" + declaration.name());
                staticData(symbol, declaration.type(), declaration.initializer());
                slot = new Slot(symbol, 0);
            } else if (declaration.storage() == Storage.EXTERN) {
                String symbol = symbol("G", declaration.name());
                declarations.append("extern ").append(symbol).append('\n');
                slot = new Slot(symbol, 0);
            } else
                slot = allocate(declaration.type().size);
            scope.put(declaration.name(), new Binding(declaration.type(), slot));
            int permanent = next;
            if (declaration.initializer() != null && declaration.storage() == Storage.AUTO)
                initialize(new LValue(declaration.type(), slot, null), declaration.initializer());
            next = permanent;
            return;
        }
        if (statement instanceof ExprStmt expression) {
            if (expression.value() instanceof CallExpr call)
                call(call, false);
            else if (optimized)
                updateDiscarded(expression.value());
            else
                expression(expression.value());
        } else if (statement instanceof AsmStmt assembly) {
            inlineAssembly(assembly);
        } else if (statement instanceof ReturnStmt returned) {
            if (returned.value() == null) {
                if (function.type().kind != CType.Kind.VOID)
                    fail("Expected return value of type " + function.type() + "; presented return without a value.");
                emit("JMP " + exit);
            } else {
                if (function.type().kind == CType.Kind.VOID)
                    fail("Expected return without a value in void function; presented a value.");
                if (returned.value() instanceof NumberExpr number && function.type().kind == CType.Kind.INTEGER)
                    emitConstantReturn(number.value());
                else
                    emitReturn(expression(returned.value()));
            }
        } else if (statement instanceof IfStmt branch) {
            String no = fresh("else"), end = fresh("endif");
            test(expression(branch.condition()));
            emit("JZ " + no);
            statement(branch.yes());
            emit("JMP " + end);
            mark(no);
            if (branch.no() != null)
                statement(branch.no());
            mark(end);
        } else if (statement instanceof WhileStmt loop) {
            String test = fresh("while"), end = fresh("while_end");
            String oldBreak = breakLabel, oldContinue = continueLabel;
            breakLabel = end;
            continueLabel = test;
            mark(test);
            test(expression(loop.condition()));
            emit("JZ " + end);
            statement(loop.body());
            emit("JMP " + test);
            mark(end);
            breakLabel = oldBreak;
            continueLabel = oldContinue;
        } else if (statement instanceof DoWhileStmt loop) {
            String body = fresh("do"), test = fresh("do_test"), end = fresh("do_end");
            String oldBreak = breakLabel, oldContinue = continueLabel;
            breakLabel = end;
            continueLabel = test;
            mark(body);
            statement(loop.body());
            mark(test);
            test(expression(loop.condition()));
            emit("JNZ " + body);
            mark(end);
            breakLabel = oldBreak;
            continueLabel = oldContinue;
        } else if (statement instanceof ForStmt loop) {
            NarrowedLoop narrowed = narrowedLoop(loop);
            if (narrowed != null)
                emitNarrowedLoop(loop, narrowed);
            else {
                scopes.push(new LinkedHashMap<>());
                if (loop.init() != null)
                    statement(loop.init());
                String test = fresh("for"), step = fresh("for_step"), end = fresh("for_end");
                String oldBreak = breakLabel, oldContinue = continueLabel;
                breakLabel = end;
                continueLabel = step;
                mark(test);
                if (loop.condition() != null) {
                    test(expression(loop.condition()));
                    emit("JZ " + end);
                }
                statement(loop.body());
                mark(step);
                if (loop.update() != null)
                    updateDiscarded(loop.update());
                emit("JMP " + test);
                mark(end);
                breakLabel = oldBreak;
                continueLabel = oldContinue;
                scopes.pop();
            }
        } else if (statement instanceof SwitchStmt switched) {
            Value selector = expression(switched.value());
            if (selector.type.kind != CType.Kind.INTEGER)
                fail("switch expression must have integer type.");
            selector = convert(selector, CType.common(selector.type, CType.INT));
            String end = fresh("switch_end"), defaultLabel = end;
            List<String> labels = new ArrayList<>();
            Set<BigInteger> values = new HashSet<>();
            for (SwitchCase item : switched.cases()) {
                String label = fresh("case");
                labels.add(label);
                if (item.value() == null) {
                    if (!defaultLabel.equals(end))
                        fail("Duplicate default label.");
                    defaultLabel = label;
                } else if (!values.add(item.value()))
                    fail("Duplicate case label.");
            }
            for (int n = 0; n < switched.cases().size(); n++) {
                SwitchCase item = switched.cases().get(n);
                if (item.value() == null)
                    continue;
                Value result = comparison(selector, EQUAL_EQUAL, integer(item.value(), selector.type));
                test(result);
                emit("JNZ " + labels.get(n));
            }
            emit("JMP " + defaultLabel);
            String oldBreak = breakLabel;
            breakLabel = end;
            scopes.push(new LinkedHashMap<>());
            for (int n = 0; n < switched.cases().size(); n++) {
                mark(labels.get(n));
                for (Stmt child : switched.cases().get(n).statements()) statement(child);
            }
            scopes.pop();
            breakLabel = oldBreak;
            mark(end);
        } else if (statement instanceof BreakStmt) {
            if (breakLabel == null)
                fail("break outside a loop or switch.");
            emit("JMP " + breakLabel);
        } else if (statement instanceof ContinueStmt) {
            if (continueLabel == null)
                fail("continue outside a loop.");
            emit("JMP " + continueLabel);
        }
        next = scratch;
    }
    /**
     * Proves that a simple signed-int induction loop fits an unsigned byte or word.
     * The body must not assign, shadow, or expose the induction variable's address;
     * each read is reconstructed from the narrow counter and a constant bias. Counts
     * up to 255/256 use one byte, counts up to 65,535/65,536 use two bytes, and all
     * unproven or larger loops retain the original 32-bit representation.
     *
     * @param loop source loop to analyze without emitting code
     * @return a safe narrowed representation, or {@code null} to use normal lowering
     */
    private NarrowedLoop narrowedLoop(ForStmt loop) {
        checkCancelled();
        if (!optimized) return null;

        DeclStmt declaration = loop.init() instanceof DeclStmt single ? single
                : loop.init() instanceof DeclGroup group && group.declarations().size() == 1
                        ? group.declarations().get(0)
                        : null;
        if (!isEligibleNarrowedLoop(loop, declaration)) return null;

        try {
            CType type = declaration.type();
            Expr boundExpression = ((BinaryExpr) loop.condition()).right();
            CType boundType = typeOf(boundExpression);
            if (boundType.kind != CType.Kind.INTEGER || !CType.common(type, boundType).same(type)) return null;

            BigInteger start = ConstantEvaluator.evaluate(declaration.initializer(), this::typeOf)
                    .convert(type).integer();
            BigInteger bound = ConstantEvaluator.evaluate(boundExpression, this::typeOf).convert(type).integer();
            BigInteger minimum = BigInteger.ONE.shiftLeft(31).negate();
            BigInteger maximum = BigInteger.ONE.shiftLeft(31).subtract(BigInteger.ONE);
            boolean inclusive = ((BinaryExpr) loop.condition()).op() == LESS_EQUAL;
            if (inclusive && (start.compareTo(bound) > 0 || bound.compareTo(maximum) >= 0)) return null;
            if (!inclusive && start.compareTo(bound) >= 0) return null;

            BigInteger count = bound.subtract(start);
            if (inclusive) count = count.add(BigInteger.ONE);
            if (start.compareTo(minimum) < 0 || bound.compareTo(maximum) > 0 || count.signum() <= 0) return null;

            int width;
            boolean descending;
            if (count.compareTo(BigInteger.valueOf(255)) <= 0) {
                width = 1;
                descending = false;
            } else if (count.compareTo(BigInteger.valueOf(256)) <= 0) {
                width = 1;
                descending = true;
            } else if (count.compareTo(BigInteger.valueOf(65_535)) <= 0) {
                width = 2;
                descending = false;
            } else if (count.compareTo(BigInteger.valueOf(65_536)) <= 0) {
                width = 2;
                descending = true;
            } else {
                return null;
            }

            CType counterType = CType.integer(width == 1 ? "uint8" : "uint16", width, true);
            BigInteger bias = descending ? start.add(count).subtract(BigInteger.ONE) : start;
            return new NarrowedLoop(declaration, counterType, count, descending, bias);
        } catch (IllegalArgumentException | ArithmeticException ignored) {
            return null;
        }
    }

    /** Checks the loop's syntax and body effects before its source counter is narrowed. */
    private boolean isEligibleNarrowedLoop(ForStmt loop, DeclStmt declaration) {
        if (declaration == null || declaration.storage() != Storage.AUTO || declaration.initializer() == null) return false;
        CType type = declaration.type();
        if (type.kind != CType.Kind.INTEGER || type.size != 4 || type.unsigned || type.volatileQualified || type.isBoolean())
            return false;
        if (!(loop.condition() instanceof BinaryExpr condition)
                || !(condition.left() instanceof VariableExpr counter)
                || !counter.name().equals(declaration.name())
                || condition.op() != LESS && condition.op() != LESS_EQUAL) return false;
        if (!(loop.update() instanceof UpdateExpr update) || update.amount() != 1
                || !(update.target() instanceof VariableExpr updated) || !updated.name().equals(declaration.name()))
            return false;
        return narrowLoopBodySafe(loop.body(), declaration.name())
                && isConstantExpression(declaration.initializer())
                && isConstantExpression(condition.right());
    }

    /**
     * Emits an equivalent loop over the narrow counter while keeping the source type
     * in the symbol binding so reads reconstruct the original signed-int value.
     * The descending form starts at count minus one and tests for zero before its
     * decrement, avoiding wrap after the final inclusive iteration. Break and
     * continue target this loop's own exit and step labels, then prior targets return.
     */
    private void emitNarrowedLoop(ForStmt loop, NarrowedLoop narrowed) {
        scopes.push(new LinkedHashMap<>());
        Slot slot = allocate(narrowed.counterType().size);
        scopes.peek().put(narrowed.declaration().name(), new Binding(narrowed.declaration().type(), slot));
        narrowedCounters.put(slot,
                new NarrowedCounter(narrowed.counterType(), narrowed.descending(), narrowed.bias()));

        BigInteger initialValue = narrowed.descending() ? narrowed.count().subtract(BigInteger.ONE) : BigInteger.ZERO;
        write(new LValue(narrowed.counterType(), slot, null), integer(initialValue, narrowed.counterType()));
        String testLabel = fresh("for_narrow_test");
        String bodyLabel = fresh("for_narrow_body");
        String stepLabel = fresh("for_narrow_step");
        String endLabel = fresh("for_narrow_end");
        String previousBreakLabel = breakLabel;
        String previousContinueLabel = continueLabel;
        breakLabel = endLabel;
        continueLabel = stepLabel;

        if (narrowed.descending()) {
            mark(bodyLabel);
            statement(loop.body());
            mark(stepLabel);
            test(read(new LValue(narrowed.counterType(), slot, null)));
            emit("JZ " + endLabel);
            decrementLocal(slot, narrowed.counterType().size);
            emit("JMP " + bodyLabel);
        } else {
            mark(testLabel);
            Value current = read(new LValue(narrowed.counterType(), slot, null));
            test(comparison(current, LESS, integer(narrowed.count(), narrowed.counterType())));
            emit("JZ " + endLabel);
            statement(loop.body());
            mark(stepLabel);
            incrementLocal(slot, narrowed.counterType().size);
            emit("JMP " + testLabel);
        }

        mark(endLabel);
        breakLabel = previousBreakLabel;
        continueLabel = previousContinueLabel;
        narrowedCounters.remove(slot);
        scopes.pop();
    }

    /** Rejects any body statement that can change, shadow, or expose the counter. */
    private boolean narrowLoopBodySafe(Stmt statement, String name) {
        checkCancelled();
        if (statement instanceof BlockStmt block)
            return block.statements().stream().allMatch(child -> narrowLoopBodySafe(child, name));
        if (statement instanceof DeclStmt declaration)
            return !declaration.name().equals(name)
                    && (declaration.initializer() == null || narrowLoopExpressionSafe(declaration.initializer(), name));
        if (statement instanceof DeclGroup group)
            return group.declarations().stream().allMatch(declaration -> narrowLoopBodySafe(declaration, name));
        if (statement instanceof ExprStmt expression)
            return narrowLoopExpressionSafe(expression.value(), name);
        if (statement instanceof ReturnStmt returned)
            return returned.value() == null || narrowLoopExpressionSafe(returned.value(), name);
        if (statement instanceof IfStmt branch)
            return narrowLoopExpressionSafe(branch.condition(), name) && narrowLoopBodySafe(branch.yes(), name)
                    && (branch.no() == null || narrowLoopBodySafe(branch.no(), name));
        if (statement instanceof WhileStmt loop)
            return narrowLoopExpressionSafe(loop.condition(), name) && narrowLoopBodySafe(loop.body(), name);
        if (statement instanceof DoWhileStmt loop)
            return narrowLoopBodySafe(loop.body(), name) && narrowLoopExpressionSafe(loop.condition(), name);
        if (statement instanceof ForStmt loop)
            return (loop.init() == null || narrowLoopBodySafe(loop.init(), name))
                    && (loop.condition() == null || narrowLoopExpressionSafe(loop.condition(), name))
                    && (loop.update() == null || narrowLoopExpressionSafe(loop.update(), name))
                    && narrowLoopBodySafe(loop.body(), name);
        if (statement instanceof SwitchStmt selection)
            return narrowLoopExpressionSafe(selection.value(), name)
                    && selection.cases().stream().allMatch(item -> item.statements().stream()
                            .allMatch(child -> narrowLoopBodySafe(child, name)));
        return statement instanceof EmptyStmt || statement instanceof BreakStmt || statement instanceof ContinueStmt;
    }

    /** Walks an expression tree and fails closed for unsupported node kinds. */
    private boolean narrowLoopExpressionSafe(Expr expression, String name) {
        checkCancelled();
        if (expression instanceof AssignExpr assignment)
            return !(assignment.target() instanceof VariableExpr variable && variable.name().equals(name))
                    && narrowLoopExpressionSafe(assignment.target(), name)
                    && narrowLoopExpressionSafe(assignment.value(), name);
        if (expression instanceof UpdateExpr update)
            return !(update.target() instanceof VariableExpr variable && variable.name().equals(name))
                    && narrowLoopExpressionSafe(update.target(), name);
        if (expression instanceof UnaryExpr unary)
            return !(unary.op() == AMP && unary.value() instanceof VariableExpr variable && variable.name().equals(name))
                    && narrowLoopExpressionSafe(unary.value(), name);
        if (expression instanceof MemberExpr member)
            return narrowLoopExpressionSafe(member.base(), name);
        if (expression instanceof IndexExpr index)
            return narrowLoopExpressionSafe(index.base(), name) && narrowLoopExpressionSafe(index.index(), name);
        if (expression instanceof BinaryExpr binary)
            return narrowLoopExpressionSafe(binary.left(), name) && narrowLoopExpressionSafe(binary.right(), name);
        if (expression instanceof CallExpr call)
            return narrowLoopExpressionSafe(call.callee(), name)
                    && call.arguments().stream().allMatch(argument -> narrowLoopExpressionSafe(argument, name));
        if (expression instanceof CastExpr cast)
            return narrowLoopExpressionSafe(cast.value(), name);
        if (expression instanceof SizeofExpr size)
            return size.value() == null || narrowLoopExpressionSafe(size.value(), name);
        if (expression instanceof InitListExpr list)
            return list.values().stream().allMatch(value -> narrowLoopExpressionSafe(value, name));
        if (expression instanceof ConditionalExpr conditional)
            return narrowLoopExpressionSafe(conditional.condition(), name)
                    && narrowLoopExpressionSafe(conditional.yes(), name)
                    && narrowLoopExpressionSafe(conditional.no(), name);
        if (expression instanceof CommaExpr comma)
            return narrowLoopExpressionSafe(comma.left(), name) && narrowLoopExpressionSafe(comma.right(), name);
        return expression instanceof NumberExpr || expression instanceof FloatExpr || expression instanceof StringExpr
                || expression instanceof VariableExpr;
    }
    private void updateDiscarded(Expr update) {
        if (optimized && update instanceof UpdateExpr increment
                && (increment.amount() == 1 || increment.amount() == -1)
                && increment.target() instanceof VariableExpr variable
                && hasVariable(variable.name())) {
            Binding local = binding(variable.name());
            if (local.slot.label == null && local.type.kind == CType.Kind.INTEGER
                    && !local.type.isBoolean() && !local.type.volatileQualified && local.type.size <= 8) {
                if (increment.amount() == 1)
                    incrementLocal(local.slot, local.type.size);
                else
                    decrementLocal(local.slot, local.type.size);
                return;
            }
        }
        if (optimized && update instanceof AssignExpr assignment
                && (assignment.op() == PLUS_EQUALS || assignment.op() == MINUS_EQUALS)
                && assignment.target() instanceof VariableExpr variable
                && hasVariable(variable.name())) {
            Binding local = binding(variable.name());
            if (local.slot.label == null && local.type.kind == CType.Kind.INTEGER
                    && !local.type.isBoolean() && !local.type.volatileQualified && local.type.size <= 8) {
                BigInteger amount = constantInteger(assignment.value());
                if (amount != null) {
                    updateLocalByConstant(local.slot, local.type.size, amount, assignment.op() == MINUS_EQUALS);
                    return;
                }
            }
        }
        expression(update);
    }
    private BigInteger constantInteger(Expr expression) {
        try {
            return Parser.constant(expression);
        } catch (RuntimeException ignored) {
            return null;
        }
    }
    private void updateLocalByConstant(Slot slot, int size, BigInteger amount, boolean subtract) {
        if (size == 4) {
            BigInteger mask = BigInteger.ONE.shiftLeft(32).subtract(BigInteger.ONE);
            BigInteger immediate = amount.and(mask);
            BigInteger delta = (subtract ? immediate.negate() : immediate).and(mask);
            if (delta.signum() == 0) return;
            emit("MVI A, " + immediate.longValue());
            emit((subtract ? "SUBBC32 " : "ADDBC32 ") + slot.offset);
            return;
        }
        frameAddress(slot.offset);
        for (int byteIndex = 0; byteIndex < size; byteIndex++) {
            int immediate = amount.shiftRight(byteIndex * 8).and(BigInteger.valueOf(255)).intValue();
            nativeEmit("MOV A, M");
            if (byteIndex == 0)
                nativeEmit((subtract ? "SUI " : "ADI ") + immediate);
            else
                nativeEmit((subtract ? "SBI " : "ACI ") + immediate);
            nativeEmit("MOV M, A");
            if (byteIndex + 1 < size && !subtract) {
                nativeEmit("CPI 256");
                nativeEmit("CMC");
            }
            if (byteIndex + 1 < size)
                nativeEmit("INX H");
        }
    }
    private void incrementLocal(Slot slot, int size) {
        if (size == 4) {
            emit("MVI A, 1");
            emit("ADDBC32 " + slot.offset);
            return;
        }
        String done = fresh("loop_increment_done");
        frameAddress(slot.offset);
        for (int byteIndex = 0; byteIndex < size; byteIndex++) {
            nativeEmit("INR M");
            if (byteIndex + 1 < size) {
                nativeEmit("MOV A, M");
                nativeEmit("ORA A");
                nativeEmit("JNZ " + done);
                nativeEmit("INX H");
            }
        }
        if (size > 1) mark(done);
    }
    private void decrementLocal(Slot slot, int size) {
        if (size == 4) {
            emit("MVI A, 1");
            emit("SUBBC32 " + slot.offset);
            return;
        }
        String done = fresh("loop_decrement_done");
        frameAddress(slot.offset);
        for (int byteIndex = 0; byteIndex < size; byteIndex++) {
            nativeEmit("DCR M");
            if (byteIndex + 1 < size) {
                nativeEmit("MOV A, M");
                nativeEmit("CPI 255");
                nativeEmit("JNZ " + done);
                nativeEmit("INX H");
            }
        }
        if (size > 1) mark(done);
    }
    private void initialize(LValue target, Expr initializer) {
        checkCancelled();
        CType type = target.type;
        if (optimized && initializer != null && target.slot != null && target.slot.label == null
                && (type.kind == CType.Kind.ARRAY || type.aggregate()) && type.size <= 65_536
                && !containsVolatileObject(type)) {
            byte[] bytes = new byte[type.size];
            if (constantAggregateInitializer(type, initializer, bytes, 0)) {
                storeBytes(target.slot, bytes);
                return;
            }
        }
        if (type.kind == CType.Kind.ARRAY) {
            List<Expr> values;
            if (initializer instanceof StringExpr string) {
                values = new ArrayList<>(string.value().length());
                for (int index = 0; index < string.value().length(); index++) {
                    if ((index & 255) == 0) checkCancelled();
                    values.add(new NumberExpr(string.value().charAt(index)));
                }
                if (values.size() < type.count)
                    values.add(new NumberExpr(0));
            } else if (initializer instanceof InitListExpr list)
                values = list.values();
            else {
                fail("Array initialization requires braces or a string.");
                return;
            }
            if (values.size() > type.count)
                fail("Too many array initializers.");
            for (int n = 0; n < type.count; n++) {
                if ((n & 255) == 0) checkCancelled();
                initialize(subobject(target, type.element, n * type.element.size),
                        n < values.size() ? values.get(n) : zeroInitializer(type.element));
            }
            return;
        }
        if (type.aggregate() && initializer instanceof InitListExpr list) {
            int count = type.kind == CType.Kind.UNION ? 1 : type.fields.size();
            if (list.values().size() > count)
                fail("Too many aggregate initializers.");
            for (int n = 0; n < count; n++) {
                if ((n & 255) == 0) checkCancelled();
                CType.Field field = type.fields.get(n);
                initialize(subobject(target, field.type(), field.offset()),
                        n < list.values().size() ? list.values().get(n) : zeroInitializer(field.type()));
            }
            return;
        }
        if (initializer instanceof InitListExpr list) {
            if (list.values().size() != 1)
                fail("Invalid scalar initializer.");
            initializer = list.values().get(0);
        }
        if (type.kind == CType.Kind.FLOAT && target.slot != null && target.slot.label == null
                && isConstantExpression(initializer)) {
            ConstantEvaluator.Value constant = ConstantEvaluator.evaluate(initializer, this::typeOf).convert(type);
            BigInteger value = floatingBits(constant.floating(), type);
            storeConstant(target.slot, type.size, value);
        } else if (initializer instanceof NumberExpr number && target.slot != null && target.slot.label == null
                && type.kind == CType.Kind.INTEGER) {
            BigInteger value = type.isBoolean()
                    ? (number.value().signum() == 0 ? BigInteger.ZERO : BigInteger.ONE)
                    : number.value();
            storeConstant(target.slot, type.size, value);
        } else
            write(target, expression(initializer));
    }
    private boolean constantAggregateInitializer(CType type, Expr initializer, byte[] bytes, int offset) {
        checkCancelled();
        if (type.kind == CType.Kind.ARRAY) {
            if (initializer instanceof StringExpr string) {
                if (type.element.kind != CType.Kind.INTEGER || type.element.size != 1
                        || string.value().length() > type.count)
                    return false;
                for (int n = 0; n < string.value().length(); n++) {
                    if ((n & 255) == 0) checkCancelled();
                    bytes[offset + n] = (byte) string.value().charAt(n);
                }
                return true;
            }
            if (!(initializer instanceof InitListExpr list) || list.values().size() > type.count)
                return false;
            for (int n = 0; n < type.count; n++) {
                if ((n & 255) == 0) checkCancelled();
                Expr item = n < list.values().size() ? list.values().get(n) : null;
                if (item != null && !constantAggregateInitializer(type.element, item, bytes,
                        offset + n * type.element.size))
                    return false;
            }
            return true;
        }
        if (type.aggregate()) {
            if (!(initializer instanceof InitListExpr list))
                return false;
            int count = type.kind == CType.Kind.UNION ? 1 : type.fields.size();
            if (list.values().size() > count)
                return false;
            for (int n = 0; n < count; n++) {
                if ((n & 255) == 0) checkCancelled();
                CType.Field field = type.fields.get(n);
                Expr item = n < list.values().size() ? list.values().get(n) : null;
                if (item != null && !constantAggregateInitializer(field.type(), item, bytes,
                        offset + field.offset()))
                    return false;
            }
            return true;
        }
        if (type.kind != CType.Kind.INTEGER && type.kind != CType.Kind.FLOAT)
            return false;
        if (initializer instanceof InitListExpr list) {
            if (list.values().size() != 1)
                return false;
            initializer = list.values().get(0);
        }
        if (!isConstantExpression(initializer))
            return false;
        CType source = typeOf(initializer);
        requireImplicitConversion(source, type);
        ConstantEvaluator.Value value;
        try {
            value = ConstantEvaluator.evaluate(initializer, this::typeOf).convert(type);
        } catch (IllegalArgumentException ignored) {
            return false;
        }
        BigInteger bits = type.kind == CType.Kind.FLOAT ? floatingBits(value.floating(), type) : value.integer();
        for (int n = 0; n < type.size; n++) {
            if ((n & 255) == 0) checkCancelled();
            bytes[offset + n] = bits.shiftRight(n * 8).byteValue();
        }
        return true;
    }
    private boolean containsVolatileObject(CType type) {
        checkCancelled();
        if (type.volatileQualified)
            return true;
        if (type.kind == CType.Kind.ARRAY)
            return containsVolatileObject(type.element);
        if (type.aggregate())
            return type.fields.stream().anyMatch(field -> containsVolatileObject(field.type()));
        return false;
    }
    private Expr zeroInitializer(CType type) {
        return type.aggregate() || type.kind == CType.Kind.ARRAY ? new InitListExpr(List.of()) : new NumberExpr(0);
    }
    private LValue subobject(LValue base, CType type, int offset) {
        return base.slot != null
                ? new LValue(type, base.slot.at(offset), null)
                : new LValue(type, null, addPointer(base.pointer, integer(offset, CType.UINT), false, 1));
    }
    private void staticData(String symbol, CType type, Expr initializer) {
        checkCancelled();
        if (type.size <= 0)
            fail("Incomplete static object " + symbol);
        byte[] bytes = new byte[type.size];
        checkCancelled();
        Map<Integer, String> pointers = new LinkedHashMap<>();
        staticInitializer(type, initializer, bytes, 0, pointers);
        int padding = CType.align(dataBytes, type.alignment()) - dataBytes;
        for (int n = 0; n < padding; n++) {
            if ((n & 255) == 0) checkCancelled();
            data.append("    DB 0\n");
        }
        dataBytes += padding + type.size;
        data.append(symbol).append(":\n");
        for (int n = 0; n < bytes.length; n++) {
            if ((n & 255) == 0) checkCancelled();
            String pointer = pointers.get(n);
            if (pointer != null) {
                data.append("    DQ ").append(pointer).append("\n");
                n += 7;
            } else
                data.append("    DB ").append(bytes[n] & 255).append('\n');
        }
    }
    private Slot stringConstant(StringExpr string) {
        if (!optimized) {
            Slot stored = new Slot(fresh("string"), 0);
            staticData(stored.label(), typeOf(string), string);
            return stored;
        }
        Slot existing = stringConstants.get(string.value());
        if (existing != null)
            return existing;
        Slot stored = new Slot(fresh("string"), 0);
        staticData(stored.label(), typeOf(string), string);
        stringConstants.put(string.value(), stored);
        return stored;
    }
    private void staticInitializer(
            CType type, Expr initializer, byte[] bytes, int offset, Map<Integer, String> pointers) {
        checkCancelled();
        if (initializer == null)
            return;
        if (type.kind == CType.Kind.ARRAY) {
            if (initializer instanceof StringExpr string) {
                if (string.value().length() > type.count)
                    fail("String exceeds array size.");
                for (int n = 0; n < string.value().length(); n++) {
                    if ((n & 255) == 0) checkCancelled();
                    bytes[offset + n] = (byte) string.value().charAt(n);
                }
                return;
            }
            if (!(initializer instanceof InitListExpr))
                fail("Static array needs an initializer list.");
            List<Expr> values = ((InitListExpr) initializer).values();
            if (values.size() > type.count)
                fail("Too many initializers.");
            for (int n = 0; n < values.size(); n++) {
                if ((n & 255) == 0) checkCancelled();
                staticInitializer(type.element, values.get(n), bytes, offset + n * type.element.size, pointers);
            }
            return;
        }
        if (type.aggregate()) {
            if (!(initializer instanceof InitListExpr))
                fail("Static aggregate needs an initializer list.");
            List<Expr> values = ((InitListExpr) initializer).values();
            int count = type.kind == CType.Kind.UNION ? 1 : type.fields.size();
            if (values.size() > count)
                fail("Too many initializers.");
            for (int n = 0; n < values.size(); n++) {
                if ((n & 255) == 0) checkCancelled();
                CType.Field field = type.fields.get(n);
                staticInitializer(field.type(), values.get(n), bytes, offset + field.offset(), pointers);
            }
            return;
        }
        if (initializer instanceof InitListExpr list) {
            if (list.values().size() != 1)
                fail("Invalid scalar initializer.");
            initializer = list.values().get(0);
        }
        diagnosticToken = positions.getOrDefault(initializer, diagnosticToken);
        requireImplicitConversion(typeOf(initializer), type);
        if (type.kind == CType.Kind.POINTER) {
            String address = staticPointer(initializer);
            if (address != null) {
                pointers.put(offset, address);
                return;
            }
            if (initializer instanceof UnaryExpr unary && unary.op() == AMP
                    && unary.value() instanceof VariableExpr variable) {
                pointers.put(offset,
                        functions.containsKey(variable.name()) ? functionLabels.get(variable.name())
                                                               : binding(variable.name()).slot.label);
                return;
            }
            if (initializer instanceof VariableExpr variable && functions.containsKey(variable.name())) {
                pointers.put(offset, functionLabels.get(variable.name()));
                return;
            }
            if (initializer instanceof StringExpr string) {
                pointers.put(offset, stringConstant(string).label());
                return;
            }
        }
        ConstantEvaluator.Value constant = ConstantEvaluator.evaluate(initializer, this::typeOf).convert(type);
        BigInteger value;
        if (type.kind == CType.Kind.FLOAT) {
            double number = constant.floating();
            long bits = type.size == 4 ? Integer.toUnsignedLong(Float.floatToRawIntBits((float) number))
                                       : Double.doubleToRawLongBits(number);
            value = BigInteger.valueOf(bits);
        } else
            value = constant.integer();
        for (int n = 0; n < type.size; n++) {
            if ((n & 255) == 0) checkCancelled();
            bytes[offset + n] = (byte) value.shiftRight(n * 8).intValue();
        }
    }
    private String staticPointer(Expr expression) {
        if (expression instanceof CastExpr cast)
            return staticPointer(cast.value());
        if (expression instanceof VariableExpr variable) {
            if (functions.containsKey(variable.name())) {
                requireVisibleFunction(variable.name());
                return functionLabels.get(variable.name());
            }
            Binding value = binding(variable.name());
            return value.type.kind == CType.Kind.ARRAY ? value.slot.label : null;
        }
        if (expression instanceof UnaryExpr unary && unary.op() == AMP)
            return staticAddress(unary.value());
        if (expression instanceof BinaryExpr binary && (binary.op() == PLUS || binary.op() == MINUS)) {
            String base = staticPointer(binary.left());
            if (base == null)
                return null;
            CType pointer = typeOf(binary.left()).decay();
            long delta = Parser.constant(binary.right()).longValueExact() * pointer.element.size;
            if (binary.op() == MINUS)
                delta = -delta;
            return "(" + base + (delta < 0 ? "" : "+") + delta + ")";
        }
        return null;
    }
    private String staticAddress(Expr expression) {
        if (expression instanceof VariableExpr variable) {
            if (functions.containsKey(variable.name())) {
                requireVisibleFunction(variable.name());
                return functionLabels.get(variable.name());
            }
            String label = binding(variable.name()).slot.label;
            if (label == null)
                fail("Static initializer requires a constant address.");
            return label;
        }
        if (expression instanceof MemberExpr member && !member.pointer()) {
            String base = staticAddress(member.base());
            return "(" + base + "+" + typeOf(member.base()).field(member.name()).offset() + ")";
        }
        if (expression instanceof IndexExpr index) {
            String base = staticPointer(index.base());
            if (base == null)
                fail("Static address requires a static array.");
            return "(" + base + "+" + Parser.constant(index.index()).multiply(BigInteger.valueOf(typeOf(index).size))
                    + ")";
        }
        fail("Static initializer requires a constant address.");
        return null;
    }
    private Value floatConstant(double value, CType type) {
        return integer(floatingBits(value, type), type);
    }
    private BigInteger floatingBits(double value, CType type) {
        long bits = type.size == 4 ? Integer.toUnsignedLong(Float.floatToRawIntBits((float) value))
                                   : Double.doubleToRawLongBits(value);
        return BigInteger.valueOf(bits);
    }
    private Value foldConstant(Expr expression) {
        if (!isConstantExpression(expression))
            return null;
        CType type = typeOf(expression);
        if (!type.scalar() || type.kind == CType.Kind.POINTER)
            return null;
        ConstantEvaluator.Value value;
        try {
            value = ConstantEvaluator.evaluate(expression, this::typeOf).convert(type);
        } catch (IllegalArgumentException ignored) {
            return null;
        }
        if (type.kind == CType.Kind.FLOAT)
            return floatConstant(value.floating(), type);
        return integer(value.integer(), type);
    }
    private boolean isConstantExpression(Expr expression) {
        checkCancelled();
        if (expression instanceof NumberExpr || expression instanceof FloatExpr || expression instanceof SizeofExpr)
            return true;
        if (expression instanceof CastExpr cast)
            return isConstantExpression(cast.value());
        if (expression instanceof UnaryExpr unary)
            return unary.op() != AMP && unary.op() != STAR && isConstantExpression(unary.value());
        if (expression instanceof BinaryExpr binary)
            return isConstantExpression(binary.left()) && isConstantExpression(binary.right());
        if (expression instanceof ConditionalExpr conditional)
            return isConstantExpression(conditional.condition()) && isConstantExpression(conditional.yes())
                    && isConstantExpression(conditional.no());
        return false;
    }
    private Value floatingUnary(Value value, Token.TokenType op) {
        if (op != MINUS)
            fail("Invalid floating unary operator.");
        Value result = temp(value.type);
        copy(result, value);
        load(result.slot.at(result.type.size - 1));
        emit("XRI 128");
        store(result.slot.at(result.type.size - 1));
        return result;
    }
    private Value floatingConvert(Value value, CType type) {
        if (value.type.size > 16 || type.size > 16)
            return new SoftFloat(this).convert(value, type);
        CType destination = type;
        String helper = "CVT_" + runtimeType(value.type) + "_" + runtimeType(destination);
        Value result = helper.equals(inlineRuntime)             ? new SoftFloat(this).convert(value, destination)
                : value.type.size == 4 && destination.size == 4 ? registerRuntime(helper + "_REG", destination, value)
                                                                : runtimeCall(helper, destination, value);
        return type.same(destination) ? result : convert(result, type);
    }
    private Value floatingBinary(Value left, Token.TokenType op, Value right) {
        String helper = "F" + runtimeOperation(op) + left.type.size * 8;
        CType resultType = isComparison(op) ? CType.INT : left.type;
        return helper.equals(inlineRuntime) ? new SoftFloat(this).binary(left, op, right)
                : left.type.size == 4       ? registerRuntime(helper + "_REG", resultType, left, right)
                                            : runtimeCall(helper, resultType, left, right);
    }

    private Value registerRuntime(String helper, CType type, Value... operands) {
        Value result = temp(type);
        loadWord(operands[0].slot, 4);
        emit("MOV D, A");
        if (operands.length == 2) {
            loadWord(operands[1].slot, 4);
            emit("MOV E, A");
        }
        emit("PUSH B");
        emit("MOV B, D");
        if (operands.length == 2)
            emit("MOV C, E");
        wordCall(helper);
        emit("POP B");
        storeWord(result.slot, 4);
        return result;
    }
    private static String runtimeOperation(Token.TokenType op) {
        return switch (op) {
            case PLUS -> "ADD";
            case MINUS -> "SUB";
            case STAR -> "MUL";
            case F_SLASH -> "DIV";
            default -> op.name();
        };
    }
    private static String runtimeType(CType type) {
        return (type.kind == CType.Kind.FLOAT ? "F" : type.unsigned ? "U" : "I") + type.size * 8;
    }
    private static String integerHelper(CType type, Token.TokenType op) {
        if (op == STAR)
            return "MUL" + type.size * 8;
        if (op == F_SLASH || op == PERCENT)
            return (type.unsigned ? "UDIVMOD" : "SDIVMOD") + type.size * 8;
        return null;
    }
    private boolean kernelValue(Value value) {
        return value.slot.label == null && value.type.size > 0 && (value.type.size <= 255 || value.type.size % 4 == 0);
    }
    private boolean wordValue(Value value) {
        return value.slot.label == null && value.type.size >= 4 && value.type.size % 4 == 0;
    }

    private void byteKernel(String name, Value left, Value right) {
        boolean words = wordValue(left) && (right == null || wordValue(right))
                && !Set.of("COPY_BYTES", "FILL_BYTES", "CLEAR_BYTES", "NOT_COPY_BYTES").contains(name);
        if (words)
            name = name.replace("_BYTES", "_WORDS");
        runtime.require(name);
        emit("PUSH PSW");
        if (right != null) {
            frameAddress(right.slot.offset);
            emit("XCHG");
        }
        frameAddress(left.slot.offset);
        emit("POP PSW");
        emit("PUSH B");
        emit("MVI B, " + (words ? left.type.size / 4 : left.type.size));
        emit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + name);
        emit("POP B");
    }

    private Value runtimeCall(String helper, CType type, Value... operands) {
        runtime.require(helper);
        Value result = temp(type);
        int bytes = 8;
        for (int n = operands.length - 1; n >= 0; n--) {
            int size = argumentSize(operands[n].type);
            pushValue(operands[n], size);
            bytes += size;
        }
        frameAddress(result.slot.offset);
        emit("PUSH H");
        emit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + helper);
        emit("LXI H, " + bytes);
        emit("DAD SP");
        emit("SPHL");
        return result;
    }

    private Value fixedShift(Value value, int bits) {
        Value result = temp(value.type);
        int distance = Math.abs(bits), bytes = distance / 8;
        if (kernelValue(value)) {
            int count = Math.max(0, value.type.size - bytes);
            if (count > 0) {
                CType range = CType.integer("byte range", count, true);
                copy(new Value(range, result.slot.at(bits >= 0 ? bytes : 0)),
                        new Value(range, value.slot.at(bits >= 0 ? 0 : bytes)));
            }
            int padding = value.type.size - count;
            if (padding > 0) {
                if (bits < 0 && !value.type.unsigned) {
                    load(value.slot.at(value.type.size - 1));
                    emit("RLC 1");
                    emit("SBB A");
                } else
                    emit("MVI A, 0");
                frameAddress(result.slot.offset + (bits >= 0 ? 0 : count));
                if (padding >= 4) {
                    runtime.require("FILL_BYTES");
                    emit("PUSH B");
                    emit("MVI B, " + padding);
                    emit("CALL " + (runtimePrefix == null ? "_VCC_RT_" : runtimePrefix) + "FILL_BYTES");
                    emit("POP B");
                } else
                    for (int n = 0; n < padding; n++) {
                        emit("MOV M, A");
                        if (n + 1 < padding)
                            emit("INX H");
                    }
            }
            for (int n = 0; n < distance % 8; n++) shiftOne(result, bits >= 0, bits < 0 && !value.type.unsigned);
            return result;
        }
        for (int n = 0; n < value.type.size; n++) {
            int source = bits >= 0 ? n - bytes : n + bytes;
            if (source >= 0 && source < value.type.size)
                load(value.slot.at(source));
            else if (bits < 0 && !value.type.unsigned) {
                load(value.slot.at(value.type.size - 1));
                emit("RLC 1");
                emit("SBB A");
            } else
                emit("MVI A, 0");
            store(result.slot.at(n));
        }
        for (int n = 0; n < distance % 8; n++) shiftOne(result, bits >= 0, bits < 0 && !value.type.unsigned);
        return result;
    }
    RuntimeLibrary runtimeDependencies() {
        return runtime;
    }
    static String generateHelper(String key, RuntimeLibrary destinationLibrary) {
        return generateHelper(key, destinationLibrary, () -> false);
    }
    static String generateHelper(String key, RuntimeLibrary destinationLibrary, BooleanSupplier cancelled) {
        CodeGenerator g = new CodeGenerator("RT_" + key, Map.of(), false, cancelled);
        g.checkCancelled();
        g.inlineRuntime = key;
        g.runtimePrefix = "_VCC_RT_";
        List<CType> params = new ArrayList<>();
        Token.TokenType op = null;
        CType destination = null;
        boolean unpack = key.startsWith("UNPACK"), pack = key.startsWith("PACK"), sticky = key.equals("STICKY128"),
                cvt = key.startsWith("CVT_");
        java.util.function.Function<String, CType> type = name -> {
            int bits = Integer.parseInt(name.substring(1));
            return name.charAt(0) == 'F' ? (bits == 32 ? CType.FLOAT : CType.DOUBLE)
                                         : CType.integer(name, bits / 8, name.charAt(0) == 'U');
        };
        if (unpack)
            params.add(key.endsWith("32") ? CType.FLOAT : CType.DOUBLE);
        else if (pack) {
            destination = key.endsWith("32") ? CType.FLOAT : CType.DOUBLE;
            params.addAll(List.of(CType.CHAR, type.apply("U128"), CType.INT));
        } else if (sticky)
            params.addAll(List.of(type.apply("U128"), CType.UINT));
        else if (cvt) {
            String[] names = key.split("_");
            params.add(type.apply(names[1]));
            destination = type.apply(names[2]);
        } else {
            String number = key.replaceFirst("^.*?([0-9]+)$", "$1");
            int bits = Integer.parseInt(number);
            String operation = key.substring(0, key.length() - number.length());
            CType t;
            if (operation.equals("MUL")) {
                op = STAR;
                t = type.apply("U" + bits);
            } else if (operation.endsWith("DIVMOD")) {
                op = F_SLASH;
                t = type.apply((operation.startsWith("U") ? "U" : "I") + bits);
            } else if (operation.equals("SHL") || operation.equals("SHR") || operation.equals("SAR")) {
                op = operation.equals("SHL") ? SHIFT_LEFT : SHIFT_RIGHT;
                t = type.apply((operation.equals("SAR") ? "I" : "U") + bits);
            } else {
                op = switch (operation.substring(1)) {
                    case "ADD" -> PLUS;
                    case "SUB" -> MINUS;
                    case "MUL" -> STAR;
                    case "DIV" -> F_SLASH;
                    case "CMP" -> EQUAL_EQUAL;
                    default -> Token.TokenType.valueOf(operation.substring(1));
                };
                t = type.apply(operation.substring(0, 1) + bits);
            }
            params.add(t);
            params.add(op == SHIFT_LEFT || op == SHIFT_RIGHT ? CType.UINT : t);
        }
        List<Value> values = new ArrayList<>();
        int offset = 8;
        for (CType t : params) {
            g.checkCancelled();
            values.add(new Value(t, new Slot(null, offset)));
            offset += g.argumentSize(t);
        }
        Value result;
        SoftFloat sf = g.new SoftFloat(g);
        if (unpack) {
            SoftFloat.Parts parts = sf.unpack(values.get(0));
            result = g.temp(CType.integer("parts", 29 + params.get(0).size, true));
            int at = 0;
            for (Value v : List.of(parts.bits(), parts.sign(), parts.mantissa(), parts.exponent(), parts.rawExponent(),
                         parts.classification())) {
                g.checkCancelled();
                g.copy(new Value(v.type, result.slot.at(at)), v);
                at += v.type.size;
            }
        } else if (pack)
            result = sf.pack(values.get(0), values.get(1), values.get(2), destination);
        else if (sticky)
            result = sf.rightSticky(values.get(0), values.get(1));
        else if (cvt)
            result = g.floatingConvert(values.get(0), destination);
        else if (key.startsWith("FCMP"))
            result = sf.binary(values.get(0), EQUAL_EQUAL, values.get(1));
        else if (key.startsWith("F"))
            result = g.floatingBinary(values.get(0), op, values.get(1));
        else if (op == SHIFT_LEFT || op == SHIFT_RIGHT)
            result = g.shift(values.get(0), op, values.get(1));
        else
            result = g.integerOperation(values.get(0), op, values.get(1));
        g.pointerRegisters(new Value(CType.pointer(CType.CHAR), new Slot(null, 0)));
        g.emit("XCHG");
        for (int n = 0; n < result.type.size;) {
            if (n + 4 <= result.type.size) {
                g.loadWord(result.slot.at(n), 4);
                g.emit("XCHG");
                g.wordCall("STORE32");
                g.emit("XCHG");
                n += 4;
                if (n < result.type.size)
                    for (int k = 0; k < 4; k++) g.emit("INX D");
            } else {
                g.load(result.slot.at(n));
                g.emit("STAX D");
                n++;
                if (n < result.type.size)
                    g.emit("INX D");
            }
        }
        g.emit("LXI H, -16");
        g.emit("DAD B");
        g.emit("SPHL");
        g.emit("POP B");
        g.emit("RET");
        g.checkCancelled();
        String assembly = "_VCC_RT_" + key
                + ":\n    PUSH B\n    LXI H, 16\n    DAD SP\n    MOV B, H\n    MOV C, L\n    LXI H, " + (-g.peak)
                + "\n    DAD SP\n    SPHL\n" + g.code;
        for (String dependency : g.runtime.required) {
            g.checkCancelled();
            destinationLibrary.require(dependency);
        }
        g.checkCancelled();
        return assembly;
    }

    private final class SoftFloat {
        private final CType wide = CType.integer("uint16", 16, true);
        private record
                Parts(Value bits, Value sign, Value mantissa, Value exponent, Value rawExponent, Value classification) {
        }
        SoftFloat(CodeGenerator ignored) {}
        private int fraction(CType type) {
            return type.size == 4 ? 23 : 52;
        }
        private int bias(CType type) {
            return type.size == 4 ? 127 : 1023;
        }
        private int maxExponent(CType type) {
            return type.size == 4 ? 255 : 2047;
        }
        private BigInteger bit(int position) {
            return BigInteger.ONE.shiftLeft(position);
        }
        private CType bitsType(CType type) {
            return CType.integer("uint" + type.size, type.size, true);
        }
        private Value op(Value left, Token.TokenType operation, Value right) {
            return binaryValues(left, operation, right);
        }
        private Value number(long number, CType type) {
            return integer(number, type);
        }
        private Value mask(Value value, BigInteger mask) {
            return op(value, AMP, integer(mask, value.type));
        }
        private Value compare(Value value, Token.TokenType operation, long number) {
            return op(value, operation, integer(number, value.type));
        }
        private void set(Value target, Value source) {
            copy(target, CodeGenerator.this.convert(source, target.type));
        }
        private void choose(Value condition, Runnable yes, Runnable no) {
            String other = fresh("fp_else"), done = fresh("fp_join");
            test(condition);
            emit("JZ " + other);
            yes.run();
            emit("JMP " + done);
            mark(other);
            if (no != null)
                no.run();
            mark(done);
        }
        private Parts unpack(Value value) {
            if (!inlineRuntime.equals("UNPACK" + value.type.size * 8)) {
                Value parts = runtimeCall("UNPACK" + value.type.size * 8,
                        CType.integer("float parts", 29 + value.type.size, true), value);
                int at = value.type.size;
                return new Parts(new Value(bitsType(value.type), parts.slot), new Value(CType.CHAR, parts.slot.at(at)),
                        new Value(wide, parts.slot.at(at + 1)), new Value(CType.INT, parts.slot.at(at + 17)),
                        new Value(CType.INT, parts.slot.at(at + 21)), new Value(CType.INT, parts.slot.at(at + 25)));
            }
            CType type = value.type;
            int fraction = fraction(type);
            Value bits = new Value(bitsType(type), value.slot);
            Value sign = CodeGenerator.this.convert(fixedShift(bits, -(type.size * 8 - 1)), CType.CHAR);
            Value mantissa = CodeGenerator.this.convert(mask(bits, bit(fraction).subtract(BigInteger.ONE)), wide);
            Value rawExponent = CodeGenerator.this.convert(
                    mask(fixedShift(bits, -fraction), BigInteger.valueOf(maxExponent(type))), CType.INT);
            Value exponent = temp(CType.INT);
            copy(exponent, rawExponent);
            choose(compare(rawExponent, EQUAL_EQUAL, 0),
                    ()
                            -> set(exponent, number(1, CType.INT)),
                    () -> set(mantissa, op(mantissa, PIPE, integer(bit(fraction), wide))));
            set(exponent, op(exponent, MINUS, number(bias(type) + fraction, CType.INT)));
            Parts parts = new Parts(bits, sign, mantissa, exponent, rawExponent, null);
            Value classification = number(0, CType.INT);
            copy(new Value(CType.CHAR, classification.slot), new Value(CType.CHAR, nan(parts, type).slot));
            copy(new Value(CType.CHAR, classification.slot.at(1)), new Value(CType.CHAR, infinity(parts, type).slot));
            copy(new Value(CType.CHAR, classification.slot.at(2)), new Value(CType.CHAR, zero(parts, type).slot));
            return new Parts(bits, sign, mantissa, exponent, rawExponent, classification);
        }
        private Value nan(Parts value, CType type) {
            if (value.classification != null)
                return new Value(CType.CHAR, value.classification.slot);
            Value exponent = compare(value.rawExponent, EQUAL_EQUAL, maxExponent(type));
            Value fraction = mask(value.bits, bit(fraction(type)).subtract(BigInteger.ONE));
            Value nonzero = compare(fraction, NOT_EQUAL, 0);
            return op(exponent, AMP, nonzero);
        }
        private Value infinity(Parts value, CType type) {
            if (value.classification != null)
                return new Value(CType.CHAR, value.classification.slot.at(1));
            return op(compare(value.rawExponent, EQUAL_EQUAL, maxExponent(type)), AMP,
                    compare(mask(value.bits, bit(fraction(type)).subtract(BigInteger.ONE)), EQUAL_EQUAL, 0));
        }
        private Value zero(Parts value, CType type) {
            return value.classification != null
                    ? new Value(CType.CHAR, value.classification.slot.at(2))
                    : compare(mask(value.bits, bit(type.size * 8 - 1).subtract(BigInteger.ONE)), EQUAL_EQUAL, 0);
        }
        private void normalizeDivisorOperand(Parts value, CType type) {
            String loop = fresh("fp_div_normalize"), done = fresh("fp_div_normalized");
            test(value.mantissa);
            emit("JZ " + done);
            mark(loop);
            test(op(value.mantissa, GREATER_EQUAL, integer(bit(fraction(type)), wide)));
            emit("JNZ " + done);
            shiftOne(value.mantissa, true, false);
            set(value.exponent, op(value.exponent, MINUS, number(1, CType.INT)));
            emit("JMP " + loop);
            mark(done);
        }
        private Value special(CType type, Value sign, boolean nan) {
            CType integerType = bitsType(type);
            BigInteger bits = BigInteger.valueOf(maxExponent(type)).shiftLeft(fraction(type));
            if (nan)
                bits = bits.or(bit(fraction(type) - 1));
            Value base = integer(bits, integerType);
            base = op(base, PIPE, fixedShift(CodeGenerator.this.convert(sign, integerType), type.size * 8 - 1));
            return new Value(type, base.slot);
        }
        private Value rightSticky(Value value, Value distance) {
            if (value.type.size == 16 && !inlineRuntime.equals("STICKY128"))
                return runtimeCall("STICKY128", value.type, value, CodeGenerator.this.convert(distance, CType.UINT));
            Value result = temp(value.type);
            copy(result, value);
            Value count = temp(CType.UINT);
            copy(count, CodeGenerator.this.convert(distance, CType.UINT));
            Value sticky = number(0, CType.CHAR);
            String large = fresh("fp_shift_large"), loop = fresh("fp_shift"), done = fresh("fp_shift_done");
            Value excessive = compare(count, GREATER_EQUAL, value.type.size * 8L);
            test(excessive);
            emit("JNZ " + large);
            mark(loop);
            test(count);
            emit("JZ " + done);
            set(sticky, op(sticky, PIPE, mask(result, BigInteger.ONE)));
            shiftOne(result, false, false);
            set(count, op(count, MINUS, number(1, CType.UINT)));
            emit("JMP " + loop);
            mark(large);
            test(result);
            String isZero = fresh("fp_shift_zero");
            emit("JZ " + isZero);
            set(sticky, number(1, CType.CHAR));
            mark(isZero);
            set(result, number(0, result.type));
            mark(done);
            set(result, op(result, PIPE, CodeGenerator.this.convert(sticky, result.type)));
            return result;
        }
        private Value pack(Value sign, Value mantissa, Value exponent, CType type) {
            if (mantissa.type.size == 16 && !inlineRuntime.equals("PACK" + type.size * 8))
                return runtimeCall("PACK" + type.size * 8, type, sign, mantissa, exponent);
            Value result = temp(type);
            int keep = next;
            Value work = temp(mantissa.type);
            copy(work, mantissa);
            Value power = temp(CType.INT);
            copy(power, exponent);
            int fraction = fraction(type);
            BigInteger minimum = bit(fraction + 3), maximum = bit(fraction + 4);
            String low = fresh("fp_normalize_low"), high = fresh("fp_normalize_high"),
                   normalized = fresh("fp_normalized"), zero = fresh("fp_zero"), done = fresh("fp_done");
            test(work);
            emit("JZ " + zero);
            mark(low);
            test(op(work, GREATER_EQUAL, integer(minimum, work.type)));
            emit("JNZ " + high);
            shiftOne(work, true, false);
            set(power, op(power, MINUS, number(1, CType.INT)));
            emit("JMP " + low);
            mark(high);
            test(op(work, LESS, integer(maximum, work.type)));
            emit("JNZ " + normalized);
            set(work, rightSticky(work, number(1, CType.UINT)));
            set(power, op(power, PLUS, number(1, CType.INT)));
            emit("JMP " + high);
            mark(normalized);
            Value encodedExponent = op(power, PLUS, number(fraction + 3 + bias(type), CType.INT));
            choose(compare(encodedExponent, LESS_EQUAL, 0), () -> {
                Value distance = op(number(1, CType.INT), MINUS, encodedExponent);
                set(work, rightSticky(work, distance));
                set(encodedExponent, number(0, CType.INT));
            }, null);
            Value rounding = mask(work, BigInteger.valueOf(7));
            Value retained = fixedShift(work, -3);
            Value above = compare(rounding, GREATER, 4), tie = compare(rounding, EQUAL_EQUAL, 4),
                  odd = mask(retained, BigInteger.ONE);
            Value roundUp = op(above, PIPE, op(tie, AMP, CodeGenerator.this.convert(odd, CType.INT)));
            choose(roundUp, () -> set(retained, op(retained, PLUS, number(1, retained.type))), null);
            choose(op(retained, GREATER_EQUAL, integer(bit(fraction + 1), retained.type)), () -> {
                set(retained, fixedShift(retained, -1));
                set(encodedExponent, op(encodedExponent, PLUS, number(1, CType.INT)));
            }, null);
            Value becameNormal = op(compare(encodedExponent, EQUAL_EQUAL, 0), AMP,
                    op(retained, GREATER_EQUAL, integer(bit(fraction), retained.type)));
            choose(becameNormal, () -> set(encodedExponent, number(1, CType.INT)), null);
            choose(compare(encodedExponent, GREATER_EQUAL, maxExponent(type)),
                    () -> copy(result, special(type, sign, false)), () -> {
                        CType integerType = bitsType(type);
                        Value significand = CodeGenerator.this.convert(
                                mask(retained, bit(fraction).subtract(BigInteger.ONE)), integerType);
                        Value encoded = op(significand, PIPE,
                                fixedShift(CodeGenerator.this.convert(encodedExponent, integerType), fraction));
                        encoded = op(encoded, PIPE,
                                fixedShift(CodeGenerator.this.convert(sign, integerType), type.size * 8 - 1));
                        copy(result, new Value(type, encoded.slot));
                    });
            emit("JMP " + done);
            mark(zero);
            Value signedZero = fixedShift(CodeGenerator.this.convert(sign, bitsType(type)), type.size * 8 - 1);
            copy(result, new Value(type, signedZero.slot));
            mark(done);
            next = keep;
            return result;
        }
        Value convert(Value source, CType type) {
            Value result = temp(type);
            int keep = next;
            if (source.type.kind != CType.Kind.FLOAT) {
                CType magnitudeType =
                        CType.integer("uint" + Math.max(16, source.type.size), Math.max(16, source.type.size), true);
                Value magnitude = temp(magnitudeType), sign = number(0, CType.CHAR);
                copy(magnitude, source);
                if (!source.type.unsigned)
                    choose(compare(source, LESS, 0), () -> {
                        set(sign, number(1, CType.CHAR));
                        negate(magnitude);
                    }, null);
                copy(result, pack(sign, magnitude, number(0, CType.INT), type));
            } else {
                Parts parts = unpack(source);
                if (type.kind == CType.Kind.FLOAT) {
                    choose(nan(parts, source.type), () -> copy(result, special(type, parts.sign, true)), () -> {
                        choose(infinity(parts, source.type),
                                ()
                                        -> copy(result, special(type, parts.sign, false)),
                                () -> copy(result, pack(parts.sign, parts.mantissa, parts.exponent, type)));
                    });
                } else {
                    CType magnitudeType =
                            CType.integer("uint" + Math.max(16, type.size), Math.max(16, type.size), true);
                    Value magnitude = temp(magnitudeType);
                    copy(magnitude, parts.mantissa);
                    choose(compare(parts.exponent, GREATER_EQUAL, 0),
                            () -> set(magnitude, shift(magnitude, SHIFT_LEFT, parts.exponent)), () -> {
                                Value distance = temp(CType.INT);
                                copy(distance, parts.exponent);
                                negate(distance);
                                set(magnitude, shift(magnitude, SHIFT_RIGHT, distance));
                            });
                    choose(compare(parts.sign, NOT_EQUAL, 0), () -> negate(magnitude), null);
                    copy(result,
                            new Value(CType.integer("int" + magnitudeType.size, magnitudeType.size, false),
                                    magnitude.slot));
                }
            }
            next = keep;
            return result;
        }
        Value binary(Value left, Token.TokenType operation, Value right) {
            if (operation == MINUS)
                return runtimeCall("FADD" + left.type.size * 8, left.type, left, floatingUnary(right, MINUS));
            if (isComparison(operation) && !inlineRuntime.equals("FCMP" + left.type.size * 8)) {
                Value order = runtimeCall("FCMP" + left.type.size * 8, CType.INT, left, right);
                int selected = switch (operation) {
                    case LESS -> 1;
                    case EQUAL_EQUAL -> 2;
                    case GREATER -> 4;
                    case LESS_EQUAL -> 3;
                    case GREATER_EQUAL -> 6;
                    default -> 13;
                };
                return compare(mask(order, BigInteger.valueOf(selected)), NOT_EQUAL, 0);
            }
            CType type = left.type;
            Value result = temp(isComparison(operation) ? CType.INT : type);
            int keep = next;
            Parts a = unpack(left), b = unpack(right);
            if (isComparison(operation)) {
                choose(op(nan(a, type), PIPE, nan(b, type)), () -> set(result, number(8, CType.INT)), () -> {
                    Value bothZero = op(zero(a, type), AMP, zero(b, type));
                    choose(bothZero, () -> set(result, number(2, CType.INT)), () -> {
                        choose(op(a.sign, EQUAL_EQUAL, b.sign),
                                ()
                                        -> {
                                    choose(op(a.bits, EQUAL_EQUAL, b.bits),
                                            () -> set(result, number(2, CType.INT)), () -> {
                                                Value less = op(op(a.bits, LESS, b.bits), CARET,
                                                        CodeGenerator.this.convert(a.sign, CType.INT));
                                                choose(less,
                                                        ()
                                                                -> set(result, number(1, CType.INT)),
                                                        () -> set(result, number(4, CType.INT)));
                                            });
                                },
                                ()
                                        -> choose(compare(a.sign, NOT_EQUAL, 0),
                                                ()
                                                        -> set(result, number(1, CType.INT)),
                                                () -> set(result, number(4, CType.INT))));
                    });
                });
                next = keep;
                return result;
            }
            if (operation != PLUS && operation != MINUS && operation != STAR && operation != F_SLASH)
                fail("Invalid floating operator " + operation);
            Value sign = number(0, CType.CHAR), mantissa = number(0, wide), exponent = number(0, CType.INT);
            if (operation == MINUS)
                set(b.sign, op(b.sign, CARET, number(1, CType.CHAR)));
            Value anyNan = op(nan(a, type), PIPE, nan(b, type)), infA = infinity(a, type), infB = infinity(b, type),
                  zeroA = zero(a, type), zeroB = zero(b, type);
            String exceptional = fresh("fp_exceptional"), done = fresh("fp_binary_done");
            test(op(anyNan, PIPE, op(op(infA, PIPE, infB), PIPE, operation == F_SLASH ? zeroB : number(0, CType.INT))));
            emit("JNZ " + exceptional);
            if (operation == PLUS || operation == MINUS) {
                Value am = fixedShift(a.mantissa, 3), bm = fixedShift(b.mantissa, 3);
                Value ae = op(a.exponent, MINUS, number(3, CType.INT)),
                      be = op(b.exponent, MINUS, number(3, CType.INT));
                set(exponent, ae);
                choose(op(ae, GREATER_EQUAL, be), () -> set(bm, rightSticky(bm, op(ae, MINUS, be))), () -> {
                    set(am, rightSticky(am, op(be, MINUS, ae)));
                    set(exponent, be);
                });
                choose(op(a.sign, EQUAL_EQUAL, b.sign),
                        ()
                                -> {
                            set(sign, a.sign);
                            set(mantissa, op(am, PLUS, bm));
                        },
                        () -> {
                            choose(op(am, GREATER_EQUAL, bm),
                                    ()
                                            -> {
                                        set(sign, a.sign);
                                        set(mantissa, op(am, MINUS, bm));
                                    },
                                    () -> {
                                        set(sign, b.sign);
                                        set(mantissa, op(bm, MINUS, am));
                                    });

                            choose(compare(mantissa, EQUAL_EQUAL, 0), () -> set(sign, number(0, CType.CHAR)), null);
                        });
            } else if (operation == STAR) {
                set(sign, op(a.sign, CARET, b.sign));
                set(mantissa, op(a.mantissa, STAR, b.mantissa));
                set(exponent, op(a.exponent, PLUS, b.exponent));
            } else {
                normalizeDivisorOperand(a, type);
                normalizeDivisorOperand(b, type);
                int precision = fraction(type) + 4;
                set(sign, op(a.sign, CARET, b.sign));
                Value dividend = fixedShift(a.mantissa, precision);
                Value pair = runtimeCall(
                        "UDIVMOD128", CType.integer("quotient and remainder", 32, true), dividend, b.mantissa);
                set(mantissa, new Value(wide, pair.slot));
                Value rest = new Value(wide, pair.slot.at(16));
                choose(compare(rest, NOT_EQUAL, 0), () -> set(mantissa, op(mantissa, PIPE, number(1, wide))), null);
                set(exponent, op(op(a.exponent, MINUS, b.exponent), MINUS, number(precision, CType.INT)));
            }
            copy(result, pack(sign, mantissa, exponent, type));
            emit("JMP " + done);
            mark(exceptional);
            if (operation == PLUS || operation == MINUS) {
                Value oppositeInf = op(op(infA, AMP, infB), AMP, op(a.sign, NOT_EQUAL, b.sign));
                choose(op(anyNan, PIPE, oppositeInf), () -> copy(result, special(type, a.sign, true)), () -> {
                    choose(infA,
                            ()
                                    -> copy(result, special(type, a.sign, false)),
                            () -> copy(result, special(type, b.sign, false)));
                });
            } else {
                Value invalid = operation == STAR ? op(op(infA, AMP, zeroB), PIPE, op(infB, AMP, zeroA))
                                                  : op(op(infA, AMP, infB), PIPE, op(zeroA, AMP, zeroB));
                Value signed = op(a.sign, CARET, b.sign);
                choose(op(anyNan, PIPE, invalid), () -> copy(result, special(type, signed, true)), () -> {
                    if (operation == F_SLASH)
                        choose(infB,
                                ()
                                        -> copy(result,
                                                new Value(type,
                                                        fixedShift(CodeGenerator.this.convert(signed, bitsType(type)),
                                                                type.size * 8 - 1)
                                                                .slot)),
                                () -> copy(result, special(type, signed, false)));
                    else
                        copy(result, special(type, signed, false));
                });
            }
            mark(done);
            next = keep;
            return result;
        }
    }
    private void fail(String message) {
        throw new SourceDiagnostic(diagnosticToken, message);
    }
}
