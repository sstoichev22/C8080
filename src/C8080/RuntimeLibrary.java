package C8080;

import java.util.*;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;

/** Collects runtime routines and emits them once, including their transitive dependencies. */
final class RuntimeLibrary {
    final Set<String> required = new LinkedHashSet<>();

    void require(String name) {
        required.add(name);
    }

    String assembly(String prefix) {
        return assembly(prefix, () -> false);
    }

    String assembly(String prefix, BooleanSupplier cancelled) {
        BooleanSupplier cancellation = cancelled == null ? () -> false : cancelled;
        checkCancelled(cancellation);
        StringBuilder output = new StringBuilder();
        List<String> pending = new ArrayList<>(required);
        Set<String> scheduled = new HashSet<>(pending);
        for (int index = 0; index < pending.size(); index++) {
            checkCancelled(cancellation);
            String name = pending.get(index);
            String body = Float32Runtime.routine(name, this);
            if (body == null) body = WordRuntime.routine(name, this);
            if (body == null) body = nativeRoutine(name);
            if (body == null) body = kernel(name);
            if (body == null) body = CodeGenerator.generateHelper(name, this, cancellation);
            checkCancelled(cancellation);
            output.append(body);

            for (String dependency : required) {
                checkCancelled(cancellation);
                if (scheduled.add(dependency)) {
                    pending.add(dependency);
                }
            }
        }
        checkCancelled(cancellation);
        String assembly = output.toString();
        checkCancelled(cancellation);
        return assembly.replace("_VCC_RT_", prefix);
    }

    private static void checkCancelled(BooleanSupplier cancelled) {
        if (cancelled.getAsBoolean()) throw new CancellationException("Runtime helper generation was cancelled.");
    }
    private static String nativeRoutine(String name){
        if(name.equals("mul32"))return """
_VCC_RT_mul32:
    MVI D, 0
    MVI H, 32
_VCC_RT_mul32_loop:
    MOV A, C
    ANI 1
    JZ _VCC_RT_mul32_skip
    MOV A, D
    ADD B
    MOV D, A
_VCC_RT_mul32_skip:
    MOV A, B
    ADD A
    MOV B, A
    MOV A, C
    ORA A
    RAR 1
    MOV C, A
    DCR H
    JNZ _VCC_RT_mul32_loop
    MOV A, D
    RET
""";
        if(!Set.of("udiv32","sdiv32","umod32","smod32").contains(name))return null;
        String head="_VCC_RT_"+name,sign=name.startsWith("s")?"""
    MVI L, 0
    MOV A, B
    ORA A
    JP %s_bpositive
    CMA
    ADI 1
    MOV B, A
    MVI L, 3
%s_bpositive:
    MOV A, C
    ORA A
    JP %s_cpositive
    CMA
    ADI 1
    MOV C, A
    MOV A, L
    XRI 1
    MOV L, A
%s_cpositive:
""".formatted(head,head,head,head):"";
        String body="""
    MOV A, C
    ORA A
    JNZ %s_nonzero
    STOP
%s_nonzero:
    MVI D, 0
    MVI H, 32
%s_loop:
    MOV A, B
    ADD A
    MOV B, A
    MOV A, D
    RAL 1
    MOV D, A
    JC %s_subtract
    CMP C
    JC %s_skip
%s_subtract:
    SUB C
    MOV D, A
    INR B
%s_skip:
    DCR H
    JNZ %s_loop
    MOV A, %s
""".formatted(head,head,head,head,head,head,head,head,name.contains("mod")?"D":"B");
        String tail=name.startsWith("s")?"""
    MOV E, A
    MOV A, L
    ANI %d
    JZ %s_positive
    MOV A, E
    CMA
    ADI 1
    RET
%s_positive:
    MOV A, E
    RET
""".formatted(name.contains("mod")?2:1,head,head):"    RET\n";
        return head+":\n"+sign+body+tail;
    }
    private String kernel(String name){
        String h="_VCC_RT_"+name;String code;
        switch(name){
            case "COPY_BYTES" -> code="LDAX D\nMOV M, A\nINX D\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "NOT_COPY_BYTES" -> code="LDAX D\nCMA\nMOV M, A\nINX D\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "FILL_BYTES" -> code="MOV M, A\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "TEST_BYTES" -> code="MVI C, 0\n"+h+"_loop:\nMOV A, M\nORA C\nMOV C, A\nINX H\nDCR B\nJNZ "+h+"_loop\nORA A\nRET\n";
            case "ADD_BYTES","SUB_BYTES" -> code="XRA A\n"+h+"_loop:\nLDAX D\nMOV C, A\nMOV A, M\n"+(name.startsWith("ADD")?"ADC C":"SBB C")+"\nMOV M, A\nINX D\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "AND_BYTES","OR_BYTES","XOR_BYTES" -> code="LDAX D\nMOV C, A\nMOV A, M\n"+(name.startsWith("AND")?"ANA":name.startsWith("XOR")?"XRA":"ORA")+" C\nMOV M, A\nINX D\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "NEG_BYTES" -> code="STC\n"+h+"_loop:\nMOV A, M\nCMA\nACI 0\nMOV M, A\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "SHL_BYTES" -> {require("RCL_BYTES");return h+":\n    XRA A\n    JMP _VCC_RT_RCL_BYTES\n";}
            case "RCL_BYTES" -> code="MOV A, M\nRAL 1\nMOV M, A\nINX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            case "SHR_BYTES","SAR_BYTES","RCR_BYTES" -> {

                String init="PUSH PSW\nPUSH D\nMVI D, 0\nMOV E, B\nDAD D\nDCX H\nPOP D\nPOP PSW\n";
                if(name.equals("SHR_BYTES"))init+="XRA A\n";
                if(name.equals("SAR_BYTES"))init+="MOV A, M\nRLC 1\n";
                code=init+h+"_loop:\nMOV A, M\nRAR 1\nMOV M, A\nDCX H\nDCR B\nJNZ "+h+"_loop\nRET\n";
            }
            case "CMP_BYTES","SCMP_BYTES" -> {
                String init="MOV A, B\nPUSH B\nMVI B, 0\nMOV C, A\nDAD B\nDCX H\nXCHG\nDAD B\nDCX H\nXCHG\nPOP B\n";
                String signed=name.startsWith("S")?"MOV A, M\nMOV C, A\nLDAX D\nXRA C\nANI 128\nJZ "+h+"_loop\nMOV A, C\nANI 128\nJNZ "+h+"_less\nJMP "+h+"_greater\n":"";
                code=init+signed+h+"_loop:\nLDAX D\nMOV C, A\nMOV A, M\nCMP C\nJC "+h+"_less\nJNZ "+h+"_greater\nDCX H\nDCX D\nDCR B\nJNZ "+h+"_loop\nMVI A, 2\nRET\n"+h+"_less:\nMVI A, 1\nRET\n"+h+"_greater:\nMVI A, 4\nRET\n";
            }
            default -> {return null;}
        }
        if(!code.contains(h+"_loop:"))code=h+"_loop:\n"+code;
        StringBuilder out=new StringBuilder(h+":\n");int n=0;
        for(String line:code.split("\n")){if(line.endsWith(":"))out.append(line).append('\n');else out.append(ByteAssembly.lower(line,h+"_byte"+n++));}
        return out.toString();
    }
}
