package C8080;

/** Generates the 32-bit word runtime helpers (multiply, divide, remainder, shifts) for compiled C. */
final class WordRuntime {
    private WordRuntime() {}
    static String routine(String name,RuntimeLibrary dependencies){
        String h="_VCC_RT_"+name;
        if(name.endsWith("32_REG")){
            String operation=name.substring(0,name.length()-4);
            dependencies.require(operation);dependencies.require("LOAD32");
            boolean unary=operation.startsWith("CVT_");int arguments=unary?8:16;
            return h+":\n    LXI H, -8\n    DAD SP\n    SPHL\n    MVI D, 0\n"+
                (unary?"":"    MOV E, C\n    PUSH D\n")+
                "    MOV E, B\n    PUSH D\n    LXI H, "+arguments+"\n    DAD SP\n    PUSH H\n    CALL _VCC_RT_"+operation+
                "\n    LXI H, "+(arguments+8)+"\n    DAD SP\n    CALL _VCC_RT_LOAD32\n    LXI H, "+(arguments+16)+"\n    DAD SP\n    SPHL\n    RET\n";
        }
        if(name.equals("LOAD32")){
            StringBuilder out=new StringBuilder(h+":\n    PUSH D\n    PUSH PSW\n    INX H\n    INX H\n    INX H\n    MOV E, M\n");
            for(int n=0;n<3;n++){out.append("    DCX H\n    MOV A, E\n");out.append("    RLC 8\n");out.append("    ORA M\n    MOV E, A\n");}
            return out+"    POP PSW\n    MOV A, E\n    POP D\n    RET\n";
        }
        if(name.equals("STORE32")){
            StringBuilder out=new StringBuilder(h+":\n    PUSH PSW\n    MOV M, A\n");
            for(int n=0;n<3;n++){out.append("    INX H\n");out.append("    RRC 8\n");out.append("    MOV M, A\n");}
            return out+"    DCX H\n    DCX H\n    DCX H\n    POP PSW\n    RET\n";
        }
        if(!name.endsWith("_WORDS"))return null;
        dependencies.require("LOAD32");dependencies.require("STORE32");
        String advance="    INX H\n".repeat(4),retreat="    DCX H\n".repeat(4);
        String advanceRight="    INX D\n".repeat(4),retreatRight="    DCX D\n".repeat(4);
        String count="    DCR B\n    JNZ "+h+"_loop\n";
        String ends="    PUSH PSW\n    MOV A, B\n    PUSH B\n    MVI B, 0\n    ADD A\n    ADD A\n    MOV C, A\n    DAD B\n    XCHG\n    DAD B\n    XCHG\n    POP B\n"+retreat+retreatRight+"    POP PSW\n";
        String endLeft="    PUSH PSW\n    PUSH D\n    MVI D, 0\n    MOV A, B\n    ADD A\n    ADD A\n    MOV E, A\n    DAD D\n    POP D\n"+retreat+"    POP PSW\n";
        return switch(name){
            case "ADD_WORDS","SUB_WORDS","AND_WORDS","OR_WORDS","XOR_WORDS" -> {
                String instruction=switch(name){case "ADD_WORDS"->"ADC C";case "SUB_WORDS"->"SBB C";case "AND_WORDS"->"ANA C";case "OR_WORDS"->"ORA C";default->"XRA C";};
                yield h+":\n    XRA A\n"+h+"_loop:\n    XCHG\n    CALL _VCC_RT_LOAD32\n    MOV C, A\n    XCHG\n    CALL _VCC_RT_LOAD32\n    "+instruction+"\n    CALL _VCC_RT_STORE32\n"+advance+advanceRight+count+"    RET\n";
            }
            case "TEST_WORDS" -> h+":\n    MVI C, 0\n"+h+"_loop:\n    CALL _VCC_RT_LOAD32\n    ORA C\n    MOV C, A\n"+advance+count+"    ORA A\n    RET\n";
            case "FILL_WORDS" -> h+":\n"+h+"_loop:\n    CALL _VCC_RT_STORE32\n"+advance+count+"    RET\n";
            case "NEG_WORDS" -> h+":\n    STC\n"+h+"_loop:\n    CALL _VCC_RT_LOAD32\n    CMA\n    ACI 0\n    CALL _VCC_RT_STORE32\n"+advance+count+"    RET\n";
            case "SHL_WORDS","RCL_WORDS" -> h+":\n"+(name.equals("SHL_WORDS")?"    XRA A\n":"")+h+"_loop:\n    CALL _VCC_RT_LOAD32\n    RAL 1\n    CALL _VCC_RT_STORE32\n"+advance+count+"    RET\n";
            case "SHR_WORDS","SAR_WORDS","RCR_WORDS" -> h+":\n"+endLeft+
                (name.equals("SHR_WORDS")?"    XRA A\n":name.equals("SAR_WORDS")?"    CALL _VCC_RT_LOAD32\n    RLC 1\n":"")+
                h+"_loop:\n    CALL _VCC_RT_LOAD32\n    RAR 1\n    CALL _VCC_RT_STORE32\n"+retreat+count+"    RET\n";
            case "CMP_WORDS","SCMP_WORDS" -> h+":\n"+ends+
                (name.equals("SCMP_WORDS")?"    CALL _VCC_RT_LOAD32\n    MOV C, A\n    XCHG\n    CALL _VCC_RT_LOAD32\n    XCHG\n    XRA C\n    ANI 0x80000000\n    JZ "+h+"_loop\n    MOV A, C\n    ORA A\n    JM "+h+"_less\n    JMP "+h+"_greater\n":"")+
                h+"_loop:\n    XCHG\n    CALL _VCC_RT_LOAD32\n    MOV C, A\n    XCHG\n    CALL _VCC_RT_LOAD32\n    CMP C\n    JC "+h+"_less\n    JNZ "+h+"_greater\n"+retreat+retreatRight+count+
                "    MVI A, 2\n    RET\n"+h+"_less:\n    MVI A, 1\n    RET\n"+h+"_greater:\n    MVI A, 4\n    RET\n";
            default -> throw new IllegalArgumentException("Unknown word helper: "+name);
        };
    }
}
