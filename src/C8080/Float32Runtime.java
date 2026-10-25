package C8080;

import java.util.Set;

/** Generates the binary32 register helper routines used by compiled floating-point code. */
final class Float32Runtime {
    private Float32Runtime() {}
    private static final String ROOT="_VCC_RT_";
    static String routine(String name,RuntimeLibrary dependencies){
        if(name.equals("PACK32")){dependencies.require("LOAD32");dependencies.require("STORE32");return pack();}
        if(name.equals("UNPACK32")){dependencies.require("LOAD32");dependencies.require("STORE32");return unpack();}
        if(name.equals("PACK64")){dependencies.require("LOAD32");dependencies.require("STORE32");return pack64();}
        if(name.equals("UNPACK64")){dependencies.require("LOAD32");dependencies.require("STORE32");return unpack64();}
        if(name.equals("STICKY128")){dependencies.require("LOAD32");dependencies.require("STORE32");return sticky128();}
        if(name.equals("MUL_WIDE32"))return multiplyWide();
        if(name.equals("DIV64_32"))return divideWide();
        if(name.equals("SHR32_TRUNC")||name.equals("SHR32_JAM"))return shift32(name);
        if(name.equals("FCMP32_REG"))return compare();
        if(Set.of("FEQUAL_EQUAL32_REG","FNOT_EQUAL32_REG","FLESS32_REG","FLESS_EQUAL32_REG","FGREATER32_REG","FGREATER_EQUAL32_REG").contains(name)){
            dependencies.require("FCMP32_REG");int mask=switch(name){case "FEQUAL_EQUAL32_REG"->2;case "FNOT_EQUAL32_REG"->13;case "FLESS32_REG"->1;case "FLESS_EQUAL32_REG"->3;case "FGREATER32_REG"->4;default->6;};
            return ROOT+name+":\n    CALL "+ROOT+"FCMP32_REG\n    ANI "+mask+"\n    SUI 1\n    SBB A\n    INR A\n    RET\n";
        }
        if(Set.of("CVT_I32_F32_REG","CVT_U32_F32_REG","CVT_F32_I32_REG","CVT_F32_U32_REG").contains(name)){
            if(name.endsWith("_F32_REG")){dependencies.require("PACK32");dependencies.require("LOAD32");return integerToFloat(name);}
            dependencies.require("SHR32_TRUNC");return floatToInteger(name);
        }
        if(name.equals("FSUB32_REG")){dependencies.require("FADD32_REG");return ROOT+name+":\n    MOV A, C\n    XRI 0x80000000\n    MOV C, A\n    JMP "+ROOT+"FADD32_REG\n";}
        if(!Set.of("FADD32_REG","FMUL32_REG","FDIV32_REG").contains(name))return null;
        dependencies.require("PACK32");dependencies.require("LOAD32");
        if(name.equals("FADD32_REG"))dependencies.require("SHR32_JAM");
        if(name.equals("FMUL32_REG"))dependencies.require("MUL_WIDE32");
        if(name.equals("FDIV32_REG"))dependencies.require("DIV64_32");
        return binary(name);
    }
    private static String read(int offset){return "    LXI H, "+offset+"\n    DAD SP\n    CALL "+ROOT+"LOAD32\n";}
    private static String rotations(String opcode,int count){return "    "+opcode+" "+count+"\n";}
    private static String advance(){return "    INX H\n".repeat(4);}
    private static String pointer(int offset){return read(offset)+"    MOV E, A\n"+advance()+"    CALL "+ROOT+"LOAD32\n    MOV D, A\n    PUSH D\n    POP H\n";}

    private static String pack(){
        String h=ROOT+"PACK32";
        String code=h+":\n    PUSH B\n"+pointer(16)+"    PUSH H\n"+read(56)+"    PUSH PSW\n"+
            "    LXI H, 40\n    DAD SP\n    MOV A, M\n    PUSH PSW\n"+
            read(56)+"    MOV B, A\n"+read(60)+"    MOV C, A\n"+read(64)+"    MOV D, A\n"+read(68)+"    MOV E, A\n"+
            "    POP PSW\n    MOV H, A\n    POP PSW\n    MOV L, A\n";
        code+="""
    MOV A, B
    ORA C
    ORA D
    ORA E
    JZ $zero
$low:
    MOV A, C
    ORA D
    ORA E
    JNZ $high
    MOV A, B
    CPI 0x04000000
    JNC $high
    ADD A
    MOV B, A
    MOV A, C
    RAL 1
    MOV C, A
    MOV A, D
    RAL 1
    MOV D, A
    MOV A, E
    RAL 1
    MOV E, A
    DCR L
    JMP $low
$high:
    MOV A, C
    ORA D
    ORA E
    JNZ $reduce
    MOV A, B
    CPI 0x08000000
    JC $normalized
$reduce:
    CALL $right
    INR L
    JMP $high
$normalized:
    MOV A, L
    ADI 153
    MOV L, A
    ORA A
    JM $denormal
    JZ $denormal
    JMP $round
$denormal:
    MVI A, 1
    SUB L
    MOV L, A
    CPI 128
    JNC $tiny
$denormal_loop:
    CALL $right
    DCR L
    JNZ $denormal_loop
    JMP $round
$tiny:
    MVI B, 1
    MVI L, 0
$round:
    MOV A, B
    ANI 7
    CPI 4
    JC $retained
    JNZ $up
    MOV A, B
    ANI 8
    JZ $retained
$up:
    MOV A, B
    ADI 8
    MOV B, A
$retained:
    MOV A, B
    RRC 3

    ANI 0x1fffffff
    MOV B, A
    CPI 0x01000000
    JC $subnormal
    RRC 1
    ANI 0x7fffffff
    MOV B, A
    INR L
$subnormal:
    MOV A, L
    ORA A
    JNZ $encoded
    MOV A, B
    CPI 0x00800000
    JC $encoded
    MVI L, 1
$encoded:
    MOV A, L
    CPI 255
    JNC $infinity
    RRC 9

    ANI 0x7f800000
    MOV C, A
    MOV A, B
    ANI 0x007fffff
    ORA C
    MOV B, A
    MOV A, H
    RRC 1
    ORA B
    JMP $write
$infinity:
    MOV A, H
    RRC 1
    ORI 0x7f800000
    JMP $write
$zero:
    MOV A, H
    RRC 1
$write:
    POP H
    CALL _VCC_RT_STORE32
    POP B
    RET
$right:
    MOV A, E
    ORA A
    RAR 1
    MOV E, A
    MOV A, D
    RAR 1
    MOV D, A
    MOV A, C
    RAR 1
    MOV C, A
    MOV A, B
    RAR 1
    JNC $clean
    ORI 1
$clean:
    MOV B, A
    RET
""";
        return code.replace("$",h+"_");
    }

    private static String unpack(){
        String h=ROOT+"UNPACK32";
        String code=h+":\n    PUSH B\n"+read(24)+"    MOV B, A\n"+rotations("RLC",9)+"    ANI 255\n    MOV C, A\n    MOV A, B\n    ANI 0x007fffff\n    MOV D, A\n    MOV A, C\n    ORA A\n    JZ "+h+"_sub\n    MOV A, D\n    ORI 0x00800000\n    MOV D, A\n"+h+"_sub:\n    MOV A, C\n    ORA A\n    JNZ "+h+"_exponent\n    MVI A, 1\n"+h+"_exponent:\n    SUI 150\n    MOV E, A\n    PUSH D\n"+pointer(24)+"    POP D\n    MOV A, B\n    CALL "+ROOT+"STORE32\n"+advance()+"    MOV A, B\n    RLC 1\n    MVI A, 0\n    ACI 0\n    MOV M, A\n    INX H\n    MOV A, D\n    CALL "+ROOT+"STORE32\n"+advance()+"    MVI A, 0\n";
        for(int n=0;n<3;n++)code+="    CALL "+ROOT+"STORE32\n"+advance();
        code+="    MOV A, E\n    CALL "+ROOT+"STORE32\n"+advance()+"    MOV A, C\n    CALL "+ROOT+"STORE32\n"+advance()+"    MVI A, 0\n    CALL "+ROOT+"STORE32\n";
        code+="""
    MOV A, C
    CPI 255
    JNZ $finite
    MOV A, B
    ANI 0x007fffff
    JZ $infinity
    MVI M, 1
    JMP $done
$infinity:
    INX H
    MVI M, 1
    JMP $done
$finite:
    MOV A, B
    ANI 0x7fffffff
    JNZ $done
    INX H
    INX H
    MVI M, 1
$done:
    POP B
    RET
""";
        return code.replace("$",h+"_");
    }
    private static String unpack64(){
        String h=ROOT+"UNPACK64",code=h+":\n    PUSH B\n"+read(24)+"    MOV B, A\n"+read(28)+"    MOV C, A\n"+rotations("RLC",12)+
            "    ANI 2047\n    MOV D, A\n    MOV A, C\n    ANI 0x000fffff\n    MOV E, A\n    MOV A, D\n    ORA A\n    JZ "+h+"_sub\n    MOV A, E\n    ORI 0x00100000\n    MOV E, A\n"+h+"_sub:\n    MOV A, D\n    ORA A\n    JNZ "+h+"_exponent\n    MVI A, 1\n"+h+"_exponent:\n    SUI 1075\n    PUSH PSW\n    PUSH D\n"+pointer(32)+"    POP D\n    POP PSW\n    PUSH PSW\n    MOV A, B\n    CALL "+ROOT+"STORE32\n"+advance()+"    MOV A, C\n    CALL "+ROOT+"STORE32\n"+advance()+
            "    MOV A, C\n    RLC 1\n    MVI A, 0\n    ACI 0\n    MOV M, A\n    INX H\n    MOV A, B\n    CALL "+ROOT+"STORE32\n"+advance()+"    MOV A, E\n    CALL "+ROOT+"STORE32\n"+advance()+"    MVI A, 0\n";
        for(int n=0;n<2;n++)code+="    CALL "+ROOT+"STORE32\n"+advance();
        code+="    POP PSW\n    CALL "+ROOT+"STORE32\n"+advance()+"    MOV A, D\n    CALL "+ROOT+"STORE32\n"+advance()+"    MVI A, 0\n    CALL "+ROOT+"STORE32\n";
        code+="""
    MOV A, D
    CPI 2047
    JNZ $finite
    MOV A, C
    ANI 0x000fffff
    ORA B
    JZ $infinity
    MVI M, 1
    JMP $done
$infinity:
    INX H
    MVI M, 1
    JMP $done
$finite:
    MOV A, C
    ANI 0x7fffffff
    ORA B
    JNZ $done
    INX H
    INX H
    MVI M, 1
$done:
    POP B
    RET
""";
        return code.replace("$",h+"_");
    }
    private static String pack64(){
        String h=ROOT+"PACK64",code=pack().replace(ROOT+"PACK32",h);
        code=code.replace("    MOV A, C\n    ORA D\n    ORA E\n    JNZ "+h+"_high\n    MOV A, B\n    CPI 0x04000000\n    JNC "+h+"_high\n    ADD A", "    MOV A, D\n    ORA E\n    JNZ "+h+"_high\n    MOV A, C\n    CPI 0x00800000\n    JNC "+h+"_high\n    MOV A, B\n    ADD A");
        code=code.replace("    MOV A, C\n    ORA D\n    ORA E\n    JNZ "+h+"_reduce\n    MOV A, B\n    CPI 0x08000000", "    MOV A, D\n    ORA E\n    JNZ "+h+"_reduce\n    MOV A, C\n    CPI 0x01000000");
        code=code.replace("    ADI 153\n","    ADI 1078\n").replace(h+"_tiny:\n    MVI B, 1\n    MVI L, 0",h+"_tiny:\n    MVI B, 1\n    MVI C, 0\n    MVI D, 0\n    MVI E, 0\n    MVI L, 0");
        String right64="    MOV A, C\n    ORA A\n    RAR 1\n    MOV C, A\n    MOV A, B\n    RAR 1\n    MOV B, A\n";
        String round="""
$round:
    MOV A, B
    ANI 7
    CPI 4
    JC $retained
    JNZ $up
    MOV A, B
    ANI 8
    JZ $retained
$up:
    MOV A, B
    ADI 8
    MOV B, A
    MOV A, C
    ACI 0
    MOV C, A
$retained:
"""+right64.repeat(3)+"""
    MOV A, C
    CPI 0x00200000
    JC $subnormal
"""+right64+"""
    INR L
$subnormal:
    MOV A, L
    ORA A
    JNZ $encoded
    MOV A, C
    CPI 0x00100000
    JC $encoded
    MVI L, 1
$encoded:
    MOV A, L
    CPI 2047
    JNC $infinity
"""+rotations("RRC",12)+"""
    ANI 0x7ff00000
    MOV D, A
    MOV A, C
    ANI 0x000fffff
    ORA D
    MOV C, A
    MOV A, H
    RRC 1
    ORA C
    MOV C, A
    JMP $write
$infinity:
    MOV A, H
    RRC 1
    ORI 0x7ff00000
    MOV C, A
    MVI B, 0
    JMP $write
$zero:
    MOV A, H
    RRC 1
    MOV C, A
    MVI B, 0
$write:
    POP H
    MOV A, B
    CALL _VCC_RT_STORE32
"""+advance()+"    MOV A, C\n    CALL "+ROOT+"STORE32\n    POP B\n    RET\n";
        return code.substring(0,code.indexOf(h+"_round:"))+round.replace("$",h+"_")+code.substring(code.indexOf(h+"_right:"));
    }
    private static String sticky128(){
        String h=ROOT+"STICKY128",code=h+":\n    PUSH B\n"+pointer(16)+"    PUSH H\n"+read(48)+"    PUSH PSW\n"+
            read(40)+"    MOV B, A\n"+read(44)+"    MOV C, A\n"+read(48)+"    MOV D, A\n"+read(52)+"    MOV E, A\n    POP PSW\n    MOV H, A\n    MVI L, 0\n";
        code+="""
    CPI 128
    JC $test
    MOV A, B
    ORA C
    ORA D
    ORA E
    JZ $clear
    MVI L, 1
$clear:
    MVI B, 0
    MVI C, 0
    MVI D, 0
    MVI E, 0
    JMP $done
$test:
    MOV A, H
    ORA A
    JZ $done
$loop:
    MOV A, B
    ANI 1
    ORA L
    MOV L, A
    MOV A, E
    ORA A
    RAR 1
    MOV E, A
    MOV A, D
    RAR 1
    MOV D, A
    MOV A, C
    RAR 1
    MOV C, A
    MOV A, B
    RAR 1
    MOV B, A
    DCR H
    JNZ $loop
$done:
    MOV A, B
    ORA L
    MOV B, A
    POP H
""";
        for(String register:new String[]{"B","C","D","E"})code+="    MOV A, "+register+"\n    CALL "+ROOT+"STORE32\n"+advance();
        return (code+"    POP B\n    RET\n").replace("$",h+"_");
    }
    private static String multiplyWide(){return """
_VCC_RT_MUL_WIDE32:
    MVI D, 0
    MVI E, 0
    MVI H, 32
    MVI L, 0
_VCC_RT_MUL_WIDE32_loop:
    MOV A, C
    ANI 1
    JZ _VCC_RT_MUL_WIDE32_skip
    MOV A, E
    ADD B
    MOV E, A
    MOV A, D
    ADC L
    MOV D, A
_VCC_RT_MUL_WIDE32_skip:
    MOV A, B
    ADD A
    MOV B, A
    MOV A, L
    RAL 1
    MOV L, A
    MOV A, C
    ORA A
    RAR 1
    MOV C, A
    DCR H
    JNZ _VCC_RT_MUL_WIDE32_loop
    RET
""";}
    private static String divideWide(){return """
_VCC_RT_DIV64_32:
    MOV L, C
    MVI B, 0
    MVI C, 0
    MVI H, 64
_VCC_RT_DIV64_32_loop:
    MOV A, E
    ADD A
    MOV E, A
    MOV A, D
    RAL 1
    MOV D, A
    MOV A, C
    RAL 1
    MOV C, A
    JC _VCC_RT_DIV64_32_subtract
    CMP L
    JC _VCC_RT_DIV64_32_zero
_VCC_RT_DIV64_32_subtract:
    SUB L
    MOV C, A
    MOV A, B
    ADD A
    ORI 1
    MOV B, A
    JMP _VCC_RT_DIV64_32_next
_VCC_RT_DIV64_32_zero:
    MOV A, B
    ADD A
    MOV B, A
_VCC_RT_DIV64_32_next:
    DCR H
    JNZ _VCC_RT_DIV64_32_loop
    MOV E, C
    MOV A, B
    RET
""";}
    private static String shift32(String name){
        String h=ROOT+name;boolean jam=name.endsWith("JAM");
        return h+":\n    PUSH PSW\n    MOV A, E\n    CPI 32\n    JC "+h+"_small\n    POP PSW\n"+
            (jam?"    ORA A\n    RZ\n    MVI A, 1\n":"    MVI A, 0\n")+"    RET\n"+h+"_small:\n    ORA A\n    JNZ "+h+"_start\n    POP PSW\n    RET\n"+h+"_start:\n    POP PSW\n"+h+"_loop:\n    ORA A\n    RAR 1\n"+
            (jam?"    JNC "+h+"_clean\n    ORI 1\n"+h+"_clean:\n":"")+"    DCR E\n    JNZ "+h+"_loop\n    RET\n";
    }
    private static String integerToFloat(String name){
        String h=ROOT+name;
        String body=h+":\n    MVI H, 0\n    MOV A, B\n";
        if(name.startsWith("CVT_I"))body+="    ORA A\n    JP "+h+"_positive\n    MVI H, 0x80000000\n    CMA\n    ADI 1\n"+h+"_positive:\n";
        return body+"    MOV E, A\n    MVI D, 0\n    MVI L, 0\n"+packFromRegisters();
    }
    private static String packFromRegisters(){

        return "    PUSH H\n    MVI B, 0\n    MOV C, L\n    PUSH B\n    LXI B, 0\n    PUSH B\n    PUSH D\n"+
            "    LXI H, 28\n    DAD SP\n    CALL _VCC_RT_LOAD32\n    RLC 1\n    ANI 1\n    MOV C, A\n    MVI B, 0\n    PUSH B\n    LXI H, 32\n    DAD SP\n    PUSH H\n    CALL _VCC_RT_PACK32\n"+
            "    LXI H, 40\n    DAD SP\n    CALL _VCC_RT_LOAD32\n    LXI H, 48\n    DAD SP\n    SPHL\n    RET\n";
    }
    private static String floatToInteger(String name){
        String h=ROOT+name,body=h+":\n    MOV A, B\n    ANI 0x80000000\n    MOV H, A\n    MOV A, B\n"+rotations("RLC",9)+
            "    ANI 255\n    CPI 255\n    JZ "+h+"_zero\n    MOV D, A\n    ORA A\n    JZ "+h+"_sub\n    MOV A, B\n    ORI 0x00800000\n    MOV B, A\n"+h+"_sub:\n    MOV A, B\n    ANI 0x00ffffff\n    MOV B, A\n    MOV A, D\n    ORA A\n    JNZ "+h+"_exponent\n    MVI A, 1\n"+h+"_exponent:\n    SUI 150\n    MOV L, A\n    ORA A\n    JM "+h+"_right\n    CPI 32\n    JNC "+h+"_zero\n    ORA A\n    JZ "+h+"_sign\n"+h+"_left:\n    MOV A, B\n    ADD A\n    MOV B, A\n    DCR L\n    JNZ "+h+"_left\n    JMP "+h+"_sign\n"+h+"_right:\n    MVI A, 0\n    SUB L\n    MOV E, A\n    MOV A, B\n    CALL _VCC_RT_SHR32_TRUNC\n    MOV B, A\n"+h+"_sign:\n    MOV A, H\n    ORA A\n    JP "+h+"_positive\n    MOV A, B\n    CMA\n    ADI 1\n    RET\n"+h+"_positive:\n    MOV A, B\n    RET\n"+h+"_zero:\n    MVI A, 0\n    RET\n";
        return body;
    }
    private static String compare(){
        String h=ROOT+"FCMP32_REG";
        return (h+":\n"+nanChecks(h)+"""
    MOV A, B
    ORA C
    ANI 0x7fffffff
    JZ $equal
    MOV A, B
    CMP C
    JZ $equal
    XRA C
    ANI 0x80000000
    JZ $same
    MOV A, B
    ORA A
    JM $less
    JMP $greater
$same:
    MOV A, B
    ORA A
    JM $negative
    CMP C
    JC $less
    JMP $greater
$negative:
    CMP C
    JC $greater
    JMP $less
$less:
    MVI A, 1
    RET
$equal:
    MVI A, 2
    RET
$greater:
    MVI A, 4
    RET
$nan:
    MVI A, 8
    RET
""").replace("$",h+"_");
    }
    private static String nanChecks(String h){
        String code="";
        for(String reg:new String[]{"B","C"})code+="    MOV A, "+reg+"\n    ANI 0x7f800000\n    CPI 0x7f800000\n    JNZ "+h+"_notnan_"+reg+"\n    MOV A, "+reg+"\n    ANI 0x007fffff\n    JNZ "+h+"_nan\n"+h+"_notnan_"+reg+":\n";
        return code;
    }
    private static String binary(String name){
        String h=ROOT+name;boolean add=name.startsWith("FADD"),multiply=name.startsWith("FMUL");
        String code=h+":\n"+nanChecks(h)+"    MOV A, B\n"+rotations("RLC",9)+"    ANI 255\n    MOV D, A\n    MOV A, C\n"+rotations("RLC",9)+"    ANI 255\n    MOV E, A\n";
        if(add)code+="    MOV A, B\n    ANI 0x80000000\n    MOV H, A\n    MOV A, B\n    XRA C\n    ANI 0x80000000\n    MOV L, A\n";
        else code+="    MOV A, B\n    XRA C\n    ANI 0x80000000\n    MOV H, A\n";
        code+="    MOV A, D\n    CPI 255\n    JNZ "+h+"_right_inf\n";
        if(add)code+="    MOV A, E\n    CPI 255\n    JNZ "+h+"_left_inf\n    MOV A, L\n    ORA A\n    JNZ "+h+"_nan\n"+h+"_left_inf:\n    MOV A, B\n    RET\n";
        else if(multiply)code+="    MOV A, C\n    ANI 0x7fffffff\n    JZ "+h+"_nan\n    JMP "+h+"_infinity\n";
        else code+="    MOV A, E\n    CPI 255\n    JZ "+h+"_nan\n    JMP "+h+"_infinity\n";
        code+=h+"_right_inf:\n    MOV A, E\n    CPI 255\n    JNZ "+h+"_finite\n";
        if(add)code+="    MOV A, C\n    RET\n";
        else if(multiply)code+="    MOV A, B\n    ANI 0x7fffffff\n    JZ "+h+"_nan\n    JMP "+h+"_infinity\n";
        else code+="    JMP "+h+"_zero\n";
        code+=h+"_finite:\n";
        if(!add&&!multiply)code+="    MOV A, C\n    ANI 0x7fffffff\n    JNZ "+h+"_denominator\n    MOV A, B\n    ANI 0x7fffffff\n    JZ "+h+"_nan\n    JMP "+h+"_infinity\n"+h+"_denominator:\n    MOV A, B\n    ANI 0x7fffffff\n    JZ "+h+"_zero\n";
        for(String[] operand:new String[][]{{"B","D"},{"C","E"}}){String m=operand[0],e=operand[1];code+="    MOV A, "+m+"\n    ANI 0x007fffff\n    MOV "+m+", A\n    MOV A, "+e+"\n    ORA A\n    JZ "+h+"_sub_"+m+"\n    MOV A, "+m+"\n    ORI 0x00800000\n    MOV "+m+", A\n    JMP "+h+"_ready_"+m+"\n"+h+"_sub_"+m+":\n    MVI "+e+", 1\n"+h+"_ready_"+m+":\n";}
        if(add)code+=addFinite(h);
        else if(multiply)code+="    MOV A, D\n    ADD E\n    SUI 300\n    MOV L, A\n    PUSH H\n    CALL _VCC_RT_MUL_WIDE32\n    POP H\n";
        else code+=divideFinite(h);
        code+=packFromRegisters();
        code+=h+"_nan:\n    MVI A, 0x7fc00000\n    RET\n"+h+"_infinity:\n    MOV A, H\n    ORI 0x7f800000\n    RET\n"+h+"_zero:\n    MOV A, H\n    RET\n";
        return code;
    }
    private static String addFinite(String h){return ("""
    MOV A, B
    RLC 3

    MOV B, A
    MOV A, C
    RLC 3

    MOV C, A
    MOV A, D
    CMP E
    JNC $aligned
    MOV A, B
    MOV B, C
    MOV C, A
    MOV A, D
    MOV D, E
    MOV E, A
    MOV A, H
    XRA L
    MOV H, A
$aligned:
    MOV A, D
    SUB E
    MOV E, A
    MOV A, C
    CALL _VCC_RT_SHR32_JAM
    MOV C, A
    MOV A, L
    ORA A
    JNZ $opposite
    MOV A, B
    ADD C
    MOV B, A
    JMP $mantissa
$opposite:
    MOV A, B
    CMP C
    JNC $subtract
    MOV A, H
    XRI 0x80000000
    MOV H, A
    MOV A, C
    SUB B
    MOV B, A
    JMP $cancel
$subtract:
    SUB C
    MOV B, A
$cancel:
    MOV A, B
    ORA A
    JNZ $mantissa
    MVI H, 0
$mantissa:
    MOV A, D
    SUI 153
    MOV L, A
    MOV E, B
    MVI D, 0
""").replace("$",h+"_");}
    private static String divideFinite(String h){String code="";
        for(String[] part:new String[][]{{"B","D"},{"C","E"}}){String m=part[0],e=part[1];code+=h+"_normalize_"+m+":\n    MOV A, "+m+"\n    ANI 0x00800000\n    JNZ "+h+"_normal_"+m+"\n    MOV A, "+m+"\n    ADD A\n    MOV "+m+", A\n    DCR "+e+"\n    JMP "+h+"_normalize_"+m+"\n"+h+"_normal_"+m+":\n";}
        return code+"    MOV A, D\n    SUB E\n    SUI 27\n    MOV L, A\n    PUSH H\n    MOV A, B\n"+rotations("RRC",5)+"    ANI 0x07ffffff\n    MOV D, A\n    MOV A, B\n"+rotations("RRC",5)+"    ANI 0xf8000000\n    MOV E, A\n    CALL _VCC_RT_DIV64_32\n    MOV B, A\n    MOV A, E\n    ORA A\n    JZ "+h+"_exact\n    MOV A, B\n    ORI 1\n    MOV B, A\n"+h+"_exact:\n    POP H\n    MOV E, B\n    MVI D, 0\n";
    }
}
