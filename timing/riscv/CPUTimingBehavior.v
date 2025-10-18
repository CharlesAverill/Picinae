Require Import NArith.

Module Type CPUTimingBehavior.
    (* === Instruction Timings === *)

    (* ==== I ISA Extension ==== *)
    (* ALU: rd rs1 rs2 *)
    Parameter
        tadd tsub tslt tsltu txor tor tand : N -> N -> N.
    (* ALU (immediate): rd rs1 imm *)
    Parameter
        taddi tslti tsltiu txori tori tandi : N -> N -> N.
    (* Upper immediates: rd imm *)
    Parameter
        tlui tauipc : N -> N.

    (* Branches: rs1 rs2 imm *)
    Parameter
        (* taken *)
        ttbeq ttbne ttblt ttbge ttbltu ttbgeu
        (* not taken *)
        tfbeq tfbne tfblt tfbge tfbltu tfbgeu :
            N -> N -> N.

    (* Jump/call *)
    Parameter
        (* jal: rd imm *)
        tjal : N -> N.
    Parameter
        (* jalr: rd rs1 imm *)
        tjalr : N -> N -> N.

    (* Load/store *)
    Parameter
        (* load: rd rs1 imm *)
        tlb tlh tlw tlbu tlhu
        (* store: rs1 rs2 imm *)
        tsb tsh tsw : N -> N -> N.

    (* Data fence: no operands *)
    Parameter tfence : N.

    (* System: no operands or immediate *)
    Parameter
        tecall tebreak tmret twfi : N.

    (* ==== M ISA Extension ==== *)
    (* Multiplication/division: rd rs1 rs2 *)
    Parameter
        tmul tmulh tmulhsu tmulhu
        tdiv tdivu trem tremu : N -> N -> N.

    (* ==== Zbb ISA Extension ==== *)
    (* Logic with negate: rd rs1 rs2 *)
    Parameter
        tandn torn txnor : N -> N -> N.
    (* Integer max/min: rd rs1 rs2 *)
    Parameter
        tmin tminu tmax tmaxu : N -> N -> N.
    (* Sign/zero extension: rd rs1 *)
    Parameter
        tsext_b tsext_h tzext : N -> N.
    (* OR-combine: rd rs1 *)
    Parameter torc_b : N -> N.
    (* Byte-reverse: rd rs1 *)
    Parameter trev8 : N -> N.

    (* ==== Zicsr ISA Extension ==== *)
    (* System CSR access: rd rs1 csr *)
    Parameter
        tcsrrw tcsrrs tcsrrc : N -> N -> N.
    (* System CSR immediate: rd csr imm *)
    Parameter
        tcsrrwi tcsrrsi tcsrrci : N -> N -> N.

    (* ==== I ISA Extension ==== *)
    (* ALU Shifts: rd rs1 (rs2 or imm) *)
    Parameter
        tsll tsrl tsra
        tslli tsrli tsrai : N -> N -> N.

    (* ==== Zbb ISA Extension ==== *)
    (* Bit count: rd rs1 *)
    Parameter
        tclz tctz tcpop : N -> N.
    (* Bitwise rotation: rd rs1 (rs2 or imm) *)
    Parameter
        trol tror
        trori : N -> N -> N.
End CPUTimingBehavior.
