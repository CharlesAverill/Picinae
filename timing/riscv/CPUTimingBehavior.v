Require Import NArith.

Module Type CPUTimingBehavior.
    (* === Instruction Timings === *)
    Parameter
        (* ==== I ISA Extension ==== *)
        (* ALU *)
            tadd taddi tslt tslti tsltu tsltiu
            txor txori tor tori tand tandi tsub tlui
            tauipc
        (* Branches *)
            (* taken *)
                ttbeq ttbne ttblt ttbge ttbltu ttbgeu
            (* not taken *)
                tfbeq tfbne tfblt tfbge tfbltu tfbgeu
        (* Jump/call *)
            tjal tjalr
        (* Load/store *)
            tlb tlh tlw tlbu tlhu tsb tsh tsw
        (* Data fence *)
            tfence
        (* System *)
            tecall tebreak tmret twfi

        (* ==== M ISA Extension ==== *)
        (* Multiplication *)
            tmul tmulh tmulhsu tmulhu
        (* Division *)
            tdiv tdivu trem tremu

        (* ==== Zbb ISA Extension ==== *)
        (* Logic with negate *)
            tandn torn txnor
        (* Integer max/min *)
            tmin tminu tmax tmaxu
        (* Sign/zero extension *)
            tsext_b tsext_h tzext
        (* OR-combine *)
            torc_b
        (* Byte-reverse *)
            trev8
    : N.

    (* These instr times need to be N->N because they could depend on state values *)
    Parameter
        (* ==== I ISA Extension ==== *)
        (* ALU Shifts *)
            tsll tslli tsrl tsrli tsra tsrai

        (* ==== Zbb ISA Extension ==== *)
        (* Bit count *)
            tclz tctz tcpop
        (* Bitwise rotation *)
            trol tror trori
    : N -> N.
End CPUTimingBehavior.
