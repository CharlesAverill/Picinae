From Picinae Require Import Picinae_riscv.
Require Import NArith ZArith.

Definition resolve_jalr_addr (offset : Z) (a : addr) : addr :=
        N.clearbit (ofZ 32 (Z.add offset (toZ 32 a))) 0.

Definition add_signed_offset (a : N) (o : Z) : N :=
    ofZ 32 (Z.add (toZ 32 a) o).

Definition add_signed_offset' (a o : N) : N :=
    ofZ 32 (Z.add (toZ 32 a) (toZ 32 o)).

Definition reg s n := match n with 0 => 0 | _ => s (rv_varid n) end.

Module Type CPUTimingBehavior.
    Parameter cache : Type.
    Parameter cache_step : store -> cache -> addr -> cache.

    (* === Instruction Timings === *)
    Parameter
        (* ==== I ISA Extension ==== *)
        (* ALU *)
            tadd taddi tslt tslti tsltu tsltiu
            txor txori tor tori tand tandi tsub tlui
            tauipc : N.
    Parameter
        (* Branches *)
            (* taken *)
                ttbeq ttbne ttblt ttbge ttbltu ttbgeu
            (* not taken *)
                tfbeq tfbne tfblt tfbge tfbltu tfbgeu
        (* Jump/call *)
            tjal tjalr : cache -> addr -> N.
    Parameter
        (* Load/store *)
            tlb tlh tlw tlbu tlhu tsb tsh tsw
            : cache -> N -> N.
    Parameter
        (* Data fence *)
            tfence tfencei : cache -> N.
    Parameter
        (* System *)
            tecall tebreak tmret : cache -> N. 
    Parameter 
        (* System *) 
            twfi
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

        (* ==== Zicsr ISA Extension ==== *)
        (* System *)
            tcsrrw tcsrrwi
            tcsrrs tcsrrsi
            tcsrrc tcsrrci
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
