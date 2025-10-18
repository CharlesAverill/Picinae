Require Import CPUTimingBehavior.
Require Import NArith.
Require Import Picinae_core.
Open Scope N.

(* https://stnolting.github.io/neorv32/#_processor_top_entity_generics *)
Module Type NEORV32Config.
    (* The clock frequency of the processor’s clk_i input port in Hertz *)
    Parameter CLOCK_FREQUENCY : N.
    (* Implement fast but large full-parallel barrel shifters *)
    Parameter CPU_FAST_SHIFT_EN : bool.
    (* Implement fast but large full-parallel multipliers *)
    Parameter CPU_FAST_MUL_EN : bool.
    (* Implement the instruction cache *)
    Parameter ICACHE_EN : bool.
    (* Implement the data cache *)
    Parameter DCACHE_EN : bool.
End NEORV32Config.

(* https://stnolting.github.io/neorv32/#_instruction_sets_and_extensions *)
Module NEORV32 (cfg : NEORV32Config) <: CPUTimingBehavior.
    (* Latency Definitions *)
    Definition T_shift_latency (offset : N) : N :=
        if cfg.CPU_FAST_SHIFT_EN then
            1
        else
            offset.

    Definition T_mul_latency : N :=
        if cfg.CPU_FAST_MUL_EN then
            1
        else
            32.

    Parameter T_data_latency : N.
    Parameter T_inst_latency : N.

    (* ==== I ISA Extension ==== *)
    (* ALU *)
    Definition tadd    (_ _ : N) := 2.
    Definition taddi   (_ _ : N) := 2.
    Definition tslt    (_ _ : N) := 2.
    Definition tslti   (_ _ : N) := 2.
    Definition tsltu   (_ _ : N) := 2.
    Definition tsltiu  (_ _ : N) := 2.
    Definition txor    (_ _ : N) := 2.
    Definition txori   (_ _ : N) := 2.
    Definition tor     (_ _ : N) := 2.
    Definition tori    (_ _ : N) := 2.
    Definition tand    (_ _ : N) := 2.
    Definition tandi   (_ _ : N) := 2.
    Definition tsub    (_ _ : N) := 2.
    Definition tlui    (_ : N) := 2.
    Definition tauipc  (_ : N) := 2.

    (* ALU Shifts *)
    Definition tsll    (_ offset : N) := 3 + T_shift_latency offset.
    Definition tslli   (_ offset : N) := 3 + T_shift_latency offset.
    Definition tsrl    (_ offset : N) := 3 + T_shift_latency offset.
    Definition tsrli   (_ offset : N) := 3 + T_shift_latency offset.
    Definition tsra    (_ offset : N) := 3 + T_shift_latency offset.
    Definition tsrai   (_ offset : N) := 3 + T_shift_latency offset.

    (* Branches *)
    Definition ttbeq   (_ _ : N) := 5 + T_inst_latency.
    Definition ttbne   (_ _ : N) := 5 + T_inst_latency.
    Definition ttblt   (_ _ : N) := 5 + T_inst_latency.
    Definition ttbge   (_ _ : N) := 5 + T_inst_latency.
    Definition ttbltu  (_ _ : N) := 5 + T_inst_latency.
    Definition ttbgeu  (_ _ : N) := 5 + T_inst_latency.

    Definition tfbeq   (_ _ : N) := 3.
    Definition tfbne   (_ _ : N) := 3.
    Definition tfblt   (_ _ : N) := 3.
    Definition tfbge   (_ _ : N) := 3.
    Definition tfbltu  (_ _ : N) := 3.
    Definition tfbgeu  (_ _ : N) := 3.

    (* Jump/call *)
    Definition tjal    (_ : N) := 5 + T_inst_latency.
    Definition tjalr   (_ _ : N) := 5 + T_inst_latency.

    (* Load/store *)
    Definition tlb     (_ _ : N) := 4 + T_data_latency.
    Definition tlh     (_ _ : N) := 4 + T_data_latency.
    Definition tlw     (_ _ : N) := 4 + T_data_latency.
    Definition tlbu    (_ _ : N) := 4 + T_data_latency.
    Definition tlhu    (_ _ : N) := 4 + T_data_latency.
    Definition tsb     (_ _ : N) := 4 + T_data_latency.
    Definition tsh     (_ _ : N) := 4 + T_data_latency.
    Definition tsw     (_ _ : N) := 4 + T_data_latency.

    (* Data fence *)
    Definition tfence  : N := 6 + T_data_latency.

    (* System *)
    Definition tecall  : N := 7 + T_inst_latency.
    Definition tebreak : N := 7 + T_inst_latency.
    Definition tmret   : N := 7 + T_inst_latency.
    Definition twfi    : N := 7 + T_inst_latency.

    (* ==== M ISA Extension ==== *)
    (* Multiplication *)
    Definition tmul    (_ _ : N) := 3 + T_mul_latency.
    Definition tmulh   (_ _ : N) := 3 + T_mul_latency.
    Definition tmulhsu (_ _ : N) := 3 + T_mul_latency.
    Definition tmulhu  (_ _ : N) := 3 + T_mul_latency.

    (* Division *)
    Definition tdiv    (_ _ : N) := 3 + 32.
    Definition tdivu   (_ _ : N) := 3 + 32.
    Definition trem    (_ _ : N) := 3 + 32.
    Definition tremu   (_ _ : N) := 3 + 32.

    (* ==== Zbb ISA Extension ==== *)
    (* Logic with negate *)
    Definition tandn   (_ _ : N) := 4.
    Definition torn    (_ _ : N) := 4.
    Definition txnor   (_ _ : N) := 4.

    (* Bit count *)
    Definition tclz    (val : N) := 4 + T_shift_latency (clz val 32).
    Definition tctz    (val : N) := 4 + T_shift_latency (ctz val 32).
    Definition tcpop   (val : N) := 4 + T_shift_latency 32.

    (* Integer max/min *)
    Definition tmin    (_ _ : N) := 4.
    Definition tminu   (_ _ : N) := 4.
    Definition tmax    (_ _ : N) := 4.
    Definition tmaxu   (_ _ : N) := 4.

    (* Sign/zero extension *)
    Definition tsext_b (_ : N) := 4.
    Definition tsext_h (_ : N) := 4.
    Definition tzext   (_ : N) := 4.

    (* Bitwise rotation *)
    Definition trol    (_ rot_factor : N) := 4 + T_shift_latency rot_factor.
    Definition tror    (_ rot_factor : N) := 4 + T_shift_latency rot_factor.
    Definition trori   (rot_factor _ : N) := 4 + T_shift_latency rot_factor.

    (* OR-combine *)
    Definition torc_b  (_ : N) := 4.

    (* Byte-reverse *)
    Definition trev8   (_ : N) := 4.

    (* ==== Zicsr ISA Extension ==== *)
    (* System *)
    Definition tcsrrw  (_ _ : N) := 3.
    Definition tcsrrwi (_ _ : N) := 3.
    Definition tcsrrs  (_ _ : N) := 3.
    Definition tcsrrsi (_ _ : N) := 3.
    Definition tcsrrc  (_ _ : N) := 3.
    Definition tcsrrci (_ _ : N) := 3.
End NEORV32.

(* https://github.com/stnolting/neorv32/blob/main/rtl/test_setups/neorv32_test_setup_bootloader.vhd *)
(* https://github.com/stnolting/neorv32-setups/blob/main/quartus/terasic-cyclone-V-gx-starter-kit-test-setup/create_project.tcl *)
Module NEORV32BaseConfig <: NEORV32Config.
    (* 50 MHz *)
    Definition CLOCK_FREQUENCY : N := 50000000.
    Definition CPU_FAST_SHIFT_EN : bool := false.
    Definition CPU_FAST_MUL_EN : bool := false.
    Definition ICACHE_EN : bool := false.
    Definition DCACHE_EN : bool := false.
End NEORV32BaseConfig.

Module NEORV32Base := NEORV32 NEORV32BaseConfig.
