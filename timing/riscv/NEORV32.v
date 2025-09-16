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
    Definition tadd := 2.
    Definition taddi := 2.
    Definition tslt := 2.
    Definition tslti := 2.
    Definition tsltu := 2.
    Definition tsltiu := 2.
    Definition txor := 2.
    Definition txori := 2.
    Definition tor := 2.
    Definition tori := 2.
    Definition tand := 2.
    Definition tandi := 2.
    Definition tsub := 2.
    Definition tlui := 2.
    Definition tauipc := 2.
    (* ALU Shifts *)
    Definition tsll (offset : N) := 
        3 + T_shift_latency offset.
    Definition tslli (offset : N) := 
        3 + T_shift_latency offset.
    Definition tsrl (offset : N) := 
        3 + T_shift_latency offset.
    Definition tsrli (offset : N) := 
        3 + T_shift_latency offset.
    Definition tsra (offset : N) := 
        3 + T_shift_latency offset.
    Definition tsrai (offset : N) := 
        3 + T_shift_latency offset.
    (* Branches *)
    (* taken *)
    Definition ttbeq := 5 + T_inst_latency.
    Definition ttbne := 5 + T_inst_latency.
    Definition ttblt := 5 + T_inst_latency.
    Definition ttbge := 5 + T_inst_latency.
    Definition ttbltu := 5 + T_inst_latency.
    Definition ttbgeu := 5 + T_inst_latency.
    (* not taken *)
    Definition tfbeq := 3.
    Definition tfbne := 3.
    Definition tfblt := 3.
    Definition tfbge := 3.
    Definition tfbltu := 3.
    Definition tfbgeu := 3.
    (* Jump/call *)
    Definition tjal := 5 + T_inst_latency.
    Definition tjalr := 5 + T_inst_latency.
    (* Load/store *)
    Definition tlb := 4 + T_data_latency.
    Definition tlh := 4 + T_data_latency.
    Definition tlw := 4 + T_data_latency.
    Definition tlbu := 4 + T_data_latency.
    Definition tlhu := 4 + T_data_latency.
    Definition tsb := 4 + T_data_latency.
    Definition tsh := 4 + T_data_latency.
    Definition tsw := 4 + T_data_latency.
    (* Data fence *)
    Definition tfence := 6 + T_data_latency.
    (* System *)
    Definition tecall := 7 + T_inst_latency.
    Definition tebreak := 7 + T_inst_latency.
    Definition tmret := 7 + T_inst_latency.
    Definition twfi := 7 + T_inst_latency.

    (* ==== M ISA Extension ==== *)
    (* Multiplication *)
    Definition tmul := 3 + T_mul_latency.
    Definition tmulh := 3 + T_mul_latency.
    Definition tmulhsu := 3 + T_mul_latency.
    Definition tmulhu := 3 + T_mul_latency.
    (* Division *)
    Definition tdiv := 3 + 32.
    Definition tdivu := 3 + 32.
    Definition trem := 3 + 32.
    Definition tremu := 3 + 32.

    (* ==== Zbb ISA Extension ==== *)
    (* Logic with negate *)
    Definition tandn := 4.
    Definition torn := 4.
    Definition txnor := 4.
    (* Bit count *)
    Definition tclz (val : N) := 4 + T_shift_latency (clz val 32).
    Definition tctz (val : N) := 4 + T_shift_latency (ctz val 32).
    Definition tcpop (val : N) := 4 + T_shift_latency 32.
    (* Integer max/min *)
    Definition tmin := 4.
    Definition tminu := 4.
    Definition tmax := 4.
    Definition tmaxu := 4.
    (* Sign/zero extension *)
    Definition tsext_b := 4.
    Definition tsext_h := 4.
    Definition tzext := 4.
    (* Bitwise rotation *)
    Definition trol (rot_factor : N) := 4 + T_shift_latency rot_factor.
    Definition tror (rot_factor : N) := 4 + T_shift_latency rot_factor.
    Definition trori (rot_factor : N) := 4 + T_shift_latency rot_factor.
    (* OR-combine *)
    Definition torc_b := 4.
    (* Byte-reverse *)
    Definition trev8 := 4.

    (* ==== Zicsr ISA Extension ==== *)
    (* System *)
    Definition tcsrrw := 3.
    Definition tcsrrwi := 3.
    Definition tcsrrs := 3.
    Definition tcsrrsi := 3.
    Definition tcsrrc := 3.
    Definition tcsrrci := 3.
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
