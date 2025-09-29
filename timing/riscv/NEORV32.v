Require Import CPUTimingBehavior ProgramInformation.
Require Import NArith ZArith.
Require Import Picinae_riscv.
Import RISCVNotations.
Open Scope r5_scope.
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
    (* Number of instruction cache lines *)
    Parameter ICACHE_NUM_BLOCKS : N.
    (* Implement the data cache *)
    Parameter DCACHE_EN : bool.
    (* Number of data cache lines *)
    Parameter DCACHE_NUM_BLOCKS : N.
    (* Size of a cache line *)
    Parameter CACHE_BLOCK_SIZE : N.
End NEORV32Config.

Record cache_line : Type := {
    tag : N;
    data : memory;
    initialized : bool
}.

Inductive cache_type : Type :=
    | Data | Instruction.

Record cache : Type := {
    iline : N -> cache_line;
    dline : N -> cache_line;
}.

Fixpoint range (n : N) : list N.
    destruct n as [| n' IHn'] using (N.peano_rect).
        exact nil.
    exact (List.cons n' IHn').
Defined.

(* https://stnolting.github.io/neorv32/#_instruction_sets_and_extensions *)
Module NEORV32 (cfg : NEORV32Config) (prog : ProgramInformation) <: CPUTimingBehavior.
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

    Definition cache : Type := cache.

    Definition clear_cache : cache :=
        {|iline := fun _ => {|tag := 0; data := 0; initialized := false|};
          dline := fun _ => {|tag := 0; data := 0; initialized := false|}|}.

    Definition cache_read (s : store) (c : cache) 
            (address : addr) (ct : cache_type) : cache :=
        let '(CACHE, CACHE_LINES) := (
             match ct with 
             | Instruction => (c.(iline), cfg.ICACHE_NUM_BLOCKS)
             | Data => (c.(dline), cfg.DCACHE_NUM_BLOCKS)
             end) in
        let offset := address mod cfg.CACHE_BLOCK_SIZE in
        let index := (address / cfg.CACHE_BLOCK_SIZE) mod CACHE_LINES in
        let tag' := address / (cfg.CACHE_BLOCK_SIZE * CACHE_LINES) in
        
        let line := CACHE index in

        if andb (line.(initialized)) (line.(tag) =? tag') then (
            c
        ) else (
            let base_addr := address - offset in
            let line' := {| data := List.fold_left (fun data i =>
                data [Ⓑ i := (s V_MEM32) Ⓑ[base_addr + i]]
            ) (range cfg.CACHE_BLOCK_SIZE) (line.(data));
               tag := tag';
               initialized := true |} in
            match ct with
            | Data =>
                {|dline := update c.(dline) index line'; iline := c.(iline)|}
            | Instruction =>
                {|dline := c.(dline); iline := update c.(iline) index line'|}
            end
        ).

    Definition cache_write (c : cache) 
            (address : addr) (value : N) (ct : cache_type) : cache :=
        let '(CACHE, CACHE_LINES) := (
             match ct with 
             | Instruction => (c.(iline), cfg.ICACHE_NUM_BLOCKS)
             | Data => (c.(dline), cfg.DCACHE_NUM_BLOCKS)
             end) in
        let offset := address mod cfg.CACHE_BLOCK_SIZE in
        let index := (address / cfg.CACHE_BLOCK_SIZE) mod CACHE_LINES in
        let tag' := address / (cfg.CACHE_BLOCK_SIZE * CACHE_LINES) in
        
        let line := CACHE index in

        if line.(tag) =? tag' then (
            let line' :=
                {|data := line.(data) [Ⓓ offset := value];
                  tag := tag';
                  initialized := true|} in
            match ct with
            | Data =>
                {|dline := update c.(dline) index line'; iline := c.(iline)|}
            | Instruction =>
                {|dline := c.(dline); iline := update c.(iline) index line'|}
            end
        ) else (
            c
        ).

    Definition cached (c : cache) (address : addr) (ct : cache_type) : bool :=
         let '(CACHE, CACHE_LINES) := (
             match ct with 
             | Instruction => (c.(iline), cfg.ICACHE_NUM_BLOCKS)
             | Data => (c.(dline), cfg.DCACHE_NUM_BLOCKS)
             end) in
        let index := (address / cfg.CACHE_BLOCK_SIZE) mod CACHE_LINES in
        let tag' := address / (cfg.CACHE_BLOCK_SIZE * CACHE_LINES) in

        (CACHE index).(tag) =? tag'.

    Definition cache_step (s : store) (c : cache) (a : addr) : cache :=
        let load a o := cache_read s c 
            (add_signed_offset' (reg s a) o) Data in
        let write a o v := cache_write c 
            (add_signed_offset (reg s a) o)
            (reg s v) Data in
        let jump a' := cache_read s c (add_signed_offset a a') Instruction in
        match rv_decode (prog.binary a) with
        | R5_Lb _ rs imm => load rs imm
        | R5_Lh _ rs imm => load rs imm
        | R5_Lw _ rs imm => load rs imm
        | R5_Lbu _ rs imm => load rs imm
        | R5_Lhu _ rs imm => load rs imm
        | R5_Sb rs2 rs1 imm => write rs1 imm rs2
        | R5_Sh rs2 rs1 imm => write rs1 imm rs2
        | R5_Sw rs2 rs1 imm => write rs1 imm rs2
        | R5_Fence _ _ => clear_cache
        | R5_Fence_i => clear_cache
        | R5_Beq _ _ a => jump a
        | R5_Bne _ _ a => jump a
        | R5_Blt _ _ a => jump a
        | R5_Bge _ _ a => jump a
        | R5_Bltu _ _ a => jump a
        | R5_Bgeu _ _ a => jump a
        | R5_Jal _ a => jump a
        | R5_Jalr r1 _ a =>
            cache_read s c (resolve_jalr_addr a r1) Instruction
        | _ => c
        end.

    Parameter T_data_latency_raw : N.
    Parameter T_inst_latency_raw : N.

    Definition T_data_latency (c : cache) (a : addr) : N :=
        if cfg.DCACHE_EN then (
            if cached c a Data then 1 else T_inst_latency_raw
        ) else (
            T_inst_latency_raw
        ).

    Definition T_inst_latency (c : cache) (a : addr) : N :=
        if cfg.ICACHE_EN then (
            if cached c a Instruction then 1 else T_inst_latency_raw
        ) else (
            T_inst_latency_raw
        ).

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
    Definition ttbeq c a := 5 + T_inst_latency c a.
    Definition ttbne c a := 5 + T_inst_latency c a.
    Definition ttblt c a := 5 + T_inst_latency c a.
    Definition ttbge c a := 5 + T_inst_latency c a.
    Definition ttbltu c a := 5 + T_inst_latency c a.
    Definition ttbgeu c a := 5 + T_inst_latency c a.
    (* not taken *)
    Definition tfbeq (_ : cache) (_ : addr) := 3.
    Definition tfbne (_ : cache) (_ : addr)  := 3.
    Definition tfblt (_ : cache) (_ : addr)  := 3.
    Definition tfbge (_ : cache) (_ : addr)  := 3.
    Definition tfbltu (_ : cache) (_ : addr)  := 3.
    Definition tfbgeu (_ : cache) (_ : addr)  := 3.
    (* Jump/call *)
    Definition tjal c a := 5 + T_inst_latency c a.
    Definition tjalr c a := 5 + T_inst_latency c a.
    (* Load/store *)
    Definition tlb c a := 4 + T_data_latency c a.
    Definition tlh c a := 4 + T_data_latency c a.
    Definition tlw c a := 4 + T_data_latency c a.
    Definition tlbu c a := 4 + T_data_latency c a.
    Definition tlhu c a := 4 + T_data_latency c a.
    Definition tsb c a := 4 + T_data_latency c a.
    Definition tsh c a := 4 + T_data_latency c a.
    Definition tsw c a := 4 + T_data_latency c a.
    (* Data fence *)
    Definition tfence c := 6 + T_data_latency c 0.
    Definition tfencei c := 6 + T_data_latency c 0.
    (* System *)
    Definition tecall c := 7 + T_inst_latency c 0.
    Definition tebreak c := 7 + T_inst_latency c 0.
    Definition tmret c := 7 + T_inst_latency c 0.
    Definition twfi := 3.

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
    Definition ICACHE_NUM_BLOCKS : N := 4.
    Definition DCACHE_NUM_BLOCKS : N := 4.
    Definition CACHE_BLOCK_SIZE : N := 64.
End NEORV32BaseConfig.

Module NEORV32Base := NEORV32 NEORV32BaseConfig.
