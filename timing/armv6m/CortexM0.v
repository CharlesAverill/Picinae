(* CortexM0.v - Concrete Timing Parameters for ARM Cortex-M0 *)
(* Based on ARMv6-M Architecture Reference Manual Table 3-1 *)
(* Assumes zero wait-state memory *)
(* TODO: Validate against the Cortex-M0 TRM and the STM32F0DISCOVERY's flash wait states *)

Require Import NArith.
Require Import ARMv6MCPUTimingBehavior.

Open Scope N.

(*
   ARM Cortex-M0 Instruction Timing
   ================================
   
   Source: ARMv6-M Architecture Reference Manual DDI 0419E
           Section 3.3.1 "Instruction cycle counts"
   
   Key characteristics:
   - 3-stage pipeline (Fetch, Decode, Execute)
   - Most ALU operations: 1 cycle
   - Load/Store: 2 cycles (with zero wait-state memory)
   - Branches taken: 1-3 cycles (pipeline refill)
   - Multiply: 1 cycle (fast multiplier) or 32 cycles (small multiplier)
   
   This implementation assumes:
   - Zero wait-state memory
   - Fast multiplier option
   - No flash acceleration
*)

Module CortexM0 <: ARMv6MCPUTimingBehavior.

    (* Infinite time for exceptional conditions *)
    Definition time_inf : N := 2^32.
    
    (* ===== Move Operations - 1 cycle ===== *)
    Definition tmovs_imm : N := 1.
    Definition tmovs_reg : N := 1.
    Definition tmov_reg : N := 1.
    Definition tmov_pc : N := 3.   (* Branch to PC - pipeline refill *)
    
    (* ===== Add Operations - 1 cycle ===== *)
    Definition tadds_3reg : N := 1.
    Definition tadds_imm3 : N := 1.
    Definition tadds_imm8 : N := 1.
    Definition tadd_reg : N := 1.
    Definition tadd_pc : N := 3.   (* ADD PC - pipeline refill *)
    Definition tadcs : N := 1.
    Definition tadd_sp_imm : N := 1.
    Definition tadr : N := 1.
    
    (* ===== Subtract Operations - 1 cycle ===== *)
    Definition tsubs_3reg : N := 1.
    Definition tsubs_imm3 : N := 1.
    Definition tsubs_imm8 : N := 1.
    Definition tsbcs : N := 1.
    Definition tsub_sp_imm : N := 1.
    Definition trsbs : N := 1.
    
    (* ===== Multiply - 1 cycle (fast multiplier) ===== *)
    (* Note: Some Cortex-M0 implementations use a small multiplier
       which takes 32 cycles. Check your specific implementation. *)
    Definition tmuls : N := 1.
    
    (* ===== Compare Operations - 1 cycle ===== *)
    Definition tcmp_reg : N := 1.
    Definition tcmn : N := 1.
    Definition tcmp_imm : N := 1.
    
    (* ===== Logical Operations - 1 cycle ===== *)
    Definition tands : N := 1.
    Definition teors : N := 1.
    Definition torrs : N := 1.
    Definition tbics : N := 1.
    Definition tmvns : N := 1.
    Definition ttst : N := 1.
    
    (* ===== Shift Operations - 1 cycle ===== *)
    Definition tlsls_imm : N := 1.
    Definition tlsls_reg : N := 1.
    Definition tlsrs_imm : N := 1.
    Definition tlsrs_reg : N := 1.
    Definition tasrs_imm : N := 1.
    Definition tasrs_reg : N := 1.
    Definition trors : N := 1.
    
    (* ===== Load Operations - 2 cycles ===== *)
    (* With zero wait-state memory *)
    Definition tldr_imm : N := 2.
    Definition tldrh_imm : N := 2.
    Definition tldrb_imm : N := 2.
    Definition tldr_reg : N := 2.
    Definition tldrh_reg : N := 2.
    Definition tldrsh_reg : N := 2.
    Definition tldrb_reg : N := 2.
    Definition tldrsb_reg : N := 2.
    Definition tldr_pc : N := 2.
    Definition tldr_sp : N := 2.
    
    (* ===== Store Operations - 2 cycles ===== *)
    Definition tstr_imm : N := 2.
    Definition tstrh_imm : N := 2.
    Definition tstrb_imm : N := 2.
    Definition tstr_reg : N := 2.
    Definition tstrh_reg : N := 2.
    Definition tstrb_reg : N := 2.
    Definition tstr_sp : N := 2.
    
    (* ===== Load/Store Multiple ===== *)
    (* Time = 1 + N cycles where N is number of registers *)
    Definition tldm_base : N := 1.
    Definition tstm_base : N := 1.
    
    (* ===== Push/Pop ===== *)
    (* PUSH: 1 + N cycles *)
    (* POP: 1 + N cycles (no PC) *)
    (* POP with PC: 1 + N + 3 cycles (pipeline refill) *)
    Definition tpush_base : N := 1.
    Definition tpop_base : N := 1.
    Definition tpop_pc_base : N := 4.  (* 1 base + 3 pipeline refill *)
    
    (* ===== Branch Operations ===== *)
    (* Pipeline refill takes extra cycles *)
    Definition tb_taken : N := 3.      (* Conditional branch taken *)
    Definition tb_not_taken : N := 1.  (* Conditional branch not taken *)
    Definition tb : N := 3.            (* Unconditional branch *)
    Definition tbl : N := 4.           (* Branch with link (32-bit instruction) *)
    Definition tbx : N := 3.           (* Branch and exchange *)
    Definition tblx : N := 3.          (* Branch with link and exchange *)
    
    (* ===== Extend Operations - 1 cycle ===== *)
    Definition tsxth : N := 1.
    Definition tsxtb : N := 1.
    Definition tuxth : N := 1.
    Definition tuxtb : N := 1.
    
    (* ===== Reverse Operations - 1 cycle ===== *)
    Definition trev : N := 1.
    Definition trev16 : N := 1.
    Definition trevsh : N := 1.
    
    (* ===== Hints ===== *)
    Definition tnop : N := 1.
    Definition tsev : N := 1.
    Definition twfe : N := 2.    (* Wait for event - at least 2 *)
    Definition twfi : N := 2.    (* Wait for interrupt - at least 2 *)
    Definition tyield : N := 1.
    
    (* ===== Barriers - Implementation defined, typically 4 cycles ===== *)
    Definition tdmb : N := 4.
    Definition tdsb : N := 4.
    Definition tisb : N := 4.
    
    (* ===== System Register Access - 4 cycles ===== *)
    Definition tmrs : N := 4.
    Definition tmsr : N := 4.
    
    (* ===== Interrupt Control - 1 cycle ===== *)
    Definition tcpsid : N := 1.
    Definition tcpsie : N := 1.
    
End CortexM0.

(* 
   USAGE NOTES
   ===========
   
   1. Memory Wait States:
      If your system has memory wait states, add them to load/store times.
      Example: With 1 wait state, tldr_imm would be 3 instead of 2.
   
   2. Flash Acceleration:
      Some Cortex-M0 implementations have flash accelerators that can
      reduce instruction fetch latency. This is not modeled here.
   
   3. Multiplier:
      This assumes the fast (single-cycle) multiplier option.
      If using the small multiplier, tmuls should be 32.
   
   4. Branch Prediction:
      Cortex-M0 has no branch prediction, so all taken branches
      incur the full pipeline refill penalty.
   
   5. Interrupts:
      Interrupt latency is not modeled. For worst-case timing analysis,
      consider the maximum interrupt service time.
*)
