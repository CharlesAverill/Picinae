(* ARMv6MCPUTimingBehavior.v - Module Type for CPU Timing Parameters *)
(* Defines the interface for specifying cycle counts for each instruction class *)

Require Import NArith.

Open Scope N.

(* 
   This module type defines timing parameters for ARMv6-M CPUs.
   Different implementations (Cortex-M0, Cortex-M0+, etc.) can provide
   concrete values for these parameters.
   
   Timing values are based on the processor's Technical Reference Manual
   (ARM DDI 0432C, Table 3-1, for the Cortex-M0).
   The actual cycle counts depend on:
   - Specific CPU implementation
   - Memory wait states
   - Pipeline behavior
*)

Module Type ARMv6MCPUTimingBehavior.

    (* Special value for instructions that shouldn't complete (exceptions, etc.) *)
    Parameter time_inf : N.
    
    (* ===== Move Operations ===== *)
    Parameter tmovs_imm : N.    (* MOVS Rd, #imm8 *)
    Parameter tmovs_reg : N.    (* MOVS Rd, Rm *)
    Parameter tmov_reg : N.     (* MOV Rd, Rm (low registers) *)
    Parameter tmov_pc : N.      (* MOV PC, Rm (branch) *)
    
    (* ===== Add Operations ===== *)
    Parameter tadds_3reg : N.   (* ADDS Rd, Rn, Rm *)
    Parameter tadds_imm3 : N.   (* ADDS Rd, Rn, #imm3 *)
    Parameter tadds_imm8 : N.   (* ADDS Rd, #imm8 *)
    Parameter tadd_reg : N.     (* ADD Rd, Rm (high registers) *)
    Parameter tadd_pc : N.      (* ADD PC, Rm (branch) *)
    Parameter tadcs : N.        (* ADCS Rd, Rm *)
    Parameter tadd_sp_imm : N.  (* ADD Rd, SP, #imm / ADD SP, SP, #imm *)
    Parameter tadr : N.         (* ADR Rd, label *)
    
    (* ===== Subtract Operations ===== *)
    Parameter tsubs_3reg : N.   (* SUBS Rd, Rn, Rm *)
    Parameter tsubs_imm3 : N.   (* SUBS Rd, Rn, #imm3 *)
    Parameter tsubs_imm8 : N.   (* SUBS Rd, #imm8 *)
    Parameter tsbcs : N.        (* SBCS Rd, Rm *)
    Parameter tsub_sp_imm : N.  (* SUB SP, SP, #imm *)
    Parameter trsbs : N.        (* RSBS Rd, Rn, #0 (NEG) *)
    
    (* ===== Multiply ===== *)
    Parameter tmuls : N.        (* MULS Rd, Rm - may vary by implementation *)
    
    (* ===== Compare Operations ===== *)
    Parameter tcmp_reg : N.     (* CMP Rn, Rm *)
    Parameter tcmn : N.         (* CMN Rn, Rm *)
    Parameter tcmp_imm : N.     (* CMP Rn, #imm8 *)
    
    (* ===== Logical Operations ===== *)
    Parameter tands : N.        (* ANDS Rd, Rm *)
    Parameter teors : N.        (* EORS Rd, Rm *)
    Parameter torrs : N.        (* ORRS Rd, Rm *)
    Parameter tbics : N.        (* BICS Rd, Rm *)
    Parameter tmvns : N.        (* MVNS Rd, Rm *)
    Parameter ttst : N.         (* TST Rn, Rm *)
    
    (* ===== Shift Operations ===== *)
    Parameter tlsls_imm : N.    (* LSLS Rd, Rm, #imm5 *)
    Parameter tlsls_reg : N.    (* LSLS Rd, Rs *)
    Parameter tlsrs_imm : N.    (* LSRS Rd, Rm, #imm5 *)
    Parameter tlsrs_reg : N.    (* LSRS Rd, Rs *)
    Parameter tasrs_imm : N.    (* ASRS Rd, Rm, #imm5 *)
    Parameter tasrs_reg : N.    (* ASRS Rd, Rs *)
    Parameter trors : N.        (* RORS Rd, Rs *)
    
    (* ===== Load Operations ===== *)
    Parameter tldr_imm : N.     (* LDR Rd, [Rn, #imm5] *)
    Parameter tldrh_imm : N.    (* LDRH Rd, [Rn, #imm5] *)
    Parameter tldrb_imm : N.    (* LDRB Rd, [Rn, #imm5] *)
    Parameter tldr_reg : N.     (* LDR Rd, [Rn, Rm] *)
    Parameter tldrh_reg : N.    (* LDRH Rd, [Rn, Rm] *)
    Parameter tldrsh_reg : N.   (* LDRSH Rd, [Rn, Rm] *)
    Parameter tldrb_reg : N.    (* LDRB Rd, [Rn, Rm] *)
    Parameter tldrsb_reg : N.   (* LDRSB Rd, [Rn, Rm] *)
    Parameter tldr_pc : N.      (* LDR Rd, [PC, #imm8] *)
    Parameter tldr_sp : N.      (* LDR Rd, [SP, #imm8] *)
    
    (* ===== Store Operations ===== *)
    Parameter tstr_imm : N.     (* STR Rd, [Rn, #imm5] *)
    Parameter tstrh_imm : N.    (* STRH Rd, [Rn, #imm5] *)
    Parameter tstrb_imm : N.    (* STRB Rd, [Rn, #imm5] *)
    Parameter tstr_reg : N.     (* STR Rd, [Rn, Rm] *)
    Parameter tstrh_reg : N.    (* STRH Rd, [Rn, Rm] *)
    Parameter tstrb_reg : N.    (* STRB Rd, [Rn, Rm] *)
    Parameter tstr_sp : N.      (* STR Rd, [SP, #imm8] *)
    
    (* ===== Load/Store Multiple ===== *)
    (* Base cycles - actual time is base + N where N is register count *)
    Parameter tldm_base : N.    (* LDM Rn!, {reglist} base *)
    Parameter tstm_base : N.    (* STM Rn!, {reglist} base *)
    
    (* ===== Push/Pop ===== *)
    (* Base cycles - actual time is base + N where N is register count *)
    Parameter tpush_base : N.   (* PUSH {reglist} base *)
    Parameter tpop_base : N.    (* POP {reglist} base (no PC) *)
    Parameter tpop_pc_base : N. (* POP {reglist, PC} base (includes pipeline refill); N counts PC *)
    
    (* ===== Branch Operations ===== *)
    Parameter tb_taken : N.     (* B.cond taken - includes pipeline refill *)
    Parameter tb_not_taken : N. (* B.cond not taken *)
    Parameter tb : N.           (* B (unconditional) - always refills pipeline *)
    Parameter tbl : N.          (* BL - branch with link *)
    Parameter tbx : N.          (* BX Rm - branch and exchange *)
    Parameter tblx : N.         (* BLX Rm - branch with link and exchange *)
    
    (* ===== Extend Operations ===== *)
    Parameter tsxth : N.        (* SXTH Rd, Rm *)
    Parameter tsxtb : N.        (* SXTB Rd, Rm *)
    Parameter tuxth : N.        (* UXTH Rd, Rm *)
    Parameter tuxtb : N.        (* UXTB Rd, Rm *)
    
    (* ===== Reverse Operations ===== *)
    Parameter trev : N.         (* REV Rd, Rm *)
    Parameter trev16 : N.       (* REV16 Rd, Rm *)
    Parameter trevsh : N.       (* REVSH Rd, Rm *)
    
    (* ===== Hints ===== *)
    Parameter tnop : N.         (* NOP *)
    Parameter tsev : N.         (* SEV *)
    Parameter twfe : N.         (* WFE *)
    Parameter twfi : N.         (* WFI *)
    Parameter tyield : N.       (* YIELD *)
    
    (* ===== Barriers ===== *)
    Parameter tdmb : N.         (* DMB *)
    Parameter tdsb : N.         (* DSB *)
    Parameter tisb : N.         (* ISB *)
    
    (* ===== System Register Access ===== *)
    Parameter tmrs : N.         (* MRS Rd, spec_reg *)
    Parameter tmsr : N.         (* MSR spec_reg, Rn *)
    
    (* ===== Interrupt Control ===== *)
    Parameter tcpsid : N.       (* CPSID i *)
    Parameter tcpsie : N.       (* CPSIE i *)
    
End ARMv6MCPUTimingBehavior.
