(* Picinae_armv6m.v - ARMv6-M (Cortex-M0/M0+ Thumb) ISA for Picinae *)
(* Covers every ARMv6-M instruction, including the 32-bit BL, MSR, MRS, and barriers *)
(* Models the N, Z, C, and V flags and full LDM/STM/PUSH/POP behavior *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
Require Import NArith.
Require Import ZArith.
Require Import List.
Require Import Program.Equality.
Require Import Structures.Equalities.

Open Scope N.

(* ========================================================================== *)
(*                         VARIABLE DEFINITIONS                               *)
(* ========================================================================== *)

Inductive armv6mvar :=
  | V_MEM32
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12
  | R_SP | R_LR               (* PC reads are lifted to constants *)
  | F_N | F_Z | F_C | F_V    (* Flags: Negative, Zero, Carry, oVerflow *)
  | A_READ | A_WRITE | A_EXEC
  | V_TEMP (n:N).

Definition armv6mtypctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | F_N | F_Z | F_C | F_V => Some 1
  | A_READ | A_WRITE | A_EXEC => Some (2^32)
  | V_TEMP _ => None
  | _ => Some 32
  end.

Module MiniARMv6MVarEq <: MiniDecidableType.
  Definition t := armv6mvar.
  Definition eq_dec (v1 v2:armv6mvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.
  Arguments eq_dec v1 v2 : simpl never.
End MiniARMv6MVarEq.

Module ARMv6MArch <: Architecture.
  Module Var := Make_UDT MiniARMv6MVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := armv6mtypctx.
  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End ARMv6MArch.

Module IL_ARMv6M := PicinaeIL ARMv6MArch.
Export IL_ARMv6M.
Module Theory_ARMv6M := PicinaeTheory IL_ARMv6M.
Export Theory_ARMv6M.
Module Statics_ARMv6M := PicinaeStatics IL_ARMv6M Theory_ARMv6M.
Export Statics_ARMv6M.
Module FInterp_ARMv6M := PicinaeFInterp IL_ARMv6M Theory_ARMv6M Statics_ARMv6M.
Export FInterp_ARMv6M.
Module PSimpl_ARMv6M := Picinae_Simplifier_Base IL_ARMv6M.
Export PSimpl_ARMv6M.
Module PSimpl_ARMv6M_v1_1 := Picinae_Simplifier_v1_1 IL_ARMv6M Theory_ARMv6M Statics_ARMv6M FInterp_ARMv6M.
Ltac PSimplifier ::= PSimpl_ARMv6M_v1_1.PSimplifier.

Module ISA_ARMv6M := Picinae_ISA IL_ARMv6M PSimpl_ARMv6M Theory_ARMv6M Statics_ARMv6M FInterp_ARMv6M.
Export ISA_ARMv6M.

Tactic Notation "armv6m_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "armv6m_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "armv6m_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "armv6m_psimpl" := psimpl_goal.
Ltac armv6m_step := ISA_step.

Theorem memacc_respects_armv6mtypctx: memacc_respects_typctx armv6mtypctx.
Proof. intros s1 s2 RV. rewrite <- RV. split; reflexivity. Qed.

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof. intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity. apply not_eq_sym. exact NE. Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof. intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity. apply not_eq_sym. exact NE. Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof. intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity. Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof. intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity. Qed.

Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

Declare Scope armv6m_scope.
Delimit Scope armv6m_scope with armv6m.
Bind Scope armv6m_scope with stmt exp trace.
Open Scope armv6m_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : armv6m_scope.

Module ARMv6MNotations.
  Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : armv6m_scope. (* read byte *)
  Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : armv6m_scope. (* read halfword *)
  Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : armv6m_scope. (* read word *)
  Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : armv6m_scope. (* write byte *)
  Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : armv6m_scope. (* write halfword *)
  Notation "m [Ⓓ a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : armv6m_scope. (* write word *)
  Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
  Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
  Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
  Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
  Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
  Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
  Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
  Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
  Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)
End ARMv6MNotations.

(* ========================================================================== *)
(*                         REGISTER HELPERS                                   *)
(* ========================================================================== *)

Definition regid := N.

(* Register 15 (PC) never names a variable: armv6m_var reads it as a constant,
   and arm2il lifts writes to it as jumps *)
Definition armv6m_varid (n : regid) :=
  match n with
  | 0 => R_R0  | 1 => R_R1  | 2 => R_R2  | 3 => R_R3
  | 4 => R_R4  | 5 => R_R5  | 6 => R_R6  | 7 => R_R7
  | 8 => R_R8  | 9 => R_R9  | 10 => R_R10 | 11 => R_R11
  | 12 => R_R12 | 13 => R_SP | _ => R_LR
  end.

(* Reading the PC yields the address of the current instruction plus 4 *)
Definition armv6m_var (a : addr) (n : regid) :=
  if n =? 15 then Word ((a + 4) mod 2^32) 32 else Var (armv6m_varid n).

Definition armv6m_mov (n : regid) e :=
  Move (armv6m_varid n) e.

(* Immediates are reduced modulo 2^32, so every lifted constant is well-typed *)
Definition armv6m_word n :=
  Word (n mod 2^32) 32.

(* ========================================================================== *)
(*                         CONDITION CODES                                    *)
(* ========================================================================== *)

Inductive condition :=
  | COND_EQ | COND_NE | COND_CS | COND_CC
  | COND_MI | COND_PL | COND_VS | COND_VC
  | COND_HI | COND_LS | COND_GE | COND_LT
  | COND_GT | COND_LE | COND_AL.

(* ========================================================================== *)
(*                         THUMB INSTRUCTION SET                              *)
(* ========================================================================== *)

(* Immediates are the raw instruction fields; branch offsets are sign-extended
   byte offsets from the PC (the instruction address plus 4) *)
Inductive thumb_instr :=
  | T_MOVS_imm (rd : regid) (imm8 : N)
  | T_MOVS_reg (rd rm : regid)
  | T_MOV_reg (rd rm : regid)
  | T_ADDS_3reg (rd rn rm : regid)
  | T_ADDS_imm3 (rd rn : regid) (imm3 : N)
  | T_ADDS_imm8 (rd : regid) (imm8 : N)
  | T_ADD_reg (rd rm : regid)
  | T_ADCS (rd rm : regid)
  | T_ADD_SP_imm (rd : regid) (imm8 : N)
  | T_ADD_SP_SP_imm (imm7 : N)
  | T_ADR (rd : regid) (imm8 : N)
  | T_SUBS_3reg (rd rn rm : regid)
  | T_SUBS_imm3 (rd rn : regid) (imm3 : N)
  | T_SUBS_imm8 (rd : regid) (imm8 : N)
  | T_SBCS (rd rm : regid)
  | T_SUB_SP_imm (imm7 : N)
  | T_RSBS (rd rn : regid)
  | T_MULS (rd rm : regid)
  | T_CMP_reg (rn rm : regid)
  | T_CMN (rn rm : regid)
  | T_CMP_imm (rn : regid) (imm8 : N)
  | T_ANDS (rd rm : regid)
  | T_EORS (rd rm : regid)
  | T_ORRS (rd rm : regid)
  | T_BICS (rd rm : regid)
  | T_MVNS (rd rm : regid)
  | T_TST (rn rm : regid)
  | T_LSLS_imm (rd rm : regid) (imm5 : N)
  | T_LSLS_reg (rd rm : regid)
  | T_LSRS_imm (rd rm : regid) (imm5 : N)
  | T_LSRS_reg (rd rm : regid)
  | T_ASRS_imm (rd rm : regid) (imm5 : N)
  | T_ASRS_reg (rd rm : regid)
  | T_RORS (rd rm : regid)
  | T_LDR_imm (rt rn : regid) (imm5 : N)
  | T_LDRH_imm (rt rn : regid) (imm5 : N)
  | T_LDRB_imm (rt rn : regid) (imm5 : N)
  | T_LDR_reg (rt rn rm : regid)
  | T_LDRH_reg (rt rn rm : regid)
  | T_LDRSH_reg (rt rn rm : regid)
  | T_LDRB_reg (rt rn rm : regid)
  | T_LDRSB_reg (rt rn rm : regid)
  | T_LDR_pc (rt : regid) (imm8 : N)
  | T_LDR_sp (rt : regid) (imm8 : N)
  | T_STR_imm (rt rn : regid) (imm5 : N)
  | T_STRH_imm (rt rn : regid) (imm5 : N)
  | T_STRB_imm (rt rn : regid) (imm5 : N)
  | T_STR_reg (rt rn rm : regid)
  | T_STRH_reg (rt rn rm : regid)
  | T_STRB_reg (rt rn rm : regid)
  | T_STR_sp (rt : regid) (imm8 : N)
  | T_LDM (rn : regid) (reglist : N)
  | T_STM (rn : regid) (reglist : N)
  | T_PUSH (reglist : N) (lr : bool)
  | T_POP (reglist : N) (pc : bool)
  | T_B_cond (cond : condition) (off : Z)
  | T_B (off : Z)
  | T_BL (off : Z)
  | T_BX (rm : regid)
  | T_BLX (rm : regid)
  | T_SXTH (rd rm : regid)
  | T_SXTB (rd rm : regid)
  | T_UXTH (rd rm : regid)
  | T_UXTB (rd rm : regid)
  | T_REV (rd rm : regid)
  | T_REV16 (rd rm : regid)
  | T_REVSH (rd rm : regid)
  | T_NOP | T_SEV | T_WFE | T_WFI | T_YIELD
  | T_BKPT (imm8 : N)
  | T_SVC (imm8 : N)
  | T_CPSID | T_CPSIE
  | T_DMB | T_DSB | T_ISB
  | T_MRS (rd : regid) (sysm : N)
  | T_MSR (sysm : N) (rn : regid)
  | T_Invalid.

(* ========================================================================== *)
(*                         HELPER FUNCTIONS                                   *)
(* ========================================================================== *)

(* Sequence a list of statements (without a trailing Nop) *)
Fixpoint armv6m_seq qs :=
  match qs with
  | nil => Nop
  | q :: nil => q
  | q :: qs' => Seq q (armv6m_seq qs')
  end.

(* The registers named by a register list, in ascending order *)
Definition armv6m_regs rl :=
  filter (fun r => N.testbit rl r) (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).

(* Pair each register with its slot (in words) in a transfer *)
Fixpoint armv6m_slots (k:N) (rs:list N) : list (N*N) :=
  match rs with
  | nil => nil
  | r :: rs' => (k, r) :: armv6m_slots (N.succ k) rs'
  end.

(* Rotate right by e mod 32 *)
Definition armv6m_ror x e :=
  let m := BinOp OP_AND e (Word 31 32) in
  BinOp OP_OR (BinOp OP_RSHIFT x m) (BinOp OP_LSHIFT x (BinOp OP_MINUS (Word 32 32) m)).

(* ========================================================================== *)
(*                         CONDITION EXPRESSION                               *)
(* ========================================================================== *)

Definition armv6m_cond c :=
  match c with
  | COND_EQ => Var F_Z
  | COND_NE => UnOp OP_NOT (Var F_Z)
  | COND_CS => Var F_C
  | COND_CC => UnOp OP_NOT (Var F_C)
  | COND_MI => Var F_N
  | COND_PL => UnOp OP_NOT (Var F_N)
  | COND_VS => Var F_V
  | COND_VC => UnOp OP_NOT (Var F_V)
  | COND_HI => BinOp OP_AND (Var F_C) (UnOp OP_NOT (Var F_Z))
  | COND_LS => BinOp OP_OR (UnOp OP_NOT (Var F_C)) (Var F_Z)
  | COND_GE => BinOp OP_EQ (Var F_N) (Var F_V)
  | COND_LT => BinOp OP_NEQ (Var F_N) (Var F_V)
  | COND_GT => BinOp OP_AND (UnOp OP_NOT (Var F_Z)) (BinOp OP_EQ (Var F_N) (Var F_V))
  | COND_LE => BinOp OP_OR (Var F_Z) (BinOp OP_NEQ (Var F_N) (Var F_V))
  | COND_AL => Word 1 1
  end.

(* The value of armv6m_cond c in store s (nonzero iff c holds), for timing
   models; see armv6m_cond_val_eval *)
Definition armv6m_cond_val (s : store) c :=
  match c with
  | COND_EQ => s F_Z
  | COND_NE => N.lnot (s F_Z) 1
  | COND_CS => s F_C
  | COND_CC => N.lnot (s F_C) 1
  | COND_MI => s F_N
  | COND_PL => N.lnot (s F_N) 1
  | COND_VS => s F_V
  | COND_VC => N.lnot (s F_V) 1
  | COND_HI => N.land (s F_C) (N.lnot (s F_Z) 1)
  | COND_LS => N.lor (N.lnot (s F_C) 1) (s F_Z)
  | COND_GE => N.b2n (s F_N =? s F_V)
  | COND_LT => N.b2n (negb (s F_N =? s F_V))
  | COND_GT => N.land (N.lnot (s F_Z) 1) (N.b2n (s F_N =? s F_V))
  | COND_LE => N.lor (s F_Z) (N.b2n (negb (s F_N =? s F_V)))
  | COND_AL => 1
  end.

(* ========================================================================== *)
(*                         IL GENERATION HELPERS                              *)
(* ========================================================================== *)

Definition armv6m_setnz r :=
  Seq (Move F_N (Cast CAST_HIGH 1 r)) (Move F_Z (BinOp OP_EQ r (Word 0 32))).

(* Flags of x + y = r (with carry-in); the caller computes the carry c *)
Definition armv6m_addflags x y r c :=
  Seq (armv6m_setnz r)
      (Seq (Move F_V (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR x r) (BinOp OP_XOR y r))))
           (Move F_C c)).

(* Flags of x - y = r (with borrow); the caller computes the carry c *)
Definition armv6m_subflags x y r c :=
  Seq (armv6m_setnz r)
      (Seq (Move F_V (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR x y) (BinOp OP_XOR x r))))
           (Move F_C c)).

(* Flags are set before rd is written, so they see the original operands *)
Definition armv6m_adds rd x y :=
  let r := BinOp OP_PLUS x y in
  Seq (armv6m_addflags x y r (BinOp OP_LT r x)) (armv6m_mov rd r).

Definition armv6m_subs rd x y :=
  let r := BinOp OP_MINUS x y in
  Seq (armv6m_subflags x y r (BinOp OP_LE y x)) (armv6m_mov rd r).

Definition armv6m_logic rd r :=
  Seq (armv6m_setnz r) (armv6m_mov rd r).

Definition armv6m_target (a : addr) off :=
  Word (ofZ 32 (Z.of_N a + 4 + off)%Z) 32.

(* BX, BLX, and POP {PC} to an address with bit 0 clear raise a HardFault (3),
   since ARMv6-M has no ARM state *)
Definition armv6m_bxwritepc e :=
  If (Cast CAST_LOW 1 e) (Jmp (BinOp OP_AND e (Word (N.ones 32 - 1) 32))) (Exn 3).

(* APSR flags in bits 31-28 (the IPSR reads as zero in Thread mode) *)
Definition armv6m_apsr :=
  BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var F_N)) (Word 31 32))
 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var F_Z)) (Word 30 32))
 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var F_C)) (Word 29 32))
              (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var F_V)) (Word 28 32)))).

(* ========================================================================== *)
(*                  FULL LDM/STM/PUSH/POP MODELING                            *)
(* ========================================================================== *)

Definition armv6m_load_slot base (kr:N*N) :=
  armv6m_mov (snd kr) (Load (Var V_MEM32) (BinOp OP_PLUS base (armv6m_word (4 * fst kr))) LittleE 4).

Definition armv6m_store_slot base (kr:N*N) :=
  Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS base (armv6m_word (4 * fst kr)))
                      (Var (armv6m_varid (snd kr))) LittleE 4).

(* Writes back only if rn is not in the list; otherwise rn is loaded last *)
Definition armv6m_ldm (rn : regid) rl :=
  let base := Var (armv6m_varid rn) in
  let slots := armv6m_slots 0 (armv6m_regs rl) in
  armv6m_seq (map (armv6m_load_slot base) (filter (fun kr => negb (snd kr =? rn)) slots) ++
              map (armv6m_load_slot base) (filter (fun kr => snd kr =? rn) slots) ++
              (if N.testbit rl rn then nil
               else Move (armv6m_varid rn) (BinOp OP_PLUS base (armv6m_word (4 * N.of_nat (length slots)))) :: nil)).

(* Always writes back (if rn is in the list but not lowest, the architecture
   stores an UNKNOWN value; this stores rn's original value) *)
Definition armv6m_stm (rn : regid) rl :=
  let base := Var (armv6m_varid rn) in
  let slots := armv6m_slots 0 (armv6m_regs rl) in
  armv6m_seq (map (armv6m_store_slot base) slots ++
              Move (armv6m_varid rn) (BinOp OP_PLUS base (armv6m_word (4 * N.of_nat (length slots)))) :: nil).

(* Lowest register at the lowest address; LR (if present) just below the old SP *)
Definition armv6m_push rl (lr:bool) :=
  let slots := armv6m_slots 0 (armv6m_regs rl ++ (if lr then 14 :: nil else nil)) in
  let sz := 4 * N.of_nat (length slots) in
  armv6m_seq (map (armv6m_store_slot (BinOp OP_MINUS (Var R_SP) (armv6m_word sz))) slots ++
              Move R_SP (BinOp OP_MINUS (Var R_SP) (armv6m_word sz)) :: nil).

Definition armv6m_pop rl (pc:bool) :=
  let slots := armv6m_slots 0 (armv6m_regs rl) in
  let sz := 4 * (N.of_nat (length slots) + (if pc then 1 else 0)) in
  armv6m_seq (map (armv6m_load_slot (Var R_SP)) slots ++
              Move R_SP (BinOp OP_PLUS (Var R_SP) (armv6m_word sz)) ::
              (if pc then armv6m_bxwritepc (Load (Var V_MEM32) (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4) :: nil
               else nil)).

(* ========================================================================== *)
(*                         INSTRUCTION DECODING                               *)
(* ========================================================================== *)

Definition thumb_decode_cond c :=
  match c with
  | 0 => COND_EQ | 1 => COND_NE | 2 => COND_CS | 3 => COND_CC
  | 4 => COND_MI | 5 => COND_PL | 6 => COND_VS | 7 => COND_VC
  | 8 => COND_HI | 9 => COND_LS | 10 => COND_GE | 11 => COND_LT
  | 12 => COND_GT | 13 => COND_LE | _ => COND_AL
  end.

(* 00xxxx: shift (immediate), add, subtract, move, and compare *)
Definition thumb_decode_shift_add_sub_mov_cmp n :=
  match xbits n 11 14 with
  | 0 => match xbits n 6 11 with 0 => T_MOVS_reg (xbits n 0 3) (xbits n 3 6) | imm5 => T_LSLS_imm (xbits n 0 3) (xbits n 3 6) imm5 end
  | 1 => T_LSRS_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11)
  | 2 => T_ASRS_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11)
  | 3 => match xbits n 9 11 with
         | 0 => T_ADDS_3reg (xbits n 0 3) (xbits n 3 6) (xbits n 6 9) | 1 => T_SUBS_3reg (xbits n 0 3) (xbits n 3 6) (xbits n 6 9)
         | 2 => T_ADDS_imm3 (xbits n 0 3) (xbits n 3 6) (xbits n 6 9) | _ => T_SUBS_imm3 (xbits n 0 3) (xbits n 3 6) (xbits n 6 9) end
  | 4 => T_MOVS_imm (xbits n 8 11) (xbits n 0 8)
  | 5 => T_CMP_imm (xbits n 8 11) (xbits n 0 8)
  | 6 => T_ADDS_imm8 (xbits n 8 11) (xbits n 0 8)
  | _ => T_SUBS_imm8 (xbits n 8 11) (xbits n 0 8)
  end.

(* 010000: data processing *)
Definition thumb_decode_data_proc op :=
  match op with
  | 0 => T_ANDS | 1 => T_EORS | 2 => T_LSLS_reg | 3 => T_LSRS_reg
  | 4 => T_ASRS_reg | 5 => T_ADCS | 6 => T_SBCS | 7 => T_RORS
  | 8 => T_TST | 9 => T_RSBS | 10 => T_CMP_reg | 11 => T_CMN
  | 12 => T_ORRS | 13 => T_MULS | 14 => T_BICS | _ => T_MVNS
  end.

(* 010001: special data instructions and branch-and-exchange (the first operand
   is the 4-bit D:Rd; BX/BLX bits 2-0 are UNPREDICTABLE if nonzero, so ignored) *)
Definition thumb_decode_special n :=
  let rdn := N.lor (N.shiftl (xbits n 7 8) 3) (xbits n 0 3) in
  match xbits n 8 10 with
  | 0 => T_ADD_reg rdn (xbits n 3 7) | 1 => T_CMP_reg rdn (xbits n 3 7) | 2 => T_MOV_reg rdn (xbits n 3 7)
  | _ => match xbits n 7 8 with 0 => T_BX (xbits n 3 7) | _ => T_BLX (xbits n 3 7) end
  end.

(* 0101: load/store, register offset *)
Definition thumb_decode_ldst_reg op :=
  match op with
  | 0 => T_STR_reg | 1 => T_STRH_reg | 2 => T_STRB_reg | 3 => T_LDRSB_reg
  | 4 => T_LDR_reg | 5 => T_LDRH_reg | 6 => T_LDRB_reg | _ => T_LDRSH_reg
  end.

(* 1011: miscellaneous (empty PUSH/POP lists and CPS bits 3-0 other than 0010
   are UNPREDICTABLE; IT is not part of ARMv6-M; unallocated hints are NOPs) *)
Definition thumb_decode_misc n :=
  match xbits n 8 12 with
  | 0 => match xbits n 7 8 with 0 => T_ADD_SP_SP_imm (xbits n 0 7) | _ => T_SUB_SP_imm (xbits n 0 7) end
  | 2 => match xbits n 6 8 with
         | 0 => T_SXTH (xbits n 0 3) (xbits n 3 6) | 1 => T_SXTB (xbits n 0 3) (xbits n 3 6)
         | 2 => T_UXTH (xbits n 0 3) (xbits n 3 6) | _ => T_UXTB (xbits n 0 3) (xbits n 3 6) end
  | 4 => match xbits n 0 8 with 0 => T_Invalid | rl => T_PUSH rl false end
  | 5 => T_PUSH (xbits n 0 8) true
  | 6 => match xbits n 5 8, xbits n 4 5 with 3, 0 => T_CPSIE | 3, _ => T_CPSID | _, _ => T_Invalid end
  | 10 => match xbits n 6 8 with
          | 0 => T_REV (xbits n 0 3) (xbits n 3 6) | 1 => T_REV16 (xbits n 0 3) (xbits n 3 6)
          | 3 => T_REVSH (xbits n 0 3) (xbits n 3 6) | _ => T_Invalid end
  | 12 => match xbits n 0 8 with 0 => T_Invalid | rl => T_POP rl false end
  | 13 => T_POP (xbits n 0 8) true
  | 14 => T_BKPT (xbits n 0 8)
  | 15 => match xbits n 0 4 with
          | 0 => match xbits n 4 8 with 1 => T_YIELD | 2 => T_WFE | 3 => T_WFI | 4 => T_SEV | _ => T_NOP end
          | _ => T_Invalid end
  | _ => T_Invalid
  end.

(* 1101: conditional branch, UDF (14), and SVC (15) *)
Definition thumb_decode_cond_branch n :=
  match xbits n 8 12 with
  | 14 => T_Invalid
  | 15 => T_SVC (xbits n 0 8)
  | c => T_B_cond (thumb_decode_cond c) (toZ 9 (N.shiftl (xbits n 0 8) 1))
  end.

Definition thumb16_decode n :=
  match xbits n 12 16 with
  | 0 | 1 | 2 | 3 => thumb_decode_shift_add_sub_mov_cmp n
  | 4 => match xbits n 10 12 with
         | 0 => thumb_decode_data_proc (xbits n 6 10) (xbits n 0 3) (xbits n 3 6)
         | 1 => thumb_decode_special n
         | _ => T_LDR_pc (xbits n 8 11) (xbits n 0 8) end
  | 5 => thumb_decode_ldst_reg (xbits n 9 12) (xbits n 0 3) (xbits n 3 6) (xbits n 6 9)
  | 6 => match xbits n 11 12 with 0 => T_STR_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) | _ => T_LDR_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) end
  | 7 => match xbits n 11 12 with 0 => T_STRB_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) | _ => T_LDRB_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) end
  | 8 => match xbits n 11 12 with 0 => T_STRH_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) | _ => T_LDRH_imm (xbits n 0 3) (xbits n 3 6) (xbits n 6 11) end
  | 9 => match xbits n 11 12 with 0 => T_STR_sp (xbits n 8 11) (xbits n 0 8) | _ => T_LDR_sp (xbits n 8 11) (xbits n 0 8) end
  | 10 => match xbits n 11 12 with 0 => T_ADR (xbits n 8 11) (xbits n 0 8) | _ => T_ADD_SP_imm (xbits n 8 11) (xbits n 0 8) end
  | 11 => thumb_decode_misc n
  | 12 => match xbits n 11 12, xbits n 0 8 with _, 0 => T_Invalid | 0, rl => T_STM (xbits n 8 11) rl | _, rl => T_LDM (xbits n 8 11) rl end
  | 13 => thumb_decode_cond_branch n
  | 14 => match xbits n 11 12 with 0 => T_B (toZ 12 (N.shiftl (xbits n 0 11) 1)) | _ => T_Invalid end
  | _ => T_Invalid
  end.

(* Halfwords starting with 11101, 11110, or 11111 begin 32-bit instructions *)
Definition is_32bit_insn hw1 :=
  29 <=? xbits hw1 11 16.

(* ARMv6-M's only 32-bit instructions are BL, MSR, MRS, DSB, DMB, and ISB *)
Definition thumb32_decode hw1 hw2 :=
  match xbits hw1 11 16, xbits hw2 15 16 with
  | 30, 1 =>
      match xbits hw2 14 15, xbits hw2 12 13 with
      | 1, 1 => let s := xbits hw1 10 11 in   (* BL: offset S:I1:I2:imm10:imm11:'0' *)
                T_BL (toZ 25 (N.lor (N.shiftl s 24)
                             (N.lor (N.shiftl (N.lxor 1 (N.lxor (xbits hw2 13 14) s)) 23)
                             (N.lor (N.shiftl (N.lxor 1 (N.lxor (xbits hw2 11 12) s)) 22)
                             (N.lor (N.shiftl (xbits hw1 0 10) 12)
                                    (N.shiftl (xbits hw2 0 11) 1))))))
      | 0, 0 =>
          match xbits hw1 4 11 with
          | 56 | 57 => T_MSR (xbits hw2 0 8) (xbits hw1 0 4)
          | 59 => match xbits hw2 4 8 with 4 => T_DSB | 5 => T_DMB | 6 => T_ISB | _ => T_Invalid end
          | 62 | 63 => T_MRS (xbits hw2 8 12) (xbits hw2 0 8)
          | _ => T_Invalid
          end
      | _, _ => T_Invalid
      end
  | _, _ => T_Invalid
  end.

(* ========================================================================== *)
(*                         MAIN INSTRUCTION LIFTER                            *)
(* ========================================================================== *)

Definition arm2il (a : addr) (insn : thumb_instr) : stmt :=
  match insn with
  | T_Invalid => Exn 3
  | T_MOVS_imm rd imm8 => armv6m_logic rd (armv6m_word imm8)
  | T_MOVS_reg rd rm => armv6m_logic rd (armv6m_var a rm)
  | T_MOV_reg rd rm => if rd =? 15 then Jmp (BinOp OP_AND (armv6m_var a rm) (Word (N.ones 32 - 1) 32)) else armv6m_mov rd (armv6m_var a rm)
  | T_ADDS_3reg rd rn rm => armv6m_adds rd (armv6m_var a rn) (armv6m_var a rm)
  | T_ADDS_imm3 rd rn imm3 => armv6m_adds rd (armv6m_var a rn) (armv6m_word imm3)
  | T_ADDS_imm8 rd imm8 => armv6m_adds rd (armv6m_var a rd) (armv6m_word imm8)
  | T_ADD_reg rd rm => let r := BinOp OP_PLUS (armv6m_var a rd) (armv6m_var a rm) in if rd =? 15 then Jmp (BinOp OP_AND r (Word (N.ones 32 - 1) 32)) else armv6m_mov rd r
  | T_ADCS rd rm => let x := armv6m_var a rd in let y := armv6m_var a rm in let r := Var (V_TEMP 0) in Seq (Move (V_TEMP 0) (BinOp OP_PLUS (BinOp OP_PLUS x y) (Cast CAST_UNSIGNED 32 (Var F_C)))) (Seq (armv6m_addflags x y r (BinOp OP_OR (BinOp OP_LT r x) (BinOp OP_AND (Var F_C) (BinOp OP_EQ r x)))) (armv6m_mov rd r))
  | T_ADD_SP_imm rd imm8 => armv6m_mov rd (BinOp OP_PLUS (Var R_SP) (armv6m_word (imm8 * 4)))
  | T_ADD_SP_SP_imm imm7 => Move R_SP (BinOp OP_PLUS (Var R_SP) (armv6m_word (imm7 * 4)))
  | T_ADR rd imm8 => armv6m_mov rd (armv6m_word (N.land (a + 4) (N.ones 32 - 3) + imm8 * 4))
  | T_SUBS_3reg rd rn rm => armv6m_subs rd (armv6m_var a rn) (armv6m_var a rm)
  | T_SUBS_imm3 rd rn imm3 => armv6m_subs rd (armv6m_var a rn) (armv6m_word imm3)
  | T_SUBS_imm8 rd imm8 => armv6m_subs rd (armv6m_var a rd) (armv6m_word imm8)
  | T_SBCS rd rm => let x := armv6m_var a rd in let y := armv6m_var a rm in let r := Var (V_TEMP 0) in Seq (Move (V_TEMP 0) (BinOp OP_PLUS (BinOp OP_PLUS x (UnOp OP_NOT y)) (Cast CAST_UNSIGNED 32 (Var F_C)))) (Seq (armv6m_subflags x y r (BinOp OP_OR (BinOp OP_LT y x) (BinOp OP_AND (Var F_C) (BinOp OP_EQ x y)))) (armv6m_mov rd r))
  | T_SUB_SP_imm imm7 => Move R_SP (BinOp OP_MINUS (Var R_SP) (armv6m_word (imm7 * 4)))
  | T_RSBS rd rn => armv6m_subs rd (Word 0 32) (armv6m_var a rn)
  | T_MULS rd rm => armv6m_logic rd (BinOp OP_TIMES (armv6m_var a rd) (armv6m_var a rm))
  | T_CMP_reg rn rm => let x := armv6m_var a rn in let y := armv6m_var a rm in armv6m_subflags x y (BinOp OP_MINUS x y) (BinOp OP_LE y x)
  | T_CMN rn rm => let x := armv6m_var a rn in let y := armv6m_var a rm in armv6m_addflags x y (BinOp OP_PLUS x y) (BinOp OP_LT (BinOp OP_PLUS x y) x)
  | T_CMP_imm rn imm8 => let x := armv6m_var a rn in let y := armv6m_word imm8 in armv6m_subflags x y (BinOp OP_MINUS x y) (BinOp OP_LE y x)
  | T_ANDS rd rm => armv6m_logic rd (BinOp OP_AND (armv6m_var a rd) (armv6m_var a rm))
  | T_EORS rd rm => armv6m_logic rd (BinOp OP_XOR (armv6m_var a rd) (armv6m_var a rm))
  | T_ORRS rd rm => armv6m_logic rd (BinOp OP_OR (armv6m_var a rd) (armv6m_var a rm))
  | T_BICS rd rm => armv6m_logic rd (BinOp OP_AND (armv6m_var a rd) (UnOp OP_NOT (armv6m_var a rm)))
  | T_MVNS rd rm => armv6m_logic rd (UnOp OP_NOT (armv6m_var a rm))
  | T_TST rn rm => armv6m_setnz (BinOp OP_AND (armv6m_var a rn) (armv6m_var a rm))
  (* Shifts by immediate (an LSR/ASR amount of 0 encodes 32) *)
  | T_LSLS_imm rd rm imm5 => Seq (Move F_C (Cast CAST_LOW 1 (BinOp OP_RSHIFT (armv6m_var a rm) (armv6m_word (32 - imm5))))) (armv6m_logic rd (BinOp OP_LSHIFT (armv6m_var a rm) (armv6m_word imm5)))
  | T_LSRS_imm rd rm imm5 => let sh := if imm5 =? 0 then 32 else imm5 in Seq (Move F_C (Cast CAST_LOW 1 (BinOp OP_RSHIFT (armv6m_var a rm) (armv6m_word (sh - 1))))) (armv6m_logic rd (BinOp OP_RSHIFT (armv6m_var a rm) (armv6m_word sh)))
  | T_ASRS_imm rd rm imm5 => let sh := if imm5 =? 0 then 32 else imm5 in Seq (Move F_C (Cast CAST_LOW 1 (BinOp OP_ARSHIFT (armv6m_var a rm) (armv6m_word (sh - 1))))) (armv6m_logic rd (BinOp OP_ARSHIFT (armv6m_var a rm) (armv6m_word sh)))
  (* Shifts by register (the amount is rm's bottom byte; C is unchanged if it is 0) *)
  | T_LSLS_reg rd rm => let x := armv6m_var a rd in let sh := BinOp OP_AND (armv6m_var a rm) (Word 255 32) in Seq (If (BinOp OP_EQ sh (Word 0 32)) Nop (Move F_C (Ite (BinOp OP_LE sh (Word 32 32)) (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (BinOp OP_MINUS (Word 32 32) sh))) (Word 0 1)))) (armv6m_logic rd (BinOp OP_LSHIFT x sh))
  | T_LSRS_reg rd rm => let x := armv6m_var a rd in let sh := BinOp OP_AND (armv6m_var a rm) (Word 255 32) in Seq (If (BinOp OP_EQ sh (Word 0 32)) Nop (Move F_C (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (BinOp OP_MINUS sh (Word 1 32)))))) (armv6m_logic rd (BinOp OP_RSHIFT x sh))
  | T_ASRS_reg rd rm => let x := armv6m_var a rd in let sh := BinOp OP_AND (armv6m_var a rm) (Word 255 32) in Seq (If (BinOp OP_EQ sh (Word 0 32)) Nop (Move F_C (Cast CAST_LOW 1 (BinOp OP_ARSHIFT x (BinOp OP_MINUS sh (Word 1 32)))))) (armv6m_logic rd (BinOp OP_ARSHIFT x sh))
  | T_RORS rd rm => let x := armv6m_var a rd in let sh := BinOp OP_AND (armv6m_var a rm) (Word 255 32) in Seq (If (BinOp OP_EQ sh (Word 0 32)) Nop (Move F_C (Cast CAST_HIGH 1 (armv6m_ror x sh)))) (armv6m_logic rd (armv6m_ror x sh))
  | T_LDR_imm rt rn imm5 => armv6m_mov rt (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word (imm5 * 4))) LittleE 4)
  | T_LDRH_imm rt rn imm5 => armv6m_mov rt (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word (imm5 * 2))) LittleE 2))
  | T_LDRB_imm rt rn imm5 => armv6m_mov rt (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word imm5)) LittleE 1))
  | T_LDR_reg rt rn rm => armv6m_mov rt (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) LittleE 4)
  | T_LDRH_reg rt rn rm => armv6m_mov rt (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) LittleE 2))
  | T_LDRSH_reg rt rn rm => armv6m_mov rt (Cast CAST_SIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) LittleE 2))
  | T_LDRB_reg rt rn rm => armv6m_mov rt (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) LittleE 1))
  | T_LDRSB_reg rt rn rm => armv6m_mov rt (Cast CAST_SIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) LittleE 1))
  | T_LDR_pc rt imm8 => armv6m_mov rt (Load (Var V_MEM32) (armv6m_word (N.land (a + 4) (N.ones 32 - 3) + imm8 * 4)) LittleE 4)
  | T_LDR_sp rt imm8 => armv6m_mov rt (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_SP) (armv6m_word (imm8 * 4))) LittleE 4)
  | T_STR_imm rt rn imm5 => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word (imm5 * 4))) (armv6m_var a rt) LittleE 4)
  | T_STRH_imm rt rn imm5 => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word (imm5 * 2))) (Cast CAST_LOW 16 (armv6m_var a rt)) LittleE 2)
  | T_STRB_imm rt rn imm5 => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_word imm5)) (Cast CAST_LOW 8 (armv6m_var a rt)) LittleE 1)
  | T_STR_reg rt rn rm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) (armv6m_var a rt) LittleE 4)
  | T_STRH_reg rt rn rm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) (Cast CAST_LOW 16 (armv6m_var a rt)) LittleE 2)
  | T_STRB_reg rt rn rm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (armv6m_var a rn) (armv6m_var a rm)) (Cast CAST_LOW 8 (armv6m_var a rt)) LittleE 1)
  | T_STR_sp rt imm8 => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_SP) (armv6m_word (imm8 * 4))) (armv6m_var a rt) LittleE 4)
  | T_LDM rn rl => armv6m_ldm rn rl
  | T_STM rn rl => armv6m_stm rn rl
  | T_PUSH rl lr => armv6m_push rl lr
  | T_POP rl pc => armv6m_pop rl pc
  | T_B_cond c off => If (armv6m_cond c) (Jmp (armv6m_target a off)) Nop
  | T_B off => Jmp (armv6m_target a off)
  | T_BL off => Seq (Move R_LR (armv6m_word (N.lor (a + 4) 1))) (Jmp (armv6m_target a off))
  | T_BX rm => armv6m_bxwritepc (armv6m_var a rm)
  | T_BLX rm => Seq (Move (V_TEMP 0) (armv6m_var a rm)) (Seq (Move R_LR (armv6m_word (N.lor (a + 2) 1))) (armv6m_bxwritepc (Var (V_TEMP 0))))
  | T_SXTH rd rm => armv6m_mov rd (Cast CAST_SIGNED 32 (Cast CAST_LOW 16 (armv6m_var a rm)))
  | T_SXTB rd rm => armv6m_mov rd (Cast CAST_SIGNED 32 (Cast CAST_LOW 8 (armv6m_var a rm)))
  | T_UXTH rd rm => armv6m_mov rd (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 16 (armv6m_var a rm)))
  | T_UXTB rd rm => armv6m_mov rd (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 8 (armv6m_var a rm)))
  | T_REV rd rm => let x := armv6m_var a rm in armv6m_mov rd (BinOp OP_OR (BinOp OP_LSHIFT x (Word 24 32)) (BinOp OP_OR (BinOp OP_AND (BinOp OP_LSHIFT x (Word 8 32)) (Word 0xff0000 32)) (BinOp OP_OR (BinOp OP_AND (BinOp OP_RSHIFT x (Word 8 32)) (Word 0xff00 32)) (BinOp OP_RSHIFT x (Word 24 32)))))
  | T_REV16 rd rm => let x := armv6m_var a rm in armv6m_mov rd (BinOp OP_OR (BinOp OP_AND (BinOp OP_LSHIFT x (Word 8 32)) (Word 0xff00ff00 32)) (BinOp OP_AND (BinOp OP_RSHIFT x (Word 8 32)) (Word 0x00ff00ff 32)))
  | T_REVSH rd rm => let x := armv6m_var a rm in armv6m_mov rd (Cast CAST_SIGNED 32 (Cast CAST_LOW 16 (BinOp OP_OR (BinOp OP_LSHIFT x (Word 8 32)) (BinOp OP_AND (BinOp OP_RSHIFT x (Word 8 32)) (Word 0xff 32)))))
  | T_NOP | T_SEV | T_WFE | T_WFI | T_YIELD => Nop
  | T_DMB | T_DSB | T_ISB => Nop
  | T_BKPT _ => Exn 3
  | T_SVC _ => Exn 11
  | T_CPSID | T_CPSIE => Nop   (* PRIMASK is not modeled *)
  (* Only MSP (the current SP, as CONTROL.SPSEL = 0) and the APSR are modeled *)
  | T_MRS rd sysm => if sysm <? 4 then armv6m_mov rd armv6m_apsr else if sysm <? 8 then armv6m_mov rd (Word 0 32) else if sysm =? 8 then armv6m_mov rd (Var R_SP) else armv6m_mov rd (Unknown 32)
  | T_MSR sysm rn => let x := armv6m_var a rn in if sysm <? 4 then Seq (Move F_N (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (Word 31 32)))) (Seq (Move F_Z (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (Word 30 32)))) (Seq (Move F_C (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (Word 29 32)))) (Move F_V (Cast CAST_LOW 1 (BinOp OP_RSHIFT x (Word 28 32)))))) else if sysm <? 8 then Nop else if sysm =? 8 then Move R_SP (BinOp OP_AND x (Word (N.ones 32 - 3) 32)) else Nop
  end.

(* The size and IL of the instruction at a, given the halfword at each address *)
Definition armv6m_decode_at (hw : addr -> N) (a : addr) :=
  if is_32bit_insn (hw a) then (4, arm2il a (thumb32_decode (hw a) (hw ((a + 2) mod 2^32))))
  else (2, arm2il a (thumb16_decode (hw a))).

Definition armv6m_stmt m a :=
  match a mod 2 with
  | 0 => armv6m_decode_at (getmem 32 LittleE 2 m) a
  | _ => (2, arm2il a T_Invalid)
  end.

Definition armv6m_prog : program :=
  fun s a => if N.testbit (s A_EXEC) a then Some (armv6m_stmt (s V_MEM32) a) else None.

(* The literal-pool word loaded by LDR Rt, [PC, #imm8*4] at a *)
Definition armv6m_literal (binary : addr -> N) (a : addr) imm8 :=
  let la := (N.land (a + 4) (N.ones 32 - 3) + imm8 * 4) mod 2^32 in
  binary la + binary ((la + 2) mod 2^32) * 2^16.

(* Lifts a binary of halfwords (from armv6m_lifter.sh), resolving literal-pool
   loads to constants, which assumes the code is unmodified (e.g., in flash).
   The result is Some at every address, so automation needn't decode to see it. *)
Definition lift_armv6m (binary : addr -> N) (s : store) (a : addr) :=
  Some (if is_32bit_insn (binary a) then armv6m_decode_at binary a
        else match thumb16_decode (binary a) with
             | T_LDR_pc rt imm8 => (2, armv6m_mov rt (armv6m_word (armv6m_literal binary a imm8)))
             | _ => armv6m_decode_at binary a
             end).

(* ========================================================================== *)
(*                         TYPE SAFETY                                        *)
(* ========================================================================== *)

Lemma armv6m_varid_typ: forall n, armv6mtypctx (armv6m_varid n) = Some 32.
Proof. intro. destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ]. Qed.

Lemma armv6m_subset_typ:
  forall c v w (SS: armv6mtypctx ⊆ c) (TV: armv6mtypctx v = Some w), c v = Some w.
Proof. intros. apply SS, TV. Qed.

Lemma armv6m_subset_temp:
  forall c n (SS: armv6mtypctx ⊆ c), armv6mtypctx ⊆ c[V_TEMP n := Some 32].
Proof. intros c n SS v w H. rewrite update_frame. apply SS, H. intro. subst. discriminate. Qed.

Lemma hastyp_armv6m_varid:
  forall c n (SS: armv6mtypctx ⊆ c), hastyp_exp c (Var (armv6m_varid n)) 32.
Proof. intros. apply TVar, SS, armv6m_varid_typ. Qed.

Lemma hastyp_armv6m_var:
  forall c a n (SS: armv6mtypctx ⊆ c), hastyp_exp c (armv6m_var a n) 32.
Proof. intros. unfold armv6m_var. destruct (n =? 15). apply TWord, N.mod_lt. discriminate. apply hastyp_armv6m_varid, SS. Qed.

Lemma hastyp_armv6m_word: forall c n, hastyp_exp c (armv6m_word n) 32.
Proof. intros. apply TWord, N.mod_lt. discriminate. Qed.

Lemma hastyp_armv6m_move:
  forall c v w e (SS: armv6mtypctx ⊆ c) (TV: armv6mtypctx v = Some w) (TE: hastyp_exp c e w),
  hastyp_stmt armv6mtypctx c (Move v e) c.
Proof.
  intros. eapply TMove.
    right. exact TV.
    exact TE.
    intros v' w' H. unfold update. destruct (v' == v).
      subst. rewrite (SS _ _ TV) in H. exact H.
      exact H.
Qed.

Lemma hastyp_armv6m_mov:
  forall c n e (SS: armv6mtypctx ⊆ c) (TE: hastyp_exp c e 32),
  hastyp_stmt armv6mtypctx c (armv6m_mov n e) c.
Proof. intros. eapply hastyp_armv6m_move. exact SS. apply armv6m_varid_typ. exact TE. Qed.

Lemma hastyp_armv6m_temp:
  forall c n e (TE: hastyp_exp c e 32),
  hastyp_stmt armv6mtypctx c (Move (V_TEMP n) e) (c[V_TEMP n := Some 32]).
Proof. intros. eapply TMove. left. reflexivity. exact TE. reflexivity. Qed.

Lemma hastyp_armv6m_seq:
  forall c0 c c1 c2 q1 q2 (TS1: hastyp_stmt c0 c q1 c1) (TS2: hastyp_stmt c0 c1 q2 c2),
  hastyp_stmt c0 c (Seq q1 q2) c2.
Proof. intros. eapply TSeq. exact TS1. exact TS2. reflexivity. Qed.

Lemma hastyp_armv6m_if:
  forall c0 c e q1 q2 (TE: hastyp_exp c e 1)
         (TS1: hastyp_stmt c0 c q1 c) (TS2: hastyp_stmt c0 c q2 c),
  hastyp_stmt c0 c (If e q1 q2) c.
Proof. intros. eapply TIf. exact TE. exact TS1. exact TS2. reflexivity. Qed.

Lemma hastyp_armv6m_seqlist:
  forall c qs (TS: Forall (fun q => hastyp_stmt armv6mtypctx c q c) qs),
  hastyp_stmt armv6mtypctx c (armv6m_seq qs) c.
Proof.
  intros. induction TS as [|q qs TQ TQS IH].
    apply TNop. reflexivity.
    destruct qs. exact TQ. eapply hastyp_armv6m_seq. exact TQ. exact IH.
Qed.

Lemma Forall_armv6m_map:
  forall {A} (P: stmt -> Prop) (f: A -> stmt) l (H: forall x, P (f x)),
  Forall P (map f l).
Proof. intros. apply Forall_forall. intros q IN. apply in_map_iff in IN. destruct IN as [x [EQ _]]. subst. apply H. Qed.

(* Typing goals in a context c with armv6mtypctx ⊆ c *)
Ltac armv6m_subset :=
  solve [ repeat first [ assumption | reflexivity | apply armv6m_subset_temp ] ].

Ltac armv6m_typexp :=
  lazymatch goal with
  | [ |- hastyp_exp _ (armv6m_var _ _) _ ] => apply hastyp_armv6m_var; armv6m_subset
  | [ |- hastyp_exp _ (armv6m_word _) _ ] => apply hastyp_armv6m_word
  | [ |- hastyp_exp _ (Var (armv6m_varid _)) _ ] => apply hastyp_armv6m_varid; armv6m_subset
  | [ |- hastyp_exp _ (Var (V_TEMP _)) _ ] => apply TVar, update_updated
  | [ |- hastyp_exp _ (Var _) _ ] => apply TVar; eapply armv6m_subset_typ; [ armv6m_subset | reflexivity ]
  | [ |- hastyp_exp _ (Word (ofZ _ _) _) _ ] => apply TWord, ofZ_bound
  | [ |- hastyp_exp _ (Word _ _) _ ] => apply TWord; reflexivity
  | [ |- hastyp_exp _ (Load _ _ _ _) _ ] => eapply TLoad with (w:=32); [ discriminate 1 | armv6m_typexp | armv6m_typexp ]
  | [ |- hastyp_exp _ (Store _ _ _ _ _) _ ] => eapply TStore with (w:=32); [ discriminate 1 | armv6m_typexp | armv6m_typexp | armv6m_typexp ]
  | [ |- hastyp_exp _ (BinOp _ _ _) _ ] => first [ solve [ eapply TBinOp with (w:=32); armv6m_typexp ] | solve [ eapply TBinOp with (w:=1); armv6m_typexp ] ]
  | [ |- hastyp_exp _ (UnOp _ _) _ ] => apply TUnOp; armv6m_typexp
  | [ |- hastyp_exp _ (Cast _ _ _) _ ] => eapply TCast; [ armv6m_typexp | discriminate 1 ]
  | [ |- hastyp_exp _ (Ite _ _ _) _ ] => eapply TIte; armv6m_typexp
  | [ |- hastyp_exp _ (Unknown _) _ ] => apply TUnknown
  end.

Ltac armv6m_typstmt :=
  lazymatch goal with
  | [ |- hastyp_stmt _ _ (Seq _ _) _ ] => eapply hastyp_armv6m_seq; [ armv6m_typstmt | armv6m_typstmt ]
  | [ |- hastyp_stmt _ _ (If _ _ _) _ ] => apply hastyp_armv6m_if; [ armv6m_typexp | armv6m_typstmt | armv6m_typstmt ]
  | [ |- hastyp_stmt _ _ (armv6m_mov _ _) _ ] => apply hastyp_armv6m_mov; [ armv6m_subset | armv6m_typexp ]
  | [ |- hastyp_stmt _ _ (Move (V_TEMP _) _) _ ] => apply hastyp_armv6m_temp; armv6m_typexp
  | [ |- hastyp_stmt _ _ (Move V_MEM32 _) _ ] => eapply hastyp_armv6m_move with (w:=2^32*8); [ armv6m_subset | reflexivity | armv6m_typexp ]
  | [ |- hastyp_stmt _ _ (Move (armv6m_varid _) _) _ ] => eapply hastyp_armv6m_move; [ armv6m_subset | apply armv6m_varid_typ | armv6m_typexp ]
  | [ |- hastyp_stmt _ _ (Move _ _) _ ] => eapply hastyp_armv6m_move; [ armv6m_subset | reflexivity | armv6m_typexp ]
  | [ |- hastyp_stmt _ _ (Jmp _) _ ] => eapply TJmp; [ armv6m_typexp | reflexivity ]
  | [ |- hastyp_stmt _ _ (Exn _) _ ] => apply TExn; reflexivity
  | [ |- hastyp_stmt _ _ Nop _ ] => apply TNop; reflexivity
  end.

Lemma hastyp_armv6m_ldm:
  forall c rn rl (SS: armv6mtypctx ⊆ c), hastyp_stmt armv6mtypctx c (armv6m_ldm rn rl) c.
Proof.
  intros. apply hastyp_armv6m_seqlist. apply Forall_app; split.
    apply Forall_armv6m_map. intro. cbv beta. unfold armv6m_load_slot. armv6m_typstmt.
  apply Forall_app; split.
    apply Forall_armv6m_map. intro. cbv beta. unfold armv6m_load_slot. armv6m_typstmt.
  destruct N.testbit. apply Forall_nil. apply Forall_cons. armv6m_typstmt. apply Forall_nil.
Qed.

Lemma hastyp_armv6m_stm:
  forall c rn rl (SS: armv6mtypctx ⊆ c), hastyp_stmt armv6mtypctx c (armv6m_stm rn rl) c.
Proof.
  intros. apply hastyp_armv6m_seqlist. apply Forall_app; split.
    apply Forall_armv6m_map. intro. cbv beta. unfold armv6m_store_slot. armv6m_typstmt.
    apply Forall_cons. armv6m_typstmt. apply Forall_nil.
Qed.

Lemma hastyp_armv6m_push:
  forall c rl lr (SS: armv6mtypctx ⊆ c), hastyp_stmt armv6mtypctx c (armv6m_push rl lr) c.
Proof.
  intros. apply hastyp_armv6m_seqlist. apply Forall_app; split.
    apply Forall_armv6m_map. intro. cbv beta. unfold armv6m_store_slot. armv6m_typstmt.
    apply Forall_cons. armv6m_typstmt. apply Forall_nil.
Qed.

Lemma hastyp_armv6m_pop:
  forall c rl pc (SS: armv6mtypctx ⊆ c), hastyp_stmt armv6mtypctx c (armv6m_pop rl pc) c.
Proof.
  intros. apply hastyp_armv6m_seqlist. apply Forall_app; split.
    apply Forall_armv6m_map. intro. cbv beta. unfold armv6m_load_slot. armv6m_typstmt.
    apply Forall_cons. armv6m_typstmt. destruct pc.
      apply Forall_cons. unfold armv6m_bxwritepc. armv6m_typstmt. apply Forall_nil.
      apply Forall_nil.
Qed.

Theorem welltyped_arm2il:
  forall a i, exists c', hastyp_stmt armv6mtypctx armv6mtypctx (arm2il a i) c'.
Proof.
  intros. assert (SS: armv6mtypctx ⊆ armv6mtypctx) by reflexivity.
  destruct i; eexists; cbv beta iota zeta delta [arm2il];
  unfold armv6m_logic, armv6m_adds, armv6m_subs, armv6m_addflags, armv6m_subflags,
         armv6m_setnz, armv6m_bxwritepc, armv6m_ror, armv6m_apsr, armv6m_target;
  repeat match goal with |- context [ if ?b then _ else _ ] => destruct b end;
  first [ apply hastyp_armv6m_ldm, SS
        | apply hastyp_armv6m_stm, SS
        | apply hastyp_armv6m_push, SS
        | apply hastyp_armv6m_pop, SS
        | lazymatch goal with [ |- context [ armv6m_cond ?c ] ] => destruct c; cbv beta iota delta [armv6m_cond]; armv6m_typstmt end
        | armv6m_typstmt ].
Qed.

Theorem welltyped_armv6mprog: welltyped_prog armv6mtypctx armv6m_prog.
Proof.
  intros s a. unfold armv6m_prog.
  destruct (N.testbit _ _); [|exact I].
  unfold armv6m_stmt, armv6m_decode_at. destruct (a mod 2); [ destruct is_32bit_insn |];
  apply welltyped_arm2il.
Qed.

Theorem welltyped_lift_armv6m:
  forall binary, welltyped_prog armv6mtypctx (lift_armv6m binary).
Proof.
  intros binary s a. unfold lift_armv6m, armv6m_decode_at.
  destruct is_32bit_insn. apply welltyped_arm2il.
  destruct (thumb16_decode (binary a)); try apply welltyped_arm2il.
  eexists. apply hastyp_armv6m_mov. reflexivity. apply hastyp_armv6m_word.
Qed.

(* armv6m_cond_val is the value of a condition's IL encoding *)
Theorem armv6m_cond_val_eval:
  forall s c, eval_exp armv6mtypctx s (armv6m_cond c) (armv6m_cond_val s c) 1.
Proof.
  intros. destruct c; cbv [armv6m_cond armv6m_cond_val];
  repeat first [ eapply EBinOp with (n1:=s F_N) (n2:=s F_V) (w:=1)
               | eapply EBinOp with (w:=1)
               | econstructor ].
Qed.
