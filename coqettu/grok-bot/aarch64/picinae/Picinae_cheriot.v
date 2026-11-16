(* Picinae: Platform In Coq for INstruction Analysis of Executables

   Copyright (c) 2026 Kevin W. Hamlen
   The University of Texas at Dallas
   Computer Science Department

   Any use, commercial or otherwise
   requires the express permission of
   the author.

   Instantiation of Picinae for Ghidra-lifted CHERIoT.

   To compile this module, first load and compile:
   * Picinae_core
   * Picinae_theory
   * Picinae_statics
   * Picinae_finterp
   * Picinae_simplifier_*
   * Picinae_ISA
   Then compile this module with menu option
   Compile->Compile_buffer.
 *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_auto.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
From Stdlib Require Import NArith.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from CHERIoT native code: *)
Inductive cheriotvar :=
  | V_MEM32
  | V_CTAGRAM | V_CREVOCATION | V_CSR
  (* Sixteen 64-bit general capabilities. Integer registers are their low words. *)
  | R_CNULL | R_CRA | R_CSP | R_CGP | R_CTP | R_CT0 | R_CT1 | R_CT2
  | R_CS0 | R_CS1 | R_CA0 | R_CA1 | R_CA2 | R_CA3 | R_CA4 | R_CA5
  | R_CTAG0 | R_CTAG1 | R_CTAG2 | R_CTAG3 | R_CTAG4 | R_CTAG5 | R_CTAG6 | R_CTAG7
  | R_CTAG8 | R_CTAG9 | R_CTAG10 | R_CTAG11 | R_CTAG12 | R_CTAG13 | R_CTAG14 | R_CTAG15
  (* Special capabilities and their tags. PC is the low word of PCC. *)
  | R_PCC | R_MTCC | R_MTDC | R_MSCRATCHC | R_MEPCC
  | R_PCC_TAG | R_MTCC_TAG | R_MTDC_TAG | R_MSCRATCHC_TAG | R_MEPCC_TAG
  (* Load-reservation state. *)
  | R_RESERVE_ADDRESS | R_RESERVE | R_RESERVE_LENGTH
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE | A_EXEC
  | V_TEMP (n:N) (* Temporaries introduced by the lifter: *).

(* Declare the types (i.e., bitwidths) of all CPU registers and memories.
   CSR p-code uses 16-bit word addresses; the lifter scales these by four to
   byte addresses in V_CSR so consecutive 32-bit CSRs do not overlap. *)
Definition cheriottypctx v :=
  match v with
  | V_MEM32 | V_CTAGRAM | V_CREVOCATION | V_CSR => Some (8*2^32)
  | R_CNULL | R_CRA | R_CSP | R_CGP | R_CTP | R_CT0 | R_CT1 | R_CT2
  | R_CS0 | R_CS1 | R_CA0 | R_CA1 | R_CA2 | R_CA3 | R_CA4 | R_CA5 => Some 64
  | R_PCC | R_MTCC | R_MTDC | R_MSCRATCHC | R_MEPCC => Some 64
  | R_CTAG0 | R_CTAG1 | R_CTAG2 | R_CTAG3 | R_CTAG4 | R_CTAG5 | R_CTAG6 | R_CTAG7
  | R_CTAG8 | R_CTAG9 | R_CTAG10 | R_CTAG11 | R_CTAG12 | R_CTAG13 | R_CTAG14 | R_CTAG15
  | R_PCC_TAG | R_MTCC_TAG | R_MTDC_TAG | R_MSCRATCHC_TAG | R_MEPCC_TAG
  | R_RESERVE | R_RESERVE_LENGTH => Some 8
  | R_RESERVE_ADDRESS => Some 32
  | A_READ | A_WRITE | A_EXEC => Some (2^32)
  | V_TEMP _ => None
  end.

Module MiniCHERIoTVarEq <: MiniDecidableType.
  Definition t := cheriotvar.
  Definition eq_dec (v1 v2:cheriotvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniCHERIoTVarEq.

Module CHERIoTArch <: Architecture.
  Module Var := Make_UDT MiniCHERIoTVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := cheriottypctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End CHERIoTArch.

Module IL_cheriot := PicinaeIL CHERIoTArch.
Export IL_cheriot.
Module Theory_cheriot := PicinaeTheory IL_cheriot.
Export Theory_cheriot.
Module Statics_cheriot := PicinaeStatics IL_cheriot Theory_cheriot.
Export Statics_cheriot.
Module Auto_cheriot := PicinaeAuto IL_cheriot Theory_cheriot Statics_cheriot.
Export Auto_cheriot.
Module FInterp_cheriot := PicinaeFInterp IL_cheriot Theory_cheriot Statics_cheriot.
Export FInterp_cheriot.
Module PSimpl_cheriot := Picinae_Simplifier_Base IL_cheriot.
Export PSimpl_cheriot.
Module PSimpl_cheriot_v1_1 := Picinae_Simplifier_v1_1 IL_cheriot Theory_cheriot Statics_cheriot FInterp_cheriot.
Ltac PSimpl_cheriot.PSimplifier ::= PSimpl_cheriot_v1_1.PSimplifier.
Module ISA_cheriot := Picinae_ISA IL_cheriot PSimpl_cheriot Theory_cheriot Statics_cheriot FInterp_cheriot.
Export ISA_cheriot.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "cheriot_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "cheriot_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "cheriot_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "cheriot_psimpl" := psimpl_goal.
Ltac cheriot_step := ISA_step.

Theorem memacc_respects_cheriottypctx: memacc_respects_typctx cheriottypctx.
Proof.
  intros s1 s2 RV. rewrite <- RV. split; reflexivity.
Qed.

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.

Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

Declare Scope cheriot_scope.
Delimit Scope cheriot_scope with cheriot.
Bind Scope cheriot_scope with stmt exp trace.
Open Scope cheriot_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : cheriot_scope.

Module CHERIoTNotations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : cheriot_scope.
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : cheriot_scope.
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : cheriot_scope.
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : cheriot_scope.
Notation "m [Ⓑ  a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : cheriot_scope.
Notation "m [Ⓦ  a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : cheriot_scope.
Notation "m [Ⓓ  a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : cheriot_scope.
Notation "m [Ⓠ  a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : cheriot_scope.
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity).
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity).
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity).
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity).
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity).
Notation "x .& y" := (N.land x y) (at level 56, left associativity).
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity).
Notation "x .| y" := (N.lor x y) (at level 58, left associativity).

End CHERIoTNotations.
