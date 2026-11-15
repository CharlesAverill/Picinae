(* Picinae: Platform In Coq for INstruction Analysis of Executables

   Copyright (c) 2026 Kevin W. Hamlen
   The University of Texas at Dallas
   Computer Science Department

   Any use, commercial or otherwise
   requires the express permission of
   the author.

   Instantiation of Picinae for Ghidra-lifted SuperH SH-2.
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

Inductive sh2var :=
  | V_MEM32
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 | R_R13 | R_R14 | R_R15
  | R_SR | R_GBR | R_VBR | R_MACH | R_MACL | R_PR | R_PC
  | A_READ | A_WRITE | A_EXEC
  | V_TEMP (n:N).

Definition sh2typctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | A_READ | A_WRITE | A_EXEC => Some (2^32)
  | V_TEMP _ => None
  | _ => Some 32
  end.

Module MiniSH2VarEq <: MiniDecidableType.
  Definition t := sh2var.
  Definition eq_dec (v1 v2:sh2var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.
  Arguments eq_dec v1 v2 : simpl never.
End MiniSH2VarEq.

Module SH2Arch <: Architecture.
  Module Var := Make_UDT MiniSH2VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := sh2typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End SH2Arch.

Module IL_sh2 := PicinaeIL SH2Arch.
Export IL_sh2.
Module Theory_sh2 := PicinaeTheory IL_sh2.
Export Theory_sh2.
Module Statics_sh2 := PicinaeStatics IL_sh2 Theory_sh2.
Export Statics_sh2.
Module Auto_sh2 := PicinaeAuto IL_sh2 Theory_sh2 Statics_sh2.
Export Auto_sh2.
Module FInterp_sh2 := PicinaeFInterp IL_sh2 Theory_sh2 Statics_sh2.
Export FInterp_sh2.
Module PSimpl_sh2 := Picinae_Simplifier_Base IL_sh2.
Export PSimpl_sh2.
Module PSimpl_sh2_v1_1 := Picinae_Simplifier_v1_1 IL_sh2 Theory_sh2 Statics_sh2 FInterp_sh2.
Ltac PSimpl_sh2.PSimplifier ::= PSimpl_sh2_v1_1.PSimplifier.
Module ISA_sh2 := Picinae_ISA IL_sh2 PSimpl_sh2 Theory_sh2 Statics_sh2 FInterp_sh2.
Export ISA_sh2.

Tactic Notation "sh2_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "sh2_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "sh2_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "sh2_psimpl" := psimpl_goal.
Ltac sh2_step := ISA_step.

Theorem memacc_respects_sh2typctx: memacc_respects_typctx sh2typctx.
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

Declare Scope sh2_scope.
Delimit Scope sh2_scope with sh2.
Bind Scope sh2_scope with stmt exp trace.
Open Scope sh2_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : sh2_scope.

Module SH2Notations.

Notation "m Ⓑ[ a  ]" := (getmem 32 BigE 1 m a) (at level 30) : sh2_scope.
Notation "m Ⓦ[ a  ]" := (getmem 32 BigE 2 m a) (at level 30) : sh2_scope.
Notation "m Ⓓ[ a  ]" := (getmem 32 BigE 4 m a) (at level 30) : sh2_scope.
Notation "m [Ⓑ  a := v  ]" := (setmem 32 BigE 1 m a v) (at level 50, left associativity) : sh2_scope.
Notation "m [Ⓦ  a := v  ]" := (setmem 32 BigE 2 m a v) (at level 50, left associativity) : sh2_scope.
Notation "m [Ⓓ  a := v  ]" := (setmem 32 BigE 4 m a v) (at level 50, left associativity) : sh2_scope.
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity).
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity).
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity).
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity).
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity).
Notation "x .& y" := (N.land x y) (at level 56, left associativity).
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity).
Notation "x .| y" := (N.lor x y) (at level 58, left associativity).

End SH2Notations.
