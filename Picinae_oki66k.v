(* Picinae: Platform In Coq for INstruction Analysis of Executables

   Copyright (c) 2026 Kevin W. Hamlen
   The University of Texas at Dallas
   Computer Science Department

   Any use, commercial or otherwise
   requires the express permission of
   the author.

   Instantiation of Picinae for Ghidra-lifted Oki nX-8/500S.
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

Inductive oki66kvar :=
  | V_ROM32 | V_RAM16
  | R_SSP | R_LRB | R_PSW | R_ACC | R_PC | R_X1 | R_X2 | R_DP | R_USP
  | R_CSR | R_TSR | R_DSR | R_ROMWIN
  | R_C | R_Z | R_HC | R_S | R_OV
  | A_READ | A_WRITE | A_EXEC
  | V_TEMP (n:N).

Definition oki66ktypctx v :=
  match v with
  | V_ROM32 => Some (8*2^32)
  | V_RAM16 => Some (8*2^16)
  | R_SSP | R_LRB | R_PSW | R_ACC | R_PC | R_X1 | R_X2 | R_DP | R_USP => Some 16
  | R_CSR | R_TSR | R_DSR | R_ROMWIN | R_C | R_Z | R_HC | R_S | R_OV => Some 8
  | A_READ | A_WRITE | A_EXEC => Some (2^32)
  | V_TEMP _ => None
  end.

Module MiniOKI66KVarEq <: MiniDecidableType.
  Definition t := oki66kvar.
  Definition eq_dec (v1 v2:oki66kvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.
  Arguments eq_dec v1 v2 : simpl never.
End MiniOKI66KVarEq.

Module OKI66KArch <: Architecture.
  Module Var := Make_UDT MiniOKI66KVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := oki66ktypctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End OKI66KArch.

Module IL_oki66k := PicinaeIL OKI66KArch.
Export IL_oki66k.
Module Theory_oki66k := PicinaeTheory IL_oki66k.
Export Theory_oki66k.
Module Statics_oki66k := PicinaeStatics IL_oki66k Theory_oki66k.
Export Statics_oki66k.
Module Auto_oki66k := PicinaeAuto IL_oki66k Theory_oki66k Statics_oki66k.
Export Auto_oki66k.
Module FInterp_oki66k := PicinaeFInterp IL_oki66k Theory_oki66k Statics_oki66k.
Export FInterp_oki66k.
Module PSimpl_oki66k := Picinae_Simplifier_Base IL_oki66k.
Export PSimpl_oki66k.
Module PSimpl_oki66k_v1_1 := Picinae_Simplifier_v1_1 IL_oki66k Theory_oki66k Statics_oki66k FInterp_oki66k.
Ltac PSimpl_oki66k.PSimplifier ::= PSimpl_oki66k_v1_1.PSimplifier.
Module ISA_oki66k := Picinae_ISA IL_oki66k PSimpl_oki66k Theory_oki66k Statics_oki66k FInterp_oki66k.
Export ISA_oki66k.

Tactic Notation "oki66k_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "oki66k_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "oki66k_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "oki66k_psimpl" := psimpl_goal.
Ltac oki66k_step := ISA_step.

Theorem memacc_respects_oki66ktypctx: memacc_respects_typctx oki66ktypctx.
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

Declare Scope oki66k_scope.
Delimit Scope oki66k_scope with oki66k.
Bind Scope oki66k_scope with stmt exp trace.
Open Scope oki66k_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : oki66k_scope.

Module OKI66KNotations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : oki66k_scope.
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : oki66k_scope.
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : oki66k_scope.
Notation "m [Ⓑ  a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : oki66k_scope.
Notation "m [Ⓦ  a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : oki66k_scope.
Notation "m [Ⓓ  a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : oki66k_scope.
Notation "x ⊕ y" := ((x+y) mod 2^16) (at level 50, left associativity).
Notation "x ⊖ y" := (msub 16 x y) (at level 50, left associativity).
Notation "x ⊗ y" := ((x*y) mod 2^16) (at level 40, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity).
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity).
Notation "x >>> y" := (ashiftr 16 x y) (at level 55, left associativity).
Notation "x .& y" := (N.land x y) (at level 56, left associativity).
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity).
Notation "x .| y" := (N.lor x y) (at level 58, left associativity).

End OKI66KNotations.
