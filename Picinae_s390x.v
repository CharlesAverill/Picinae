(* Picinae: Platform In Coq for INstruction Analysis of Executables

   Copyright (c) 2026 Kevin W. Hamlen
   The University of Texas at Dallas
   Computer Science Department

   Any use, commercial or otherwise
   requires the express permission of
   the author.

   Instantiation of Picinae for Ghidra-lifted s390x.

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

(* Variables found in IL code lifted from s390x native code: *)
Inductive s390xvar :=
  | V_MEM64
  (* General registers; 32-bit operands are extracted from these by the lifter. *)
  | R_GR0 | R_GR1 | R_GR2 | R_GR3 | R_GR4 | R_GR5 | R_GR6 | R_GR7
  | R_GR8 | R_GR9 | R_GR10 | R_GR11 | R_GR12 | R_GR13 | R_GR14 | R_GR15
  (* Access registers. *)
  | R_AR0 | R_AR1 | R_AR2 | R_AR3 | R_AR4 | R_AR5 | R_AR6 | R_AR7
  | R_AR8 | R_AR9 | R_AR10 | R_AR11 | R_AR12 | R_AR13 | R_AR14 | R_AR15
  (* Control registers. *)
  | R_C0 | R_C1 | R_C2 | R_C3 | R_C4 | R_C5 | R_C6 | R_C7
  | R_C8 | R_C9 | R_C10 | R_C11 | R_C12 | R_C13 | R_C14 | R_C15
  (* Floating-point registers and their 128-bit extended-precision views. *)
  | R_FP0 | R_FP1 | R_FP2 | R_FP3 | R_FP4 | R_FP5 | R_FP6 | R_FP7
  | R_FP8 | R_FP9 | R_FP10 | R_FP11 | R_FP12 | R_FP13 | R_FP14 | R_FP15
  | R_XFP0 | R_XFP1 | R_XFP2 | R_XFP3 | R_XFP4 | R_XFP5 | R_XFP6 | R_XFP7
  | R_XFP8 | R_XFP9 | R_XFP10 | R_XFP11 | R_XFP12 | R_XFP13 | R_XFP14 | R_XFP15
  | R_PC | R_CC | R_FPC
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  | V_TEMP (n:N) (* Temporaries introduced by the lifter: *).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition s390xtypctx v :=
  match v with
  | V_MEM64 => Some (8*2^64)
  | R_GR0 | R_GR1 | R_GR2 | R_GR3 | R_GR4 | R_GR5 | R_GR6 | R_GR7
  | R_GR8 | R_GR9 | R_GR10 | R_GR11 | R_GR12 | R_GR13 | R_GR14 | R_GR15 => Some 64
  | R_AR0 | R_AR1 | R_AR2 | R_AR3 | R_AR4 | R_AR5 | R_AR6 | R_AR7
  | R_AR8 | R_AR9 | R_AR10 | R_AR11 | R_AR12 | R_AR13 | R_AR14 | R_AR15 => Some 32
  | R_C0 | R_C1 | R_C2 | R_C3 | R_C4 | R_C5 | R_C6 | R_C7
  | R_C8 | R_C9 | R_C10 | R_C11 | R_C12 | R_C13 | R_C14 | R_C15 => Some 64
  | R_FP0 | R_FP1 | R_FP2 | R_FP3 | R_FP4 | R_FP5 | R_FP6 | R_FP7
  | R_FP8 | R_FP9 | R_FP10 | R_FP11 | R_FP12 | R_FP13 | R_FP14 | R_FP15 => Some 64
  | R_XFP0 | R_XFP1 | R_XFP2 | R_XFP3 | R_XFP4 | R_XFP5 | R_XFP6 | R_XFP7
  | R_XFP8 | R_XFP9 | R_XFP10 | R_XFP11 | R_XFP12 | R_XFP13 | R_XFP14 | R_XFP15 => Some 128
  | R_PC => Some 64
  | R_CC => Some 8
  | R_FPC => Some 32
  | A_READ | A_WRITE => Some (2^64)
  | V_TEMP _ => None
  end.

Module MiniS390XVarEq <: MiniDecidableType.
  Definition t := s390xvar.
  Definition eq_dec (v1 v2:s390xvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniS390XVarEq.

Module S390XArch <: Architecture.
  Module Var := Make_UDT MiniS390XVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := s390xtypctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End S390XArch.

(* Instantiate the Picinae modules with the s390x identifiers above. *)
Module IL_s390x := PicinaeIL S390XArch.
Export IL_s390x.
Module Theory_s390x := PicinaeTheory IL_s390x.
Export Theory_s390x.

Module Statics_s390x := PicinaeStatics IL_s390x Theory_s390x.
Export Statics_s390x.
Module Auto_s390x := PicinaeAuto IL_s390x Theory_s390x Statics_s390x.
Export Auto_s390x.
Module FInterp_s390x := PicinaeFInterp IL_s390x Theory_s390x Statics_s390x.
Export FInterp_s390x.
Module PSimpl_s390x := Picinae_Simplifier_Base IL_s390x.
Export PSimpl_s390x.

Module PSimpl_s390x_v1_1 := Picinae_Simplifier_v1_1 IL_s390x Theory_s390x Statics_s390x FInterp_s390x.

Ltac PSimpl_s390x.PSimplifier ::= PSimpl_s390x_v1_1.PSimplifier.

Module ISA_s390x := Picinae_ISA IL_s390x PSimpl_s390x Theory_s390x Statics_s390x FInterp_s390x.
Export ISA_s390x.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "s390x_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "s390x_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "s390x_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "s390x_psimpl" := psimpl_goal.
Ltac s390x_step := ISA_step.

(* The following is needed when applying cframe theorems from Picinae_theory. *)
Theorem memacc_respects_s390xtypctx: memacc_respects_typctx s390xtypctx.
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

(* Simplify s390x memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

Declare Scope s390x_scope.
Delimit Scope s390x_scope with s390x.
Bind Scope s390x_scope with stmt exp trace.
Open Scope s390x_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : s390x_scope.

Module S390XNotations.

Notation "m Ⓑ[ a  ]" := (getmem 64 BigE 1 m a) (at level 30) : s390x_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 64 BigE 2 m a) (at level 30) : s390x_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 64 BigE 4 m a) (at level 30) : s390x_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 64 BigE 8 m a) (at level 30) : s390x_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 64 BigE 16 m a) (at level 30) : s390x_scope. (* read extended word from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 64 BigE 1 m a v) (at level 50, left associativity) : s390x_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 64 BigE 2 m a v) (at level 50, left associativity) : s390x_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 64 BigE 4 m a v) (at level 50, left associativity) : s390x_scope. (* write dword to memory *)
Notation "m [Ⓠ  a := v  ]" := (setmem 64 BigE 8 m a v) (at level 50, left associativity) : s390x_scope. (* write quad word to memory *)
Notation "m [Ⓧ  a := v  ]" := (setmem 64 BigE 16 m a v) (at level 50, left associativity) : s390x_scope. (* write extended word to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^64) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 64 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^64) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 64 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End S390XNotations.
