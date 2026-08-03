(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2025 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Instantiation of Picinae for Ghidra-lifted TOY.    MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_statics                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_finterp                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_simplifier_*                                     MDMMMMMMMO.7MDM7M+
   * Picinae_ISA                                               ZMMMMMMMM.$MM8$MN
   Then compile this module with menu option                   $ZMMMMMMZ..MMMOMZ
   Compile->Compile_buffer.                                     ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from TOY native code: *)
Inductive toyvar :=
  | V_MEM32
  | R_0 | R_1 | R_2 | R_3 | R_4 | R_5 | R_SP | R_PC
  | F_GT | F_LT | F_EQ
  | V_TEMP (n:N).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition toytypctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | R_0 | R_1 | R_2 | R_3 | R_4 | R_5 | R_SP | R_PC => Some 32
  | F_GT | F_LT | F_EQ => Some 1
  | V_TEMP _ => None
end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniTOYVarEq <: MiniDecidableType.
  Definition t := toyvar.
  Definition eq_dec (v1 v2:toyvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniTOYVarEq.

Module TOYArch <: Architecture.
  Module Var := Make_UDT MiniTOYVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := toytypctx.

  Definition mem_readable (s:store) (a:addr) := True.
  Definition mem_writable (s:store) (a:addr) := True.
End TOYArch.

(* Instantiate the Picinae modules with the toy identifiers above. *)
Module IL_toy := PicinaeIL TOYArch.
Export IL_toy.
Module Theory_toy := PicinaeTheory IL_toy.
Export Theory_toy.
Module Statics_toy := PicinaeStatics IL_toy Theory_toy.
Export Statics_toy.
Module FInterp_toy := PicinaeFInterp IL_toy Theory_toy Statics_toy.
Export FInterp_toy.
Module PSimpl_toy := Picinae_Simplifier_Base IL_toy.
Export PSimpl_toy.
Module PSimpl_toy_v1_1 := Picinae_Simplifier_v1_1 IL_toy Theory_toy Statics_toy FInterp_toy.
Ltac PSimpl_toy.PSimplifier ::= PSimpl_toy_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_toy_v1_0 := Picinae_Simplifier_v1_0 IL_toy Theory_toy Statics_toy FInterp_toy.
Ltac PSimpl_toy.PSimplifier ::= PSimpl_toy_v1_0.PSimplifier.
*)

Module ISA_toy := Picinae_ISA IL_toy PSimpl_toy Theory_toy Statics_toy FInterp_toy.
Export ISA_toy.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "toy_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "toy_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "toy_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "toy_psimpl" := psimpl_goal.
Ltac toy_step := ISA_step.

(* The following is needed when applying cframe theorems from Picinae_theory. *)
Theorem memacc_respects_toytypctx: memacc_respects_typctx toytypctx.
Proof.
  intros s1 s2 RV. rewrite <- RV. split; reflexivity.
Qed.

(* Simplify memory access propositions by observing that on toy, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)
(**)
(*Lemma memacc_read_frame:*)
(*  forall s v u (NE: v <> A_READ),*)
(*  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.*)
(*Proof.*)
(*  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.*)
(*  apply not_eq_sym. exact NE.*)
(*Qed.*)
(**)
(*Lemma memacc_write_frame:*)
(*  forall s v u (NE: v <> A_WRITE),*)
(*  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.*)
(*Proof.*)
(*  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.*)
(*  apply not_eq_sym. exact NE.*)
(*Qed.*)
(**)
(*Lemma memacc_read_updated:*)
(*  forall s v u1 u2,*)
(*  MemAcc mem_readable (update (update s v u2) A_READ u1) =*)
(*  MemAcc mem_readable (update s A_READ u1).*)
(*Proof.*)
(*  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.*)
(*Qed.*)
(**)
(*Lemma memacc_write_updated:*)
(*  forall s v u1 u2,*)
(*  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =*)
(*  MemAcc mem_writable (update s A_WRITE u1).*)
(*Proof.*)
(*  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.*)
(*Qed.*)
(**)
(* Simplify toy memory access assertions produced by step_stmt. *)
(*Ltac simpl_memaccs H ::=*)
(*  try lazymatch type of H with context [ MemAcc mem_writable ] =>*)
(*    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1*)
(*  end;*)
(*  try lazymatch type of H with context [ MemAcc mem_readable ] =>*)
(*    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1*)
(*  end.*)
Ltac simpl_memaccs H ::= idtac.

(* Define ISA-specific notations: *)

Declare Scope toy_scope.
Delimit Scope toy_scope with toy.
Bind Scope toy_scope with stmt exp trace.
Open Scope toy_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : toy_scope.

Module TOYNotations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : toy_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : toy_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : toy_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : toy_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 32 LittleE 16 m a) (at level 30) : toy_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 32 LittleE 32 m a) (at level 30) : toy_scope. (* read ymm from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : toy_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : toy_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : toy_scope. (* write dword to memory *)
Notation "m [Ⓠ  a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : toy_scope. (* write quad word to memory *)
Notation "m [Ⓧ  a := v  ]" := (setmem 32 LittleE 16 m a v) (at level 50, left associativity) : toy_scope. (* write xmm to memory *)
Notation "m [Ⓨ  a := v  ]" := (setmem 32 LittleE 32 m a v) (at level 50, left associativity) : toy_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end) (right associativity, at level 60) : toy_scope.

Notation "'_' <- e1 ;; e2" := (match e1 with
                               | Some _ => e2
                               | None => None
                               end) (right associativity, at level 60) : toy_scope.
End TOYNotations.
