(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2023 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Instantiation of Picinae for PILbox64 ISA.          MMMMMMMMMMMMMMMMM^NZMMN+Z
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
Require Export Picinae_auto.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from ARM native code: *)
Inductive pil64var :=
  (* Main memory: 64 bit-width addresses, 2^64 bytes *)
  | V_MEM64
  (* 0-5, SP, LR = 64bit registers. *)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5
  (* SP = stack pointer *)
  | R_SP
  (* LR = link register *)
  | R_LR
  (* PC = program counter *)
  | R_PC
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE | A_EXEC.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition pil64typctx (id:pil64var) : option N :=
  match id with
  | V_MEM64 => Some (8*2^64)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 => Some 64
  | R_SP | R_LR | R_PC => Some 64
  | A_READ | A_WRITE | A_EXEC => Some (2^64)
end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniPIL64VarEq <: MiniDecidableType.
  Definition t := pil64var.
  Definition eq_dec (v1 v2:pil64var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniPIL64VarEq.

Module PIL64Arch <: Architecture.
  Module Var := Make_UDT MiniPIL64VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := pil64typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End PIL64Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_pil64 := PicinaeIL PIL64Arch.
Export IL_pil64.
Module Theory_pil64 := PicinaeTheory IL_pil64.
Export Theory_pil64.
Module Statics_pil64 := PicinaeStatics IL_pil64 Theory_pil64.
Export Statics_pil64.
Module Auto_pil64 := PicinaeAuto IL_pil64 Theory_pil64 Statics_pil64.
Export Auto_pil64.
Module FInterp_pil64 := PicinaeFInterp IL_pil64 Theory_pil64 Statics_pil64.
Export FInterp_pil64.
Module PSimpl_pil64 := Picinae_Simplifier_Base IL_pil64.
Export PSimpl_pil64.
Module PSimpl_pil64_v1_1 := Picinae_Simplifier_v1_1 IL_pil64 Theory_pil64 Statics_pil64 FInterp_pil64.
Ltac PSimpl_pil64.PSimplifier ::= PSimpl_pil64_v1_1.PSimplifier.

Module ISA_pil64 := Picinae_ISA IL_pil64 PSimpl_pil64 Theory_pil64 Statics_pil64 FInterp_pil64.
Export ISA_pil64.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "pil64_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "pil64_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "pil64_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "pil64_psimpl" := psimpl_goal.
Ltac pil64_step := ISA_step.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_pil64_v1_0 := Picinae_Simplifier_v1_0 IL_pil64 Statics_pil64 FInterp_pil64.
Ltac PSimpl_pil64.PSimplifier ::= PSimpl_pil64_v1_0.PSimplifier.
*)

(* Declare which context values are used to define store equivalence *)
Definition pil64equivctx (id:var) : bool :=
  match id with
  | V_MEM64
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5
  | R_SP | R_LR => true
  | _ => false
  end.
Definition pil64equiv (s1 s2:store) :=
  forall (v:pil64var), pil64equivctx v = true -> s1 v = s2 v.
Definition pil64equiv_or (s1 s2:store) (or_exception : pil64var -> bool) :=
  forall (v:pil64var), pil64equivctx v = true -> or_exception v = true \/ s1 v = s2 v.

(* TODO: how should we change the memory access machinery?
         How does it work anyhoo? *)
(* Simplify memory access propositions by observing that on arm, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)

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

(* Simplify arm memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* Define ISA-specific notations: *)

Declare Scope pil64_scope.
Delimit Scope pil64_scope with pil64.
Bind Scope pil64_scope with stmt exp trace.
Open Scope pil64_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : pil64_scope.

Module PIL64Notations.

Notation "m Ⓑ[ a  ]" := (getmem 64 LittleE 1 m a) (at level 30) : pil64_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 64 LittleE 2 m a) (at level 30) : pil64_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 64 LittleE 4 m a) (at level 30) : pil64_scope. (* read dword from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 64 LittleE 1 m a v) (at level 50, left associativity) : pil64_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 64 LittleE 2 m a v) (at level 50, left associativity) : pil64_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 64 LittleE 4 m a v) (at level 50, left associativity) : pil64_scope. (* write dword to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^64) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 64 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^64) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 64 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End PIL64Notations.
