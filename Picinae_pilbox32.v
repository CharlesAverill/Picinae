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
   Instantiation of Picinae for PILbox32 ISA.          MMMMMMMMMMMMMMMMM^NZMMN+Z
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
Inductive pil32var :=
  (* Main memory: 32 bit-width addresses, 2^32 bytes *)
  | V_MEM32
  (* 0-5, SP, LR = 32bit registers. *)
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
Definition pil32typctx (id:pil32var) : option N :=
  match id with
  | V_MEM32 => Some (8*2^32)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 => Some 32
  | R_SP | R_LR | R_PC => Some 32
  | A_READ | A_WRITE | A_EXEC => Some (2^32)
end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniPIL32VarEq <: MiniDecidableType.
  Definition t := pil32var.
  Definition eq_dec (v1 v2:pil32var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniPIL32VarEq.

Module PIL32Arch <: Architecture.
  Module Var := Make_UDT MiniPIL32VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := pil32typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End PIL32Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_pil32 := PicinaeIL PIL32Arch.
Export IL_pil32.
Module Theory_pil32 := PicinaeTheory IL_pil32.
Export Theory_pil32.
Module Statics_pil32 := PicinaeStatics IL_pil32 Theory_pil32.
Export Statics_pil32.
Module Auto_pil32 := PicinaeAuto IL_pil32 Theory_pil32 Statics_pil32.
Export Auto_pil32.
Module FInterp_pil32 := PicinaeFInterp IL_pil32 Theory_pil32 Statics_pil32.
Export FInterp_pil32.
Module PSimpl_pil32 := Picinae_Simplifier_Base IL_pil32.
Export PSimpl_pil32.
Module PSimpl_pil32_v1_1 := Picinae_Simplifier_v1_1 IL_pil32 Theory_pil32 Statics_pil32 FInterp_pil32.
Ltac PSimpl_pil32.PSimplifier ::= PSimpl_pil32_v1_1.PSimplifier.

Module ISA_pil32 := Picinae_ISA IL_pil32 PSimpl_pil32 Theory_pil32 Statics_pil32 FInterp_pil32.
Export ISA_pil32.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "pil32_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "pil32_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "pil32_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "pil32_psimpl" := psimpl_goal.
Ltac pil32_step := ISA_step.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_pil32_v1_0 := Picinae_Simplifier_v1_0 IL_pil32 Statics_pil32 FInterp_pil32.
Ltac PSimpl_pil32.PSimplifier ::= PSimpl_pil32_v1_0.PSimplifier.
*)

(* Declare which context values are used to define store equivalence *)
Definition pil32equivctx (id:var) : bool :=
  match id with
  | V_MEM32
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5
  | R_SP | R_LR => true
  | _ => false
  end.
Definition pil32equiv (s1 s2:store) :=
  forall (v:pil32var), pil32equivctx v = true -> s1 v = s2 v.
Definition pil32equiv_or (s1 s2:store) (or_exception : pil32var -> bool) :=
  forall (v:pil32var), pil32equivctx v = true -> or_exception v = true \/ s1 v = s2 v.

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

Declare Scope pil32_scope.
Delimit Scope pil32_scope with pil32.
Bind Scope pil32_scope with stmt exp trace.
Open Scope pil32_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : pil32_scope.

Module PIL32Notations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : pil32_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : pil32_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : pil32_scope. (* read dword from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : pil32_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : pil32_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : pil32_scope. (* write dword to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End PIL32Notations.
