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
   Instantiation of Picinae for Ghidra-lifted ARM8.    MMMMMMMMMMMMMMMMM^NZMMN+Z
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

(* Variables found in IL code lifted from ARM native code: *)
Inductive arm8var :=
  (* Main memory: support both 32 bit(ARMv1-v8) mode and 64 bit(ARMv8) *)
  | V_MEM32 | V_MEM64
  (* X0-30 = 64bit registers. No need to explicitly define W0-30 since lifted code addresses the lower 32 bits when using W registers *)
  | R_X0 | R_X1 | R_X2 | R_X3 | R_X4 | R_X5 | R_X6 | R_X7 | R_X8 | R_X9 | R_X10
  | R_X11 | R_X12 | R_X13 | R_X14 | R_X15 | R_X16 | R_X17 | R_X18 | R_X19 | R_X20
  | R_X21 | R_X22 | R_X23 | R_X24 | R_X25 | R_X26 | R_X27 | R_X28 | R_X29 | R_X30
  (* SP = stack pointer *)
  | R_SP | R_LR | R_PC
  (* ng = negative, zr = zero reg, cy = carry, ov = overflow *)
  | R_NG | R_ZR | R_CY | R_OV
  (* for modeling how the cpu handles flag updates *)
  | R_TMPNG | R_TMPZR | R_TMPCY | R_TMPOV
  (* zero reg *)
  | R_XZR
  (* FP/SIMD registers *)
  | R_Z0 | R_Z1 | R_Z2 | R_Z3 | R_Z4 | R_Z5 | R_Z6 | R_Z7 | R_Z8 | R_Z9 | R_Z10
  | R_Z11 | R_Z12 | R_Z13 | R_Z14 | R_Z15 | R_Z16 | R_Z17 | R_Z18 | R_Z19 | R_Z20
  | R_Z21 | R_Z22 | R_Z23 | R_Z24 | R_Z25 | R_Z26 | R_Z27 | R_Z28 | R_Z29 | R_Z30 | R_Z31
  (* explicit registers for SIMD semantics calculations *)
  | R_TMPZ0 | R_TMPZ1 | R_TMPZ2 | R_TMPZ3 | R_TMPZ4 | R_TMPZ5 | R_TMPZ6
  | R_TMP_LDXN
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  | V_TEMP (n:N) (* Temporaries introduced by the lifter: *).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition arm8typctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | V_MEM64 => Some (8*2^64)
  | R_X0 | R_X1 | R_X2 | R_X3 | R_X4 | R_X5 | R_X6 | R_X7 | R_X8 | R_X9 | R_X10 => Some 64
  | R_X11 | R_X12 | R_X13 | R_X14 | R_X15 | R_X16 | R_X17 | R_X18 | R_X19 | R_X20 => Some 64
  | R_X21 | R_X22 | R_X23 | R_X24 | R_X25 | R_X26 | R_X27 | R_X28 | R_X29 | R_X30 => Some 64
  | R_XZR => Some 64
  | R_SP | R_LR | R_PC => Some 64
  | R_NG | R_ZR | R_CY | R_OV => Some 8
  | R_TMPNG | R_TMPZR | R_TMPCY | R_TMPOV => Some 8
  | A_READ | A_WRITE => Some (2^64)
  | V_TEMP _ => None
  | R_Z0 | R_Z1 | R_Z2 | R_Z3 | R_Z4 | R_Z5 | R_Z6 | R_Z7 | R_Z8 | R_Z9 | R_Z10 => Some 256
  | R_Z11 | R_Z12 | R_Z13 | R_Z14 | R_Z15 | R_Z16 | R_Z17 | R_Z18 | R_Z19 | R_Z20 => Some 256
  | R_Z21 | R_Z22 | R_Z23 | R_Z24 | R_Z25 | R_Z26 | R_Z27 | R_Z28 | R_Z29 | R_Z30 | R_Z31 => Some 256
  | R_TMPZ0 | R_TMPZ1 | R_TMPZ2 | R_TMPZ3 | R_TMPZ4 | R_TMPZ5 | R_TMPZ6 => Some 256
  | R_TMP_LDXN => Some 64
end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniARM8VarEq <: MiniDecidableType.
  Definition t := arm8var.
  Definition eq_dec (v1 v2:arm8var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniARM8VarEq.

Module ARM8Arch <: Architecture.
  Module Var := Make_UDT MiniARM8VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := arm8typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End ARM8Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_arm8 := PicinaeIL ARM8Arch.
Export IL_arm8.
Module Theory_arm8 := PicinaeTheory IL_arm8.
Export Theory_arm8.
Module Statics_arm8 := PicinaeStatics IL_arm8 Theory_arm8.
Export Statics_arm8.
Module FInterp_arm8 := PicinaeFInterp IL_arm8 Theory_arm8 Statics_arm8.
Export FInterp_arm8.
Module PSimpl_arm8 := Picinae_Simplifier_Base IL_arm8.
Export PSimpl_arm8.
Module PSimpl_arm8_v1_1 := Picinae_Simplifier_v1_1 IL_arm8 Theory_arm8 Statics_arm8 FInterp_arm8.
Ltac PSimpl_arm8.PSimplifier ::= PSimpl_arm8_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_arm8_v1_0 := Picinae_Simplifier_v1_0 IL_arm8 Theory_arm8 Statics_arm8 FInterp_arm8.
Ltac PSimpl_arm8.PSimplifier ::= PSimpl_arm8_v1_0.PSimplifier.
*)

Module ISA_arm8 := Picinae_ISA IL_arm8 PSimpl_arm8 Theory_arm8 Statics_arm8 FInterp_arm8.
Export ISA_arm8.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "arm8_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "arm8_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "arm8_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "arm8_psimpl" := psimpl_goal.
Ltac arm8_step := ISA_step.

(* The following is needed when applying cframe theorems from Picinae_theory. *)
Theorem memacc_respects_arm8typctx: memacc_respects_typctx arm8typctx.
Proof.
  intros s1 s2 RV. rewrite <- RV. split; reflexivity.
Qed.

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

(* Simplify arm memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* Define ISA-specific notations: *)

Declare Scope arm8_scope.
Delimit Scope arm8_scope with arm8.
Bind Scope arm8_scope with stmt exp trace.
Open Scope arm8_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : arm8_scope.

Module ARM8Notations.

Notation "m Ⓑ[ a  ]" := (getmem 64 LittleE 1 m a) (at level 30) : arm8_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 64 LittleE 2 m a) (at level 30) : arm8_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 64 LittleE 4 m a) (at level 30) : arm8_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 64 LittleE 8 m a) (at level 30) : arm8_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 64 LittleE 16 m a) (at level 30) : arm8_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 64 LittleE 32 m a) (at level 30) : arm8_scope. (* read ymm from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 64 LittleE 1 m a v) (at level 50, left associativity) : arm8_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 64 LittleE 2 m a v) (at level 50, left associativity) : arm8_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 64 LittleE 4 m a v) (at level 50, left associativity) : arm8_scope. (* write dword to memory *)
Notation "m [Ⓠ  a := v  ]" := (setmem 64 LittleE 8 m a v) (at level 50, left associativity) : arm8_scope. (* write quad word to memory *)
Notation "m [Ⓧ  a := v  ]" := (setmem 64 LittleE 16 m a v) (at level 50, left associativity) : arm8_scope. (* write xmm to memory *)
Notation "m [Ⓨ  a := v  ]" := (setmem 64 LittleE 32 m a v) (at level 50, left associativity) : arm8_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^64) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 64 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^64) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 64 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End ARM8Notations.
