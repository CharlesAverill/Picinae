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
   Instantiation of Picinae for ARMv7 ISA.             MMMMMMMMMMMMMMMMM^NZMMN+Z
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
Inductive arm7var :=
  (* Main memory: support both 32 bit(ARMv1-v8) mode and 64 bit(ARMv8) *)
  | V_MEM32 | V_MEM64
  (* Floating point (VFP) support and SIMD (NEON) are optional extensions to the ARMv7-A profile.*)
  (* ARM’s pc register is analogous to IA-32’s EIP register *)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12
  (* R13: stack pointer | R14: link register | R15: program counter *)
  | R_SP | R_LR | R_PC
  (* Current Program Status Register (CPSR)*)
  | R_M (* (bits 0–4) are the processor mode bits.*)
  | R_T (* (bit 5) is the Thumb state bit. *)
  | R_F (* (bit 6) is the FIQ disable bit. *)
  | R_I (* (bit 7) is the IRQ disable bit. *)
  | R_A (* (bit 8) is the imprecise data abort disable bit. *)
  | R_E (* (bit 9) is the data endianness bit. *)
  | R_IT (* (bits 10–15 and 25–26) is the if-then state bits. *)
  | R_GE (* (bits 16–19) is the greater-than-or-equal-to bits. *)
  | R_DNM (* (bits 20–23) is the do not modify bits. *)
  | R_JF (* (bit 24) is the Java state bit. *)
  | R_QF (* (bit 27) is the sticky overflow bit. *)
  | R_VF (* (bit 28) is the overflow bit. *)
  | R_CF (* (bit 29) is the carry/borrow/extend bit. *)
  | R_ZF (* (bit 30) is the zero bit. *)
  | R_NF (* (bit 31) is the negative/less than bit. *)
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  | V_TEMP (n:N) (* Temporaries introduced by the lifter: *).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition arm7typctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | V_MEM64 => Some (8*2^64)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7 => Some 32
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 => Some 32
  | R_SP | R_LR | R_PC => Some 32
  | R_M => Some 5
  | R_T | R_F | R_I | R_A | R_E => Some 1
  | R_IT => Some 8
  | R_GE => Some 4
  | R_DNM => Some 4
  | R_JF | R_QF | R_VF | R_CF | R_ZF | R_NF => Some 1
  | A_READ | A_WRITE => Some (2^64)
  | V_TEMP _ => None
end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniARM7VarEq <: MiniDecidableType.
  Definition t := arm7var.
  Definition eq_dec (v1 v2:arm7var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniARM7VarEq.

Module ARM7Arch <: Architecture.
  Module Var := Make_UDT MiniARM7VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := arm7typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End ARM7Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_arm7 := PicinaeIL ARM7Arch.
Export IL_arm7.
Module Theory_arm7 := PicinaeTheory IL_arm7.
Export Theory_arm7.
Module Statics_arm7 := PicinaeStatics IL_arm7 Theory_arm7.
Export Statics_arm7.
Module FInterp_arm7 := PicinaeFInterp IL_arm7 Theory_arm7 Statics_arm7.
Export FInterp_arm7.
Module PSimpl_arm7 := Picinae_Simplifier_Base IL_arm7.
Export PSimpl_arm7.
Module PSimpl_arm7_v1_1 := Picinae_Simplifier_v1_1 IL_arm7 Theory_arm7 Statics_arm7 FInterp_arm7.
Ltac PSimpl_arm7.PSimplifier ::= PSimpl_arm7_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_arm7_v1_0 := Picinae_Simplifier_v1_0 IL_arm7 Theory_arm7 Statics_arm7 FInterp_arm7.
Ltac PSimpl_arm7.PSimplifier ::= PSimpl_arm7_v1_0.PSimplifier.
*)

Module ISA_arm7 := Picinae_ISA IL_arm7 PSimpl_arm7 Theory_arm7 Statics_arm7 FInterp_arm7.
Export ISA_arm7.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "arm7_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "arm7_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "arm7_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "arm7_psimpl" := psimpl_goal.
Ltac arm7_step := ISA_step.

(* The following is needed when applying cframe theorems from Picinae_theory. *)
Theorem memacc_respects_arm7typctx: memacc_respects_typctx arm7typctx.
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

Declare Scope arm7_scope.
Delimit Scope arm7_scope with arm7.
Bind Scope arm7_scope with stmt exp trace.
Open Scope arm7_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : arm7_scope.

Module ARM7Notations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : arm7_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : arm7_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : arm7_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : arm7_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 32 LittleE 16 m a) (at level 30) : arm7_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 32 LittleE 32 m a) (at level 30) : arm7_scope. (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : arm7_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : arm7_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : arm7_scope. (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : arm7_scope. (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem 32 LittleE 16 m a v) (at level 50, left associativity) : arm7_scope. (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem 32 LittleE 32 m a v) (at level 50, left associativity) : arm7_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End ARM7Notations.
