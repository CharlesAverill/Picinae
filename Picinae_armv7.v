(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2022 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Instantiation of Picinae for ARM ISA.               MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_finterp                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_slogic                                           MDMMMMMMMO.7MDM7M+
   Then compile this module with menu option                   ZMMMMMMMM.$MM8$MN
   Compile->Compile_buffer.                                    $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
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
Require Export Picinae_slogic.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from ARM native code: *)
Inductive arm7var :=
  (* Main memory: swap between 32 bit(ARMv1-v8) mode and 64 bit(ARMv8) *)
  | V_MEM32 | V_MEM64
  (* no equivalent of the segment registers*)
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
  | V_TEMP (n:N) (* Temporaries introduced by the BIL lifter: *).

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
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 32 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 32 /\ w a <> 0.
End ARM7Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_arm7 := PicinaeIL ARM7Arch.
Export IL_arm7.
Module Theory_arm7 := PicinaeTheory IL_arm7.
Export Theory_arm7.
Module Statics_arm7 := PicinaeStatics IL_arm7.
Export Statics_arm7.
Module FInterp_arm7 := PicinaeFInterp IL_arm7 Statics_arm7.
Export FInterp_arm7.
Module SLogic_arm7 := PicinaeSLogic IL_arm7.
Export SLogic_arm7.

Module PSimpl_arm7 := Picinae_Simplifier_Base.
Export PSimpl_arm7.
Module PSimpl_arm7_v1_1 := Picinae_Simplifier_v1_1 IL_arm7 Statics_arm7 FInterp_arm7.
Ltac PSimpl_arm7.PSimplifier ::= PSimpl_arm7_v1_1.PSimplifier.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "arm7_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "arm7_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "arm7_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "arm7_psimpl" := psimpl_goal.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_arm7_v1_0 := Picinae_Simplifier_v1_0 IL_arm7 Statics_arm7 FInterp_arm7.
Ltac PSimpl_arm7.PSimplifier ::= PSimpl_arm7_v1_0.PSimplifier.
*)

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition arm7typctx (id:var) : option typ :=
  match id with
  | V_MEM32 => Some (MemT 32)
  | V_MEM64 => Some (MemT 64)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7 => Some (NumT 32)
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 => Some (NumT 32)
  | R_SP | R_LR | R_PC => Some (NumT 32)
  | R_M => Some (NumT 5)
  | R_T | R_F | R_I | R_A | R_E => Some (NumT 1)
  | R_IT => Some (NumT 8)
  | R_GE => Some (NumT 4)
  | R_DNM => Some (NumT 4)
  | R_JF | R_QF | R_VF | R_CF | R_ZF | R_NF => Some (NumT 1)
  | A_READ | A_WRITE => Some (MemT 32)
  | V_TEMP _ => None
end.

Definition arm7_wtm {s v m w} := @models_wtm v arm7typctx s m w.
Definition arm7_regsize {s v n w} := @models_regsize v arm7typctx s n w.

(* Simplify memory access propositions by observing that on arm, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)

Lemma memacc_read_frame:
  forall h s v u (NE: v <> A_READ),
  MemAcc mem_readable h (update s v u) = MemAcc mem_readable h s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall h s v u (NE: v <> A_WRITE),
  MemAcc mem_writable h (update s v u) = MemAcc mem_writable h s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall h s v u1 u2,
  MemAcc mem_readable h (update (update s v u2) A_READ u1) =
  MemAcc mem_readable h (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall h s v u1 u2,
  MemAcc mem_writable h (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable h (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.


(* Simplify arm memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* Values of IL temp variables are ignored by the arm interpreter once the IL
   block that generated them completes.  We can therefore generalize them
   away at IL block boundaries to simplify the expression. *)
Ltac generalize_temps H :=
  repeat match type of H with context [ update ?s (V_TEMP ?n) ?u ] =>
    tryif is_var u then fail else
    lazymatch type of H with context [ Var (V_TEMP ?n) ] => fail | _ =>
      let tmp := fresh "tmp" in
      pose (tmp := u);
      change (update s (V_TEMP n) u) with (update s (V_TEMP n) tmp) in H;
      clearbody tmp;
      try fold value in tmp
    end
  end.

(* Symbolically evaluate an arm machine instruction for one step, and simplify
   the resulting Coq expressions. *)
Ltac arm7_step_and_simplify XS :=
  step_stmt XS;
  psimpl in XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  generalize_temps XS.

(* Introduce automated machinery for verifying an x86 machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine.

   In order for this methodology to prove that a post-condition holds at
   subroutine exit, we must attach one of these invariants (the post-condition)
   to the return address of the subroutine.  This is a somewhat delicate
   process, since unlike most other code addresses, the exact value of the
   return address is an unknown (defined by the caller).  We therefore adopt
   the convention that subroutines "exit" whenever control flows to an address
   for which no IL code is defined at that address.  This allows proving
   correctness of a subroutine by lifting only the subroutine to IL code (or
   using the pmono theorems from Picinae_theory to isolate only the subroutine
   from a larger program), leaving the non-subroutine code undefined (None). *)

(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).
   This slow-down can be avoided by sequestering prevalent injections into
   lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Exit a. Proof eq_refl.
Remark exitof_some a x: exitof a (Some x) = x. Proof eq_refl.


(* Solve a goal of the form (p s a = None), which indicates that program p is
   exiting the subroutine.  For now, we automatically solve for three common
   cases: (A) address a is a constant, allowing function p to fully evaluate
   (reflexivity); (B) the goal is an assumption, or (C) the code is immutable,
   so there is an assumption of the form (H: forall s, p s a = None) for a
   particular return address a.  Cases other than these three forms will need
   to be solved manually by the user. *)
Ltac prove_prog_exits :=
  solve [ reflexivity | assumption |
    match goal with [ H: forall s, ?p s ?a = None |- ?p _ ?a = None ] => apply H end ].

(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac arm7_invhere :=
  first [ eapply nextinv_here; [reflexivity|]
        | apply nextinv_exn
        | apply nextinv_ret; [ prove_prog_exits |] ];
  psimpl.

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac arm7_invseek :=
  apply NIStep; [reflexivity|];
  let sz := fresh "sz" in let q := fresh "q" in let s := fresh "s" in let x := fresh "x" in
  let IL := fresh "IL" in let XS := fresh "XS" in
  intros sz q s x IL XS;
  apply inj_prog_stmt in IL; destruct IL; subst sz q;
  arm7_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             arm7_step_and_simplify XS
         | exec_stmt _ _ (N.iter _ _ _) _ _ => fail
         | _ => arm7_step_and_simplify XS
         end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac arm7_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ arm7_invseek; try arm7_invhere | arm7_invhere ].


Declare Scope arm7_scope.
Delimit Scope arm7_scope with arm7.
Bind Scope arm7_scope with stmt exp typ.
Open Scope arm7_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : arm7_scope.

Module ARM7Notations.

Notation "Ⓜ m" := (VaM m 32) (at level 20). (* memory value *)
Notation "ⓑ u" := (VaN u 1) (at level 20). (* bit value *)
Notation "Ⓑ u" := (VaN u 8) (at level 20). (* byte value *)
Notation "Ⓦ u" := (VaN u 16) (at level 20). (* word value *)
Notation "Ⓓ u" := (VaN u 32) (at level 20). (* dword value *)
Notation "Ⓠ u" := (VaN u 64) (at level 20). (* quad word value *)
Notation "Ⓧ u" := (VaN u 128) (at level 20). (* xmm value *)
Notation "Ⓨ u" := (VaN u 256) (at level 20). (* ymm value *)
Notation "m Ⓑ[ a  ]" := (getmem LittleE 1 m a) (at level 10) : arm7_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem LittleE 2 m a) (at level 10) : arm7_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem LittleE 4 m a) (at level 10) : arm7_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem LittleE 8 m a) (at level 10) : arm7_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem LittleE 16 m a) (at level 10) : arm7_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem LittleE 32 m a) (at level 10) : arm7_scope. (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem LittleE 1 m a v) (at level 50, left associativity) : arm7_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem LittleE 2 m a v) (at level 50, left associativity) : arm7_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem LittleE 4 m a v) (at level 50, left associativity) : arm7_scope. (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem LittleE 8 m a v) (at level 50, left associativity) : arm7_scope. (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem LittleE 16 m a v) (at level 50, left associativity) : arm7_scope. (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem LittleE 32 m a v) (at level 50, left associativity) : arm7_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := ((x-y) mod 2^32) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 40, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 25, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 25, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 25, left associativity). (* logical or *)

End ARM7Notations.