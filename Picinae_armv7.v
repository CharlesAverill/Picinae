(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
Require Export Picinae_finterp.
Require Export Picinae_statics.
Require Export Picinae_slogic.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from ARM native code: *)
Inductive armvar :=
  (* Main memory: swap between 32 bit(ARMv1-v8) mode and 64 bit(ARMv8) *)
  | V_MEM32 | V_MEM64
  (* no equivalent of the segment registers*)
  (* Floating point (VFP) support and SIMD (NEON) are optional extensions to the ARMv7-A profile.*)
  (* ARM’s pc register is analogous to IA-32’s EIP register *)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12
  (*R13, the Stack Pointer |R14, the Link Register| R15, the Program Counter*)
  | R_SP | R_LR | R_PC
  (* Current Program Status Register (CPSR)*)
  | R_M (*(bits 0–4) is the processor mode bits.*)
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

Module MiniARMVarEq <: MiniDecidableType.
  Definition t := armvar.
  Definition eq_dec (v1 v2:armvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniARMVarEq.

Module ARMArch <: Architecture.
  Module Var := Make_UDT MiniARMVarEq.
  Definition var := Var.t.
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 32 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 32 /\ w a <> 0.
End ARMArch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_arm := PicinaeIL ARMArch.
Export IL_arm.
Module Theory_arm := PicinaeTheory IL_arm.
Export Theory_arm.
Module Statics_arm := PicinaeStatics IL_arm.
Export Statics_arm.
Module FInterp_arm := PicinaeFInterp IL_arm Statics_arm.
Export FInterp_arm.
Module SLogic_arm := PicinaeSLogic IL_arm.
Export SLogic_arm.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition armtypctx (id:var) : option typ :=
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

Definition arm_wtm {s v m w} := @models_wtm v armtypctx s m w.
Definition arm_regsize {s v n w} := @models_regsize v armtypctx s n w.

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


(* getmem assembles bytes into words by logical-or'ing them together, but
   sometimes it is easier to reason about them as if they were summed.  The
   following theorem proves that logical-or and addition are the same when
   the operands share no common bits. *)
Theorem lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  intros. rewrite <- N.lxor_lor, N.add_nocarry_lxor by assumption. reflexivity.
Qed.

(* ((width) memory[...]) mod 2^width = (width) memory[...] *)
Lemma memlo: forall len w m a, welltyped_memory m -> Mb*len <= w ->
  (getmem LittleE len m a) mod 2^w = getmem LittleE len m a.
Proof.
  intros. apply N.mod_small. eapply N.lt_le_trans.
    apply getmem_bound. assumption.
    apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

(* (e mod 2^b) mod 2^c = e mod 2^(min b c) *)
Lemma dblmod_l: forall a b c, b <= c -> (a mod 2^b) mod 2^c = a mod 2^b.
Proof.
  intros. repeat rewrite <- N.land_ones.
  rewrite <- N.land_assoc, (N.land_comm (N.ones _)), N.land_ones, N.ones_mod_pow2.
  reflexivity. assumption.
Qed.

Lemma dblmod_r: forall a b c, c <= b -> (a mod 2^b) mod 2^c = a mod 2^c.
Proof.
  intros. repeat rewrite <- N.land_ones.
  rewrite <- N.land_assoc, N.land_ones, N.ones_mod_pow2.
  reflexivity. assumption.
Qed.

(* e & (N.ones w) = e mod 2^w *)
Remark land_mod_r: forall x y z, N.log2 (N.succ y) = N.succ (N.log2 y) -> z = N.log2 (N.succ y) ->
  N.land x y = x mod 2^z.
Proof.
  intros x y z H1 H2. subst z. destruct y.
    rewrite N.mod_1_r. apply N.land_0_r.

    apply N.log2_eq_succ_iff_pow2 in H1; [|reflexivity]. destruct H1 as [b H1].
    rewrite H1, N.log2_pow2 by apply N.le_0_l.
    rewrite <- (N.pred_succ (Npos p)), H1, <- N.ones_equiv.
    apply N.land_ones.
Qed.

(* (a & b) ^ c = (a ^ c) & b whenever b & c = c *)
Lemma lxor_land:
  forall a b c, N.land b c = c -> N.lxor (N.land a b) c = N.land (N.lxor a c) b.
Proof.
 intros. apply N.bits_inj. apply N.bits_inj_iff in H. intro n. specialize (H n).
 do 2 rewrite N.land_spec, N.lxor_spec. rewrite <- H, N.land_spec.
 repeat destruct (N.testbit _ n); reflexivity.
Qed.

Remark land_mod_l: forall x y z, N.log2 (N.succ x) = N.succ (N.log2 x) -> z = N.log2 (N.succ x) ->
  N.land x y = y mod 2^z.
Proof. intros x y. rewrite N.land_comm. apply land_mod_r. Qed.

(* (x*y) mod x = 0 *)
Remark mod_mul_l: forall x y, x<>0 -> (x*y) mod x = 0.
Proof. intros. rewrite N.mul_comm. apply N.mod_mul. assumption. Qed.

(* (x+y) mod x = y mod x *)
Remark mod_add_l: forall x y, x<>0 -> (x+y) mod x = y mod x.
Proof. intros. rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by assumption. reflexivity. Qed.

(* (y+x) mod x = y mod x *)
Remark mod_add_r: forall x y, y<>0 -> (x+y) mod y = x mod y.
Proof. intros. rewrite <- N.add_mod_idemp_r, N.mod_same, N.add_0_r by assumption. reflexivity. Qed.

(* (x*z + y) mod z = y mod z *)
Remark mod_add_mul_lr: forall x y z, z<>0 -> (x*z + y) mod z = y mod z.
Proof. intros. rewrite <- N.add_mod_idemp_l, N.mod_mul, N.add_0_l by assumption. reflexivity. Qed.

(* (z*x + y) mod z = y mod z *)
Remark mod_add_mul_ll: forall x y z, z<>0 -> (z*x + y) mod z = y mod z.
Proof. intros. rewrite <- N.add_mod_idemp_l, mod_mul_l, N.add_0_l by assumption. reflexivity. Qed.

(* (x + y*z) mod z = x mod z *)
Remark mod_add_mul_rr: forall x y z, z<>0 -> (x + y*z) mod z = x mod z.
Proof. intros. rewrite <- N.add_mod_idemp_r, N.mod_mul, N.add_0_r by assumption. reflexivity. Qed.

(* (x + z*y) mod z = x mod z *)
Remark mod_add_mul_rl: forall x y z, z<>0 -> (x + z*y) mod z = x mod z.
Proof. intros. rewrite <- N.add_mod_idemp_r, mod_mul_l, N.add_0_r by assumption. reflexivity. Qed.

(* (mem a) mod 2^8 = mem a *)
Remark mem_small: forall m a, welltyped_memory m -> (m a) mod 2^Mb = m a.
Proof. intros. apply N.mod_small, H. Qed.

(* e << w = 0 whenever e < 2^w *)
Lemma shiftr_low_pow2: forall a n, a < 2^n -> N.shiftr a n = 0.
Proof.
  intros. destruct a. apply N.shiftr_0_l.
  apply N.shiftr_eq_0. apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

(* These nested-ifs arise from conditional branches on status flag expressions. *)
Remark if_if:
  forall (b:bool) (q1 q2:stmt),
  (if (if b then 1 else N0) then q1 else q2) = (if b then q2 else q1).
Proof. intros. destruct b; reflexivity. Qed.

Remark if_not_if:
  forall (b:bool) (q1 q2:stmt),
  (if (N.lnot (if b then 1 else 0) 1) then q1 else q2) = (if b then q1 else q2).
Proof. intros. destruct b; reflexivity. Qed.

Remark if_compare0:
  forall x y, ((if x =? y then 1 else 0) =? 0) = negb (x =? y).
Proof. intros. destruct (x =? y); reflexivity. Qed.

Remark if_compare1:
  forall x y, ((if x =? y then 1 else 0) =? 1) = (x =? y).
Proof. intros. destruct (x =? y); reflexivity. Qed.

Remark if_negb:
  forall A x (y z:A), (if negb x then y else z) = (if x then z else y).
Proof. intros. destruct x; reflexivity. Qed.

(* Implementation note:  The following tactic repeatedly applies all the above
   rewriting lemmas using repeat+rewrite with a long list of lemma names.  This
   seems to be faster than rewrite_strat or autorewrite with a hint database
   (as of Coq 8.8.0).  Consider changing if performance of rewrite_strat or
   autorewrite improves in future Coq versions. *)

Ltac arm_rewrite_rules H :=
  repeat rewrite
     ?N.sub_0_r, ?N.add_0_l, ?N.add_0_r, ?N.mul_0_l, ?N.mul_0_r,
     ?N.land_0_l, ?N.land_0_r, ?N.lor_0_l, ?N.lor_0_r, ?N.lxor_0_l, ?N.lxor_0_r,
     ?N.mul_1_l, ?N.mul_1_r, ?N.lxor_nilpotent,

     ?N.mod_same, ?N.mod_mul, ?dblmod_l, ?dblmod_r, ?mod_mul_l, ?mod_add_l, ?mod_add_r,
     ?mod_add_mul_lr, ?mod_add_mul_ll, ?mod_add_mul_rr, ?mod_add_mul_rl,

     ?lxor_land,

     ?mem_small
    in H by solve [ discriminate 1 | assumption | reflexivity ].


(* When reducing modulo operations, try auto-solving inequalities of the form
   x < 2^w. *)

Ltac solve_lt_prim :=
  reflexivity (* solves "<" relations on closed terms *) +
  eassumption +
  match goal with
  | [ |- _ mod _ < _ ] => apply N.mod_upper_bound; discriminate 1
  | [ M: models armtypctx ?s, R: ?s _ = VaN ?x _ |- ?x < _ ] => apply (arm_regsize M R)
  | [ WTM: welltyped_memory ?m |- ?m _ < _ ] => apply WTM
  | [ |- getmem _ _ _ _ < 2^_ ] => apply getmem_bound; assumption
  | [ |- N.lxor _ _ < 2^_ ] => apply lxor_bound; solve_lt
  | [ |- N.land _ _ < 2^_ ] => apply land_bound; solve_lt
  | [ |- N.lor _ _ < 2^_ ] => apply lor_bound; solve_lt
  | [ |- N.lnot _ _ < 2^_ ] => apply lnot_bound; solve_lt
  end +
  (eapply N.le_lt_trans; [ apply N.le_sub_l | solve_lt ])
with solve_lt :=
  solve_lt_prim +
  (eapply N.lt_le_trans; [ solve_lt_prim | discriminate 1 ]).


(* Try to auto-simplify modular arithmetic expressions within a Coq expression
   resulting from functional interpretation of an arm IL statement. *)

Tactic Notation "simpl_arm" "in" hyp(H) :=
  repeat rewrite ?if_if, ?if_not_if, ?if_compare0, ?if_compare1, ?if_negb in H;
  rewrite ?getmem_1 in H;
  arm_rewrite_rules H;
  repeat (
    match type of H with
    | context [ (getmem LittleE ?len ?m ?a) mod 2^?w ] => rewrite (memlo len w m a) in H; [| assumption | discriminate 1 ]
    | context [ N.shiftr ?x ?y ] => rewrite (shiftr_low_pow2 x y) in H by solve_lt
    | context [ ?x mod ?m ] => rewrite (N.mod_small x m) in H by solve_lt
    | context [ N.land ?x ?y ] => (erewrite (land_mod_r x y) in H +
                                   erewrite (land_mod_l x y) in H); [| reflexivity | simpl;reflexivity ]
    end;
    arm_rewrite_rules H
  ).

Ltac simpl_arm :=
  lazymatch goal with |- ?G => let H := fresh in let Heq := fresh in
    remember G as H eqn:Heq; simpl_arm in Heq; subst H
  end.


(* Introduce automated machinery for verifying an arm machine code subroutine
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
Ltac arm_step_and_simplify XS :=
  step_stmt XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  generalize_temps XS;
  simpl_arm in XS.

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
Ltac arm_invhere :=
  first [ eapply nextinv_here; [reflexivity|]
        | apply nextinv_exn
        | apply nextinv_ret; [ prove_prog_exits |] ];
  simpl_stores; simpl_arm.

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac arm_invseek :=
  apply NIStep; [reflexivity|];
  let sz := fresh "sz" in let q := fresh "q" in let s := fresh "s" in let x := fresh "x" in
  let IL := fresh "IL" in let XS := fresh "XS" in
  intros sz q s x IL XS;
  apply inj_prog_stmt in IL; destruct IL; subst sz q;
  arm_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             arm_step_and_simplify XS
         | exec_stmt _ _ (N.iter _ _ _) _ _ => fail
         | _ => arm_step_and_simplify XS
         end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac arm_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ arm_invseek; try arm_invhere | arm_invhere ].


Module ARMNotations.

Notation "Ⓜ m" := (VaM m 32) (at level 20). (* memory value *)
Notation "ⓑ u" := (VaN u 1) (at level 20). (* bit value *)
Notation "Ⓑ u" := (VaN u 8) (at level 20). (* byte value *)
Notation "Ⓦ u" := (VaN u 16) (at level 20). (* word value *)
Notation "Ⓓ u" := (VaN u 32) (at level 20). (* dword value *)
Notation "Ⓠ u" := (VaN u 64) (at level 20). (* quad word value *)
Notation "Ⓧ u" := (VaN u 128) (at level 20). (* xmm value *)
Notation "Ⓨ u" := (VaN u 256) (at level 20). (* ymm value *)
Notation "m Ⓑ[ a  ]" := (getmem LittleE 1 m a) (at level 10). (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem LittleE 2 m a) (at level 10). (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem LittleE 4 m a) (at level 10). (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem LittleE 8 m a) (at level 10). (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem LittleE 16 m a) (at level 10). (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem LittleE 32 m a) (at level 10). (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem LittleE 1 m a v) (at level 50, left associativity). (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem LittleE 2 m a v) (at level 50, left associativity). (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem LittleE 4 m a v) (at level 50, left associativity). (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem LittleE 8 m a v) (at level 50, left associativity). (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem LittleE 16 m a v) (at level 50, left associativity). (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem LittleE 32 m a v) (at level 50, left associativity). (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := ((x-y) mod 2^32) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 40, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 25, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 25, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 25, left associativity). (* logical or *)

End ARMNotations.

Definition arm7_varid (n:N) := (* TODO Finish implementation *)
  match n with
  | 0 => R_R0
  | _ => R_R1
  end.

Inductive arm7asm :=
| ARM7_And (cond i s rn rd op2:N)
| ARM7_Eor (cond i s rn rd op2:N)
| ARM7_Sub (cond i s rn rd op2:N)
| ARM7_Rsb (cond i s rn rd op2:N)
| ARM7_Add (cond i s rn rd op2:N)
| ARM7_Adc (cond i s rn rd op2:N)
| ARM7_Sbc (cond i s rn rd op2:N)
| ARM7_Rsc (cond i s rn rd op2:N)
| ARM7_Tst (cond i s rn rd op2:N)
| ARM7_Teq (cond i s rn rd op2:N)
| ARM7_Cmp (cond i s rn rd op2:N)
| ARM7_Cmn (cond i s rn rd op2:N)
| ARM7_Orr (cond i s rn rd op2:N)
| ARM7_Mov (cond i s rn rd op2:N)
| ARM7_Bic (cond i s rn rd op2:N)
| ARM7_Mvn (cond i s rn rd op2:N)
| ARM7_InvalidI (cond i s rn rd op2:N)
.

Definition xbits n i j := N.land (N.shiftr n i) (N.ones (j - i)).

Definition arm_decode n :=
  match xbits n 20 24 with
  | 0 => ARM7_And
  | 1 => ARM7_Eor
  | 2 => ARM7_Sub
  | 3 => ARM7_Rsb
  | 4 => ARM7_Add
  | 5 => ARM7_Adc
  | 6 => ARM7_Sbc
  | 7 => ARM7_Rsc
  | 8 => ARM7_Tst
  | 9 => ARM7_Teq
  | 10 => ARM7_Cmp
  | 11 => ARM7_Cmn
  | 12 => ARM7_Orr
  | 13 => ARM7_Mov
  | 14 => ARM7_Bic
  | 15 => ARM7_Mvn
  | _ => ARM7_InvalidI (* TODO Implement other instructions *)
  end (xbits n 27 31) (xbits n 24 25) (xbits n 19 20) (xbits n 15 19) (xbits n 11 15) (xbits n 0 11).

Definition cond_eval cond il :=
  match cond with
  | 0 => If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (il) (Nop)
  | 1 => If (BinOp OP_EQ (Var R_ZF) (Word 1 0)) (il) (Nop)
  | 14 => il
  | _ => il (* TODO Implement other conditions *)
end.

Definition op2shift op2 := xbits op2 6 11.
Definition op2rm op2 := xbits op2 0 3.
Definition op2imm op2 := xbits op2 0 7.
Definition op2rs op2 := xbits op2 7 11.
Definition op2shift_type op2 := match xbits op2 5 7 with | 0 => OP_LSHIFT | 1 => OP_RSHIFT | 2 => OP_ARSHIFT | _ => OP_ROT end.
Definition op2reg_shift_field op2 := xbits op2 3 4.
Definition op2reg_shift_by_amt op2 := xbits op2 6 11.
Definition op2rot op2 := xbits op2 7 11.

Definition op2var i op2 :=
  match i with
  | 0 => Var (arm7_varid (op2rm op2))
  | _ => Word 32 (op2imm op2)
end.

Definition op2eval i op2 :=
  match i with
  | 0 => match op2reg_shift_field op2 with
         (* Shift Rm by the the 6-bit value in bits 6-11 *)
         | 0 => (BinOp (op2shift_type op2) (Var (arm7_varid (op2rm op2))) (Word 32 (op2reg_shift_by_amt op2)))
         (* Shift Rm by the value in the shift register Rs *)
         | _ => (BinOp (op2shift_type op2) (Var (arm7_varid (op2rm op2))) (Var (arm7_varid (op2rs op2))))
         end
  (* Rotate the immediate 8-bit value in bits 0-7 by two times the 4-bit value in bits 8-11. *)
  | _ => BinOp OP_ROT (Word 32 (op2imm op2)) (Word 32 (2 * (op2rot op2)))
  end.

Open Scope stmt_scope.

Definition arm_cpsr_update s rd stmts :=
  match s with
  | 0 => Nop
  | _ => match (arm7_varid rd) with
         | R_PC => Nop
         | _ => stmts
         end
  end.

Definition arm2il (a:addr) armi :=
  match armi with
  | ARM7_And cond i s rn rd op2 => Some(4,
      cond_eval cond (
        Move (arm7_varid rd) (BinOp OP_AND (Var (arm7_varid rn)) (op2eval i op2)) $;
        arm_cpsr_update s rd (
          Move R_CF (Unknown 1) $;
          Move R_ZF (BinOp OP_EQ (Var (arm7_varid rd)) (Word 0 32)) $;
          Move R_NF (Cast CAST_HIGH 1 (Var (arm7_varid rd)))
        )
      )
    )
  | ARM7_Eor cond i s rn rd op2 => Some(4,
      cond_eval cond (
        Move (arm7_varid rd) (BinOp OP_XOR (Var (arm7_varid rn)) (op2eval i op2)) $;
        arm_cpsr_update s rd (
          Move R_CF (Unknown 1) $;
          Move R_ZF (BinOp OP_EQ (Var (arm7_varid rd)) (Word 0 32)) $;
          Move R_NF (Cast CAST_HIGH 1 (Var (arm7_varid rd)))
        )
      )
    )
  | ARM7_Sub cond i s rn rd op2 => Some(4,
      cond_eval cond (
        Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rn)) (op2eval i op2)) $;
        arm_cpsr_update s rd (
          Move R_CF (BinOp OP_LE (Var (arm7_varid rd)) (op2var i op2)) $;
          Move R_ZF (BinOp OP_EQ (Var (arm7_varid rd)) (Word 0 32)) $;
          Move R_NF (Cast CAST_HIGH 1 (Var (arm7_varid rd)))
        )
      )
    )
  | _ => Some(4, Nop)
  end.