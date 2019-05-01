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
Require Export Picinae_theory.
Require Export BinNat.
Require Import NArith.
Require Import ZArith.
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
  | V_TEMP64 (n:N)
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
  | V_TEMP _ => Some (NumT 32)
  | V_TEMP64 _ => Some (NumT 64)
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

Definition arm7_varid (n:N) :=
  match n with
  | 0 => R_R0
  | 1 => R_R1
  | 2 => R_R2
  | 3 => R_R3
  | 4 => R_R4
  | 5 => R_R5
  | 6 => R_R6
  | 7 => R_R7
  | 8 => R_R8
  | 9 => R_R9
  | 10 => R_R10
  | 11 => R_R11
  | 12 => R_R12
  | 13 => R_SP
  | 14 => R_LR
  | _ => R_PC
  end.

Inductive arm7asm :=
(* Data proc with immediate values *)
| ARM7_AndI (cond s rn rd rot imm:N)
| ARM7_EorI (cond s rn rd rot imm:N)
| ARM7_SubI (cond s rn rd rot imm:N)
| ARM7_RsbI (cond s rn rd rot imm:N)
| ARM7_AddI (cond s rn rd rot imm:N)
| ARM7_AdcI (cond s rn rd rot imm:N)
| ARM7_SbcI (cond s rn rd rot imm:N)
| ARM7_RscI (cond s rn rd rot imm:N)
| ARM7_TstI (cond s rn rd rot imm:N)
| ARM7_TeqI (cond s rn rd rot imm:N)
| ARM7_CmpI (cond s rn rd rot imm:N)
| ARM7_CmnI (cond s rn rd rot imm:N)
| ARM7_OrrI (cond s rn rd rot imm:N)
| ARM7_MovI (cond s rn rd rot imm:N)
| ARM7_BicI (cond s rn rd rot imm:N)
| ARM7_MvnI (cond s rn rd rot imm:N)
| ARM7_InvalidOpI (cond s rn rd rot imm:N)
(* Data proc with shift amount *)
| ARM7_AndS (cond s rn rd sa st rm:N)
| ARM7_EorS (cond s rn rd sa st rm:N)
| ARM7_SubS (cond s rn rd sa st rm:N)
| ARM7_RsbS (cond s rn rd sa st rm:N)
| ARM7_AddS (cond s rn rd sa st rm:N)
| ARM7_AdcS (cond s rn rd sa st rm:N)
| ARM7_SbcS (cond s rn rd sa st rm:N)
| ARM7_RscS (cond s rn rd sa st rm:N)
| ARM7_TstS (cond s rn rd sa st rm:N)
| ARM7_TeqS (cond s rn rd sa st rm:N)
| ARM7_CmpS (cond s rn rd sa st rm:N)
| ARM7_CmnS (cond s rn rd sa st rm:N)
| ARM7_OrrS (cond s rn rd sa st rm:N)
| ARM7_MovS (cond s rn rd sa st rm:N)
| ARM7_BicS (cond s rn rd sa st rm:N)
| ARM7_MvnS (cond s rn rd sa st rm:N)
| ARM7_InvalidOpS (cond s rn rd sa st rm:N)
(* Data proc with shift register *)
| ARM7_AndR (cond s rn rd rs st rm:N)
| ARM7_EorR (cond s rn rd rs st rm:N)
| ARM7_SubR (cond s rn rd rs st rm:N)
| ARM7_RsbR (cond s rn rd rs st rm:N)
| ARM7_AddR (cond s rn rd rs st rm:N)
| ARM7_AdcR (cond s rn rd rs st rm:N)
| ARM7_SbcR (cond s rn rd rs st rm:N)
| ARM7_RscR (cond s rn rd rs st rm:N)
| ARM7_TstR (cond s rn rd rs st rm:N)
| ARM7_TeqR (cond s rn rd rs st rm:N)
| ARM7_CmpR (cond s rn rd rs st rm:N)
| ARM7_CmnR (cond s rn rd rs st rm:N)
| ARM7_OrrR (cond s rn rd rs st rm:N)
| ARM7_MovR (cond s rn rd rs st rm:N)
| ARM7_BicR (cond s rn rd rs st rm:N)
| ARM7_MvnR (cond s rn rd rs st rm:N)
| ARM7_InvalidOpR (cond s rn rd rs st rm:N)
(* MSR and MRS instructions -- subset of data operations *)
| ARM7_MsrCpsrI (cond s rn rd rot imm:N)
| ARM7_MsrSpsrI (cond s rn rd rot imm:N)
| ARM7_MsrCpsr (cond s rn rd sa st rm:N)
| ARM7_MsrSpsr (cond s rn rd sa st rm:N)
| ARM7_MrsCpsr (cond s rn rd sa st rm:N)
| ARM7_MrsSpsr (cond s rn rd sa st rm:N)
(* Multiplication *)
| ARM7_Mul (cond a s rd rn rs rm:N)
| ARM7_Mull (cond u a s rd_hi rd_lo rs rm:N)
(* Branch *)
| ARM7_Branch (cond l:N) (offset:Z)
(* Load and store *)
| ARM7_LdrI (cond p u b w rn rd imm:N)
| ARM7_StrI (cond p u b w rn rd imm:N)
| ARM7_LdrS (cond p u b w rn rd sa st rm:N)
| ARM7_StrS (cond p u b w rn rd sa st rm:N)
| ARM7_LdrHI (cond p u w rn rd s h off:N)
| ARM7_StrHI (cond p u w rn rd s h off:N)
| ARM7_LdrHS (cond p u w rn rd s h rm:N)
| ARM7_StrHS (cond p u w rn rd s h rm:N)
(* Swap instruction *)
| ARM7_Swp (cond b rn rd rm:N)
(* Block data transfer *)
| ARM7_Ldm (cond p u s w rn r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0:N)
| ARM7_Stm (cond p u s w rn r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0:N)
| ARM7_Invalid
| ARM7_Unsupported
.

Definition bits4 b3 b2 b1 b0 := b3*8 + b2*4 + b1*2 + b0.
Definition bits5 b4 b3 b2 b1 b0 := b4*16 + (bits4 b3 b2 b1 b0).
Definition bits8 b7 b6 b5 b4 b3 b2 b1 b0 := (bits4 b7 b6 b5 b4)*16 + (bits4 b3 b2 b1 b0).
Definition bits12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 :=
  (bits4 b11 b10 b9 b8)*256 + (bits4 b7 b6 b5 b4)*16 + (bits4 b3 b2 b1 b0).
Definition bits24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 :=
  (bits4 b23 b22 b21 b20)*1048576 + (bits4 b19 b18 b17 b16)*65536 + (bits4 b15 b14 b13 b12)*4096 + 
  (bits4 b11 b10 b9 b8)*256 + (bits4 b7 b6 b5 b4)*16 + (bits4 b3 b2 b1 b0).
Definition b (i:N) (n:N) := N.land (N.shiftr n i) 1.
Definition xbits n i j := N.land (N.shiftr n i) (N.ones (j - i)).

Require Export Bool.

Definition arm_dec_bin_opt (n:N) :=
  (* Data proc with shift register *)
  if ((xbits n 25 28) =? 0) && ((b 7 n) =? 0) && ((b 4 n) =? 1) then
    match (xbits n 21 25) with
    | 0 => ARM7_AndR
    | 1 => ARM7_EorR
    | 2 => ARM7_SubR
    | 3 => ARM7_RsbR
    | 4 => ARM7_AddR
    | 5 => ARM7_AdcR
    | 6 => ARM7_SbcR
    | 7 => ARM7_RscR
    | 8 => ARM7_TstR
    | 9 => ARM7_TeqR
    | 10 => ARM7_CmpR
    | 11 => ARM7_CmnR
    | 12 => ARM7_OrrR
    | 13 => ARM7_MovR
    | 14 => ARM7_BicR
    | _ => ARM7_MvnR
    end (xbits n 28 32) (b 20 n) (xbits n 16 20) (xbits n 12 16) (xbits n 8 12) (xbits n 5 7) (xbits n 0 4)

  (* Data proc with shift amount *)
  else if ((xbits n 25 28) =? 0) && ((b 4 n) =? 0) then
    match (xbits n 21 25) with
    | 0 => ARM7_AndS
    | 1 => ARM7_EorS
    | 2 => ARM7_SubS
    | 3 => ARM7_RsbS
    | 4 => ARM7_AddS
    | 5 => ARM7_AdcS
    | 6 => ARM7_SbcS
    | 7 => ARM7_RscS
    | 8 => if (xbits n 12 21) =? 159 then ARM7_MrsSpsr else ARM7_TstS
    | 9 => if (xbits n 12 21) =? 159 then ARM7_MsrCpsr else ARM7_TeqS
    | 10 => if (xbits n 12 21) =? 159 then ARM7_MrsCpsr else ARM7_CmpS
    | 11 => if (xbits n 12 21) =? 159 then ARM7_MsrSpsr else ARM7_CmnS
    | 12 => ARM7_OrrS
    | 13 => ARM7_MovS
    | 14 => ARM7_BicS
    | _ => ARM7_MvnS
    end (xbits n 28 32) (b 20 n) (xbits n 16 20) (xbits n 12 16) (xbits n 7 11) (xbits n 5 7) (xbits n 0 4)

  (* Data proc with immediate amount *)
  else if ((xbits n 25 28) =? 1) then
    match (xbits n 21 25) with
    | 0 => ARM7_AndI
    | 1 => ARM7_EorI
    | 2 => ARM7_SubI
    | 3 => ARM7_RsbI
    | 4 => ARM7_AddI
    | 5 => ARM7_AdcI
    | 6 => ARM7_SbcI
    | 7 => ARM7_RscI
    | 8 => ARM7_TstI
    | 9 =>  if (xbits n 12 21) =? 143 then ARM7_MsrCpsrI else ARM7_TeqI
    | 10 => ARM7_CmpI
    | 11 => if (xbits n 12 21) =? 143 then ARM7_MsrSpsrI else ARM7_CmnI
    | 12 => ARM7_OrrI
    | 13 => ARM7_MovI
    | 14 => ARM7_BicI
    | _ => ARM7_MvnI
    end (xbits n 28 32) (b 20 n) (xbits n 16 20) (xbits n 12 16) (xbits n 8 12) (xbits n 0 8)

  (* Multiply *)
  else if ((xbits n 22 28) =? 0) && ((xbits n 4 8) =? 9) then 
    ARM7_Mul (xbits n 28 32) (b 21 n) (b 20 n) (xbits n 16 20) (xbits n 12 16) (xbits n 8 12) (xbits n 0 4)

  (* Multiply Long *)
  else if ((xbits n 23 28) =? 1) && ((xbits n 4 8) =? 9) then
    ARM7_Mull (xbits n 28 32) (b 22 n) (b 21 n) (b 20 n) (xbits n 16 20) (xbits n 12 16) (xbits n 8 12) (xbits n 0 4)

  else if (((xbits n 25 28) =? 0) && ((xbits n 21 22) =? 0) && ((xbits n 7 12) =? 1) && ((xbits n 4 5) =? 1)) then
    (* Single data swap *)
    match (b 6 n), (b 5 n), (b 20 n) with
    | 0, 0, 0 => ARM7_Swp (xbits n 28 32) (xbits n 22 23) (xbits n 16 20) (xbits n 12 16) (xbits n 0 4)
    (* Halfword data transfer: register offset *)
    | _, _, 0 => ARM7_StrHS (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 21 22)
                            (xbits n 16 20) (xbits n 12 16) (xbits n 6 7) (xbits n 5 6) (xbits n 0 4)
    | _, _, _ => ARM7_LdrHS (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 21 22)
                            (xbits n 16 20) (xbits n 12 16) (xbits n 6 7) (xbits n 5 6) (xbits n 0 4)
    end

  (* Half word data transfer immediate offset *)
  else if (((xbits n 25 28) =? 0) && ((xbits n 21 22) =? 1) && ((xbits n 7 8) =? 1) && ((xbits n 4 5) =? 1)) then
    match (xbits n 20 21) with
    | 0 => ARM7_StrHI
    | _ => ARM7_LdrHI
    end (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 21 22)
        (xbits n 16 20) (xbits n 12 16) (xbits n 6 7) (xbits n 5 6) (((xbits n 8 12) * 16) + (xbits n 0 4))

  (* Single data transfer register offset *)
  else if ((xbits n 25 28) =? 2) && ((xbits n 4 5) =? 0) then
    match (xbits n 20 21) with
    | 0 => ARM7_StrS
    | _ => ARM7_LdrS
    end (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 22 23) (xbits n 21 22)
        (xbits n 16 20) (xbits n 12 16) (xbits n 7 12) (xbits n 5 7) (xbits n 0 4)

  (* Single data transfer immediate offset *)
  else if ((xbits n 25 28) =? 3) then
    match (xbits n 20 21) with
    | 0 => ARM7_StrI
    | _ => ARM7_LdrI
    end (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 22 23) (xbits n 21 22)
        (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)

  (* Branch *)
  else if (xbits n 25 28) =? 5 then
    ARM7_Branch (xbits n 28 32) (xbits n 24 25) (toZ 24 (xbits n 0 24))

  (* Block data transfer *)
  else if (xbits n 25 28) =? 4 then
    match (xbits n 20 21) with
    | 0 => ARM7_Stm
    | _ => ARM7_Ldm
    end (xbits n 28 32) (xbits n 24 25) (xbits n 23 24) (xbits n 22 23) (xbits n 21 22) (xbits n 16 20)
        (xbits n 15 16) (xbits n 14 15) (xbits n 13 14) (xbits n 12 13) (xbits n 11 12) (xbits n 10 11)
        (xbits n 9 10)  (xbits n 8 9)   (xbits n 7 8)   (xbits n 6 7)   (xbits n 5 6)   (xbits n 4 5)
        (xbits n 3 4)   (xbits n 2 1)   (xbits n 1 2)   (xbits n 0 1)
  else
    ARM7_Unsupported.

Definition arm_dec_bin (n:N) :=

  match b 27 n,  b 26 n,  b 25 n,  b 24 n,  b 23 n,  b 22 n,  b 21 n,  b 20 n,  b 19 n,  b 18 n,  b 17 n,  b 16 n,  b 15 n,  b 14 n,
        b 13 n,  b 12 n,  b 11 n,  b 10 n,  b 9 n,    b 8 n,   b 7 n,   b 6 n,   b 5 n,   b 4 n,   b 3 n,   b 2 n,   b 1 n,   b 0 n
  with

  (* Data proc with shift register *)
  |    0,    0,    0,  oc3,  oc2,  oc1,  oc0,    s,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,  rs3,  rs2,  rs1,  rs0,    0,  st1,  st0,    1,  rm3,  rm2,  rm1,  rm0 =>
    match bits4 oc3 oc2 oc1 oc0 with
    | 0 => ARM7_AndR
    | 1 => ARM7_EorR
    | 2 => ARM7_SubR
    | 3 => ARM7_RsbR
    | 4 => ARM7_AddR
    | 5 => ARM7_AdcR
    | 6 => ARM7_SbcR
    | 7 => ARM7_RscR
    | 8 => ARM7_TstR
    | 9 => ARM7_TeqR
    | 10 => ARM7_CmpR
    | 11 => ARM7_CmnR
    | 12 => ARM7_OrrR
    | 13 => ARM7_MovR
    | 14 => ARM7_BicR
    | 15 => ARM7_MvnR
    | _ => ARM7_InvalidOpS end (xbits n 27 31) s (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0) 
                               (bits4 rs3 rs2 rs1 rs0) (bits4 0 0 st1 st0) (bits4 rm3 rm2 rm1 rm0)

  (* Data proc with shift amount *)
  |    0,    0,    0,  oc3,  oc2,  oc1,  oc0,    s,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,  sa4,  sa3,  sa2,  sa1,  sa0,  st1,  st0,    0,  rm3,  rm2,  rm1,  rm0 =>
    match bits4 oc3 oc2 oc1 oc0 with
    | 0 => ARM7_AndS
    | 1 => ARM7_EorS
    | 2 => ARM7_SubS
    | 3 => ARM7_RsbS
    | 4 => ARM7_AddS
    | 5 => ARM7_AdcS
    | 6 => ARM7_SbcS
    | 7 => ARM7_RscS
    | 8 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   1,   1,   1,   1,   1 => ARM7_MrsSpsr
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_TstS
           end
    | 9 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   1,   1,   1,   1,   1 => ARM7_MsrCpsr
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_TeqS
           end
    | 10 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   1,   1,   1,   1,   1 => ARM7_MrsCpsr
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_CmpS
           end
    | 11 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   1,   1,   1,   1,   1 => ARM7_MsrSpsr
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_CmnS
           end
    | 12 => ARM7_OrrS
    | 13 => ARM7_MovS
    | 14 => ARM7_BicS
    | 15 => ARM7_MvnS
    | _ => ARM7_InvalidOpS end (xbits n 27 31) s (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0) 
                               (bits5 sa4 sa3 sa2 sa1 sa0) (bits4 0 0 st1 st0) (bits4 rm3 rm2 rm1 rm0)

  (* Data proc with immediate values *)
  |    0,    0,    1,  oc3,  oc2,  oc1,  oc0,    s,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0, rot3, rot2, rot1, rot0, imm7, imm6, imm5, imm4, imm3, imm2, imm1, imm0 => 
    match bits4 oc3 oc2 oc1 oc0 with
    | 0 => ARM7_AndI
    | 1 => ARM7_EorI
    | 2 => ARM7_SubI
    | 3 => ARM7_RsbI
    | 4 => ARM7_AddI
    | 5 => ARM7_AdcI
    | 6 => ARM7_SbcI
    | 7 => ARM7_RscI
    | 8 => ARM7_TstI
    | 9 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   0,   1,   1,   1,   1 => ARM7_MsrCpsrI
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_TeqI
           end
    | 10 => ARM7_CmpI
    | 11 => match s, rn3, rn2, rn1, rn0, rd3, rd2, rd1, rd0 with
           |     0,   1,   0,   0,   0,   1,   1,   1,   1 => ARM7_MsrSpsrI
           |     _,   _,   _,   _,   _,   _,   _,   _,   _ => ARM7_CmnI
           end
    | 12 => ARM7_OrrI
    | 13 => ARM7_MovI
    | 14 => ARM7_BicI
    | 15 => ARM7_MvnI
    | _ => ARM7_InvalidOpI end (xbits n 27 31) s (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0) 
                               (bits4 rot3 rot2 rot1 rot0) (bits8 imm7 imm6 imm5 imm4 imm3 imm2 imm1 imm0)

  (* Multiply *)
  |    0,    0,    0,    0,    0,    0,    a,    s,  rd3,  rd2,  rd1,  rd0,  rn3,  rn2,
     rn1,  rn0,  rs3,  rs2,  rs1,  rs0,    1,    0,    0,    1,  rm3,  rm2,  rm1,  rm0 =>
     ARM7_Mul (xbits n 27 31) a s (bits4 rd3 rd2 rd1 rd0) (bits4 rn3 rn2 rn1 rn0)
              (bits4 rs3 rs2 rs1 rs0) (bits4 rm3 rm2 rm1 rm0)

  (* Multiply Long *)
  |    0,    0,    0,    0,    1,    u,    a,    s,  rd7,  rd6,  rd5,  rd4,  rd3,  rd2,
     rd1,  rd0,  rs3,  rs2,  rs1,  rs0,    1,    0,    0,    1,  rm3,  rm2,  rm1,  rm0 =>
     ARM7_Mull (xbits n 27 31) u a s (bits4 rd7 rd6 rd5 rd4) (bits4 rd3 rd2 rd1 rd0)
     (bits4 rs3 rs2 rs1 rs0) (bits4 rm3 rm2 rm1 rm0)

  (* Branch and exchange *)
  |    0,    0,    0,    1,    0,    b,    0,    0,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,    0,    0,    0,    0,    1,    0,    0,    1,  rm3,  rm2,  rm1,  rm0 => ARM7_Unsupported

  (* Half word data transfer register offset *)
  |    0,    0,    0,    p,    u,    b,    w,    l,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,    0,    0,    0,    0,    1,    s,    h,    1,  rm3,  rm2,  rm1,  rm0 =>
    match s, h, l with
    | 0, 0, 0 => ARM7_Swp (xbits n 27 31) b (bits4 rn3 rn2 rn1 rn0)
                          (bits4 rd3 rd2 rd1 rd0) (bits4 rm3 rm2 rm1 rm0)
    | _, _, 0 => ARM7_StrHS (xbits n 27 31) p u w (bits4 rn3 rn2 rn1 rn0)
                            (bits4 rd3 rd2 rd1 rd0) s h (bits4 rm3 rm2 rm1 rm0)
    | _, _, _ => ARM7_LdrHS (xbits n 27 31) p u w (bits4 rn3 rn2 rn1 rn0)
                            (bits4 rd3 rd2 rd1 rd0) s h (bits4 rm3 rm2 rm1 rm0)
    end

  (* Half word data transfer immediate offset *)
  |    0,    0,    0,    p,    u,    1,    w,    l,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,   o7,   o6,   o5,   o4,    1,    s,    h,    1,   o3,   o2,   o1,   o0 =>
    match l with
    | 0 => ARM7_StrHI
    | _ => ARM7_LdrHI
    end (xbits n 27 31) p u w (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0)
         s h (bits8 o7 o6 o5 o4 o3 o2 o1 o0)


  (* Single data transfer register offset *)
  |    0,    1,    0,    p,    u,    b,    w,    l,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,  sa4,  sa3,  sa2,  sa1,  sa0,  st1,  st0,    0,  rm0,  rm1,  rm2,  rm3 =>
    match l with
    | 0 => ARM7_StrS
    | _ => ARM7_LdrS
    end (xbits n 27 31) p u b w (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0)
        (bits5 sa4 sa3 sa2 sa1 sa0) (bits4 0 0 st1 st0) (bits4 rm3 rm2 rm1 rm0)

  (* Single data transfer immediate offset *)
  |    0,    1,    1,    p,    u,    b,    w,    l,  rn3,  rn2,  rn1,  rn0,  rd3,  rd2,
     rd1,  rd0,imm11,imm10, imm9, imm8, imm7, imm6, imm5, imm4, imm3, imm2, imm1, imm0 =>
    match l with
    | 0 => ARM7_StrI
    | _ => ARM7_LdrI
    end (xbits n 27 31) p u b w (bits4 rn3 rn2 rn1 rn0) (bits4 rd3 rd2 rd1 rd0)
        (bits12 imm1 imm10 imm9 imm8 imm7 imm6 imm5 imm4 imm3 imm2 imm1 imm0)

  (* Block data transfer *)
  |    1,    0,    0,    p,    u,    s,    w,    l,  rn3,  rn2,  rn1,  rn0, rl15, rl14,
    rl13, rl12, rl11, rl10,  rl9,  rl8,  rl7,  rl6,  rl5,  rl4,  rl3,  rl2,  rl1,  rl0 => ARM7_Unsupported

  (* Branch *)
  |    1,    0,    1,    l,  o23,  o22,  o21,  o20,  o19,  o18,  o17,  o16,  o15,  o14,
     o13,  o12,  o11,  o10,   o9,   o8,   o7,   o6,   o5,   o4,   o3,   o2,   o1,   o0 =>
    ARM7_Branch (xbits n 27 31) l (toZ 24 (bits24 o23 o22 o21 o20 o19 o18 o17 o16 o15 o14 o13 o12 o11 o10
                                                  o9 o8 o7 o6 o5 o4 o3 o2 o1 o0))

  (* Coprocessor Data Transfer *)
  |    1,    1,    0,    p,    u,    n,    w,    l,  rn3,  rn2,  rn1,  rn0, crd3, crd2, 
    crd1, crd0, cpn3, cpn2, cpn1, cpn0,   o7,   o6,   o5,   o4,   o3,   o2,   o1,   o0 => ARM7_Unsupported

  (* Coprocessor Data Ooperation *)
  |    1,    1,    1,    0,  oc3,  oc2,  oc1,  oc0, crn3, crn2, crn1, crn0, crd3, crd2, 
    crd1, crd0, cpn3, cpn2, cpn1, cpn0,  cp2,  cp1,  cp0,    0, crm3, crm2, crm1, crm0 => ARM7_Unsupported

  (* Coprocessor Register Transfer *)
  |    1,    1,    1,    0,  oc3,  oc2,  oc1,    l, crn3, crn2, crn1, crn0,  rd3,  rd2,
     rd1,  rd0, cpn3, cpn2, cpn1, cpn0,  cp2,  cp1,  cp0,    1, crm3, crm2, crm1, crm0 => ARM7_Unsupported

  (* Software Interrupt *)
  |    1,    1,    1,    1,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,
       _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _  => ARM7_Unsupported

  (* Invalid instruction *)
  |    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,
       _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _,    _ => ARM7_Invalid
  end.

Open Scope stmt_scope.

Definition bit_set := (Word 1 1).
Definition bit_clr := (Word 0 1).
Definition arm7_st st := match st with | 0 => OP_LSHIFT | 1 => OP_RSHIFT | 2 => OP_ARSHIFT | _ => OP_ROT end.
Definition ldr_str_word_bit b := match b with | 0 => 32 | _ => 8 end.
Definition ldr_str_up_bit u := match u with | 0 => OP_MINUS | _ => OP_PLUS end.
Definition ldr_str_half_word_bit h := match h with | 0 => 8 | _ => 16 end.
Definition ldr_str_signed_bit s := match s with | 0 => CAST_UNSIGNED | _ => CAST_SIGNED end.
Definition swp_word_bit b := match b with | 0 => 32 | _ => 8 end.

Definition mov_imm_op2 imm rot := BinOp OP_ROT (Word imm 32) (Word (2 * rot) 32).
Definition mov_imm op dst rn imm rot := Move dst (BinOp op (Var (arm7_varid rn)) (mov_imm_op2 imm rot)).

Definition mov_reg_op2 st rm rs := (BinOp (arm7_st st) (Var (arm7_varid rm)) (Var (arm7_varid rs))).
Definition mov_reg op dst rn st rm rs := Move dst (BinOp op (Var (arm7_varid rn)) (mov_reg_op2 st rm rs)).

Definition mov_shift_op2 st rm sa := (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32)).
Definition mov_shift op dst rn st sa rm := Move dst (BinOp op (Var (arm7_varid rn)) (mov_shift_op2 st rm sa)).

Definition pre_post p exp1 exp2 := if p =? 0 then exp1 $; exp2 else exp2 $; exp1.

Definition cpsr_update_arith s dst carry :=
  If (BinOp OP_EQ bit_set (Word s 1)) (
    if dst == R_PC then
      Nop
    else
      Move R_VF (BinOp OP_XOR (carry) (Var R_CF)) $;
      Move R_CF (carry) $;
      Move R_ZF (Cast CAST_HIGH 1 (BinOp OP_EQ (Var dst) (Word 0 32))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var dst))
    )
    (Nop).

Definition cpsr_update_logical s dst src st sa :=
  if s =? 1 then
    if dst == R_PC then
      Nop
    else
      If (BinOp OP_NEQ sa (Word 0 32))
        (if st =? 0 then
            (Move R_CF (Cast CAST_HIGH 1 (BinOp OP_LSHIFT src (BinOp OP_MINUS sa (Word 1 32)))))
        else
            (Move R_CF (Cast CAST_LOW 1 (BinOp OP_RSHIFT src (BinOp OP_MINUS sa (Word 1 32))))))
        Nop
      $;
      Move R_ZF (Cast CAST_HIGH 1 (BinOp OP_EQ (Var dst) (Word 0 32))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var dst))
    else
    (Nop).

Definition cpsr_update s dst := cpsr_update_arith s dst (Unknown 1).

Definition cond_eval cond il :=
  match cond with
  | 0 => If (BinOp OP_EQ (Var R_ZF) bit_set) (il) (Nop)
  | 1 => If (BinOp OP_EQ (Var R_ZF) bit_clr) (il) (Nop)
  | 2 => If (BinOp OP_EQ (Var R_CF) bit_set) (il) (Nop)
  | 3 => If (BinOp OP_EQ (Var R_CF) bit_clr) (il) (Nop)
  | 4 => If (BinOp OP_EQ (Var R_NF) bit_set) (il) (Nop)
  | 5 => If (BinOp OP_EQ (Var R_NF) bit_clr) (il) (Nop)
  | 6 => If (BinOp OP_EQ (Var R_VF) bit_set) (il) (Nop)
  | 7 => If (BinOp OP_EQ (Var R_VF) bit_clr) (il) (Nop)
  | 8 => If (BinOp OP_AND (BinOp OP_EQ (Var R_CF) bit_set) (BinOp OP_EQ (Var R_ZF) bit_clr)) (il) (Nop)
  | 9 => If (BinOp OP_OR (BinOp OP_EQ (Var R_CF) bit_clr) (BinOp OP_EQ (Var R_ZF) bit_set)) (il) (Nop)
  | 10 => If (BinOp OP_EQ (Var R_NF) (Var R_VF)) (il) (Nop)
  | 11 => If (BinOp OP_NEQ (Var R_NF) (Var R_VF)) (il) (Nop)
  | 12 => If (BinOp OP_AND (BinOp OP_EQ (Var R_ZF) bit_clr) (BinOp OP_EQ (Var R_NF) (Var R_VF))) (il) (Nop)
  | _ => If (BinOp OP_OR (BinOp OP_EQ (Var R_ZF) bit_set) (BinOp OP_NEQ (Var R_NF) (Var R_VF))) (il) (Nop)
end.

Definition arm2il (ad:addr) armi :=
  match armi with
  (* Arithmatic data processing operations *)
  | ARM7_SubI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_MINUS (arm7_varid rd) rn imm rot) $; 
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LE (Var (arm7_varid rd)) (Var (arm7_varid rn))))
  | ARM7_SubR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_MINUS (arm7_varid rd) rn st rm rs) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LE (Var (arm7_varid rd)) (Var (arm7_varid rn))))
  | ARM7_SubS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_MINUS (arm7_varid rd) rn st sa rm $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LE (Var (arm7_varid rd)) (Var (arm7_varid rn))))
  | ARM7_RsbI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_MINUS (arm7_varid rd) rn imm rot) $;
                                      Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_imm_op2 imm rot) (Var (arm7_varid rd))))
  | ARM7_RsbR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_MINUS (arm7_varid rd) rn st rm rs) $;
                                       Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_reg_op2 st rm rs) (Var (arm7_varid rd))))
  | ARM7_RsbS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_MINUS (arm7_varid rd) rn st sa rm $;
                                       Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_shift_op2 st rm sa) (Var (arm7_varid rd))))
  | ARM7_AddI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_PLUS (arm7_varid rd) rn imm rot) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_imm_op2 imm rot)))
  | ARM7_AddR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_PLUS (arm7_varid rd) rn st rm rs) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_reg_op2 st rm rs)))
  | ARM7_AddS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_PLUS (arm7_varid rd) rn st sa rm $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_shift_op2 st rm sa)))
  | ARM7_AdcI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_PLUS (arm7_varid rd) rn imm rot) $;
                                      Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_imm_op2 imm rot)))
  | ARM7_AdcR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_PLUS (arm7_varid rd) rn st rm rs) $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_reg_op2 st rm rs)))
  | ARM7_AdcS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_PLUS (arm7_varid rd) rn st sa rm $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (Var (arm7_varid rd)) (mov_shift_op2 st rm sa)))
  | ARM7_SbcI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_MINUS (arm7_varid rd) rn imm rot) $;
                                      Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                      Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_imm_op2 imm rot) (Var (arm7_varid rd))))
  | ARM7_SbcR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_MINUS (arm7_varid rd) rn st rm rs) $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_reg_op2 st rm rs) (Var (arm7_varid rd))))
  | ARM7_SbcS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_MINUS (arm7_varid rd) rn st sa rm $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_shift_op2 st rm sa) (Var (arm7_varid rd))))
  | ARM7_RscI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_MINUS (arm7_varid rd) rn imm rot) $;
                                      Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                      Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                      Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_imm_op2 imm rot) (Var (arm7_varid rd))))
  | ARM7_RscR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_MINUS (arm7_varid rd) rn st rm rs) $;
                                       Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                      cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_reg_op2 st rm rs) (Var (arm7_varid rd))))
  | ARM7_RscS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_MINUS (arm7_varid rd) rn st sa rm $;
                                       Move (arm7_varid rd) (UnOp OP_NEG (Var (arm7_varid rd))) $;
                                       Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Cast CAST_UNSIGNED 32 (Var R_CF))) $;
                                       Move (arm7_varid rd) (BinOp OP_MINUS (Var (arm7_varid rd)) (Word 1 32)) $;
                                       cpsr_update_arith s (arm7_varid rd) (BinOp OP_LT (mov_shift_op2 st rm sa) (Var (arm7_varid rd))))
  | ARM7_TstI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_AND (V_TEMP ad) rn imm rot) $; cpsr_update s (V_TEMP ad))
  | ARM7_TstR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_AND (V_TEMP ad) rn st rm rs) $; cpsr_update s (V_TEMP ad))
  | ARM7_TstS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_AND (V_TEMP ad) rn st sa rm $; cpsr_update s (V_TEMP ad))
  | ARM7_TeqI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_XOR (V_TEMP ad) rn imm rot) $; cpsr_update s (V_TEMP ad))
  | ARM7_TeqR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_XOR (V_TEMP ad) rn st rm rs) $; cpsr_update s (V_TEMP ad))
  | ARM7_TeqS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_XOR (V_TEMP ad) rn st sa rm $; cpsr_update s (V_TEMP ad))
  | ARM7_CmpI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_MINUS (V_TEMP ad) rn imm rot) $; cpsr_update s (V_TEMP ad))
  | ARM7_CmpR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_MINUS (V_TEMP ad) rn st rm rs) $; cpsr_update s (V_TEMP ad))
  | ARM7_CmpS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_MINUS (V_TEMP ad) rn st sa rm $; cpsr_update s (V_TEMP ad))
  | ARM7_CmnI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_PLUS (V_TEMP ad) rn imm rot) $; cpsr_update s (V_TEMP ad))
  | ARM7_CmnR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_PLUS (V_TEMP ad) rn st rm rs) $; cpsr_update s (V_TEMP ad))
  | ARM7_CmnS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_PLUS (V_TEMP ad) rn st sa rm $; cpsr_update s (V_TEMP ad))
  (* Logical data processing operations *)
  | ARM7_AndI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_AND (arm7_varid rd) rn imm rot) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_AndR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_AND (arm7_varid rd) rn st rm rs) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_AndS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_AND (arm7_varid rd) rn st sa rm $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))
  | ARM7_EorI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_XOR (arm7_varid rd) rn imm rot) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_EorR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_XOR (arm7_varid rd) rn st rm rs) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_EorS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_XOR (arm7_varid rd) rn st sa rm $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))
  | ARM7_OrrI cond s rn rd rot imm => cond_eval cond ((mov_imm OP_OR (arm7_varid rd) rn imm rot) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_OrrR cond s rn rd rs st rm => cond_eval cond ((mov_reg OP_OR (arm7_varid rd) rn st rm rs) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_OrrS cond s rn rd sa st rm => cond_eval cond (mov_shift OP_OR (arm7_varid rd) rn st sa rm $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))
  | ARM7_MovI cond s rn rd rot imm => cond_eval cond (Move (arm7_varid rd) (mov_imm_op2 imm rot) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_MovR cond s rn rd rs st rm => cond_eval cond (Move (arm7_varid rd) (mov_reg_op2 st rm rs) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_MovS cond s rn rd sa st rm => cond_eval cond (Move (arm7_varid rd) (mov_shift_op2 st rm sa) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))
  | ARM7_BicI cond s rn rd rot imm => cond_eval cond (Move (arm7_varid rd) (BinOp OP_AND (Var (arm7_varid rn)) (UnOp OP_NOT (mov_imm_op2 imm rot))) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_BicR cond s rn rd rs st rm => cond_eval cond (Move (arm7_varid rd) (BinOp OP_AND (Var (arm7_varid rn)) (UnOp OP_NOT (mov_reg_op2 st rm rs))) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_BicS cond s rn rd sa st rm => cond_eval cond (Move (arm7_varid rd) (BinOp OP_AND (Var (arm7_varid rn)) (UnOp OP_NOT (mov_shift_op2 st rm sa))) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))
  | ARM7_MvnI cond s rn rd rot imm => cond_eval cond (Move (arm7_varid rd) (UnOp OP_NOT (mov_imm_op2 imm rot)) $; cpsr_update_logical s (arm7_varid rd) (Word imm 32) 1 (Word (2 * rot) 32))
  | ARM7_MvnR cond s rn rd rs st rm => cond_eval cond (Move (arm7_varid rd) (UnOp OP_NOT (mov_reg_op2 st rm rs)) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Var (arm7_varid rs)))
  | ARM7_MvnS cond s rn rd sa st rm => cond_eval cond (Move (arm7_varid rd) (UnOp OP_NOT (mov_shift_op2 st rm sa)) $; cpsr_update_logical s (arm7_varid rd) (Var (arm7_varid rm)) st (Word sa 32))

  | ARM7_Mul cond a s rd rn rs rm =>
      cond_eval cond (
        Move (arm7_varid rd) (BinOp OP_TIMES (Var (arm7_varid rm)) (Var (arm7_varid rs))) $;
        If (BinOp OP_EQ (Word a 32) (Word 1 32)) (
          Move (arm7_varid rd) (BinOp OP_PLUS (Var (arm7_varid rd)) (Var (arm7_varid rn)))
        ) (
          Nop
        ) $;
        cpsr_update s (arm7_varid rd)
      )
  | ARM7_Mull cond u a s rd_hi rd_lo rs rm =>
      cond_eval cond (
        Move (V_TEMP64 ad) (BinOp OP_TIMES (Cast CAST_SIGNED 64 (Var (arm7_varid rm)))
                                           (Cast CAST_SIGNED 64 (Var (arm7_varid rs)))) $;
        If (BinOp OP_EQ (Word a 32) (Word 1 32)) (
          Move (V_TEMP64 ad) (BinOp OP_PLUS (Var (V_TEMP64 ad))
                                          (BinOp OP_OR (Cast CAST_UNSIGNED 64 (BinOp OP_LSHIFT (Var (arm7_varid rd_hi)) (Word 32 32)))
                                                       (Cast CAST_UNSIGNED 64 (Var (arm7_varid rd_lo)))))
        ) (
          Nop
        ) $;
        If (BinOp OP_EQ (Word u 32) (Word 1 32)) (
          Move (arm7_varid rd_hi) (Cast CAST_HIGH 32 (Cast CAST_UNSIGNED 64 (Var (V_TEMP64 ad)))) $;
          Move (arm7_varid rd_lo) (Cast CAST_LOW 32 (Cast CAST_UNSIGNED 64 (Var (V_TEMP64 ad))))
        ) (
          Nop
        ) $;
        If (BinOp OP_NEQ (Word u 32) (Word 1 32)) (
          Move (arm7_varid rd_hi) (Cast CAST_HIGH 32 (Cast CAST_SIGNED 64 (Var (V_TEMP64 ad)))) $;
          Move (arm7_varid rd_lo) (Cast CAST_LOW 32 (Cast CAST_SIGNED 64 (Var (V_TEMP64 ad))))
        ) (
          Nop
        )
      ) $;
      Move R_VF (Unknown 1) $;
      Move R_CF (Unknown 1) $;
      Move R_NF (BinOp OP_AND (Cast CAST_LOW 1 (Word u 32))
                              (Cast CAST_HIGH 1 (Var (arm7_varid rd_hi)))) $;
      Move R_ZF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_EQ (Var (arm7_varid rd_hi)) (Word 0 32))
                                  (BinOp OP_EQ (Var (arm7_varid rd_lo)) (Word 0 32))))
  | ARM7_Branch cond l offset =>
      cond_eval cond (
        If (BinOp OP_EQ (Word l 32) (Word 1 32)) (
          Move R_PC (Word ((Z.to_N (Z.of_N ad + offset + 4)) mod 2^32) 32)
        ) (
          Nop
        ) $;
        Jmp (Word ((Z.to_N (Z.of_N ad + offset)) mod 2^32) 32)
      )
  | ARM7_LdrI cond p u b w rn rd imm =>
      cond_eval cond (
      match p with
      | 1 => Move (arm7_varid rd) (Load (Var V_MEM32)
                                        (Cast CAST_SIGNED 32
                                          (Cast CAST_LOW (ldr_str_word_bit b)
                                            (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word imm 32))))
                                        LittleE
                                        4)
      | _ => Move (arm7_varid rd) (Load (Var V_MEM32)
                                        (Cast CAST_SIGNED 32
                                            (Cast CAST_LOW (ldr_str_word_bit b)
                                            (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word 0 32))))
                                        LittleE
                                        4)
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn) (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word imm 32))
      end) 
  | ARM7_StrI cond p u b w rn rd imm =>
      cond_eval cond (
      match p with
      | 1 => Move V_MEM32 (Store (Var V_MEM32)
                          (Cast CAST_SIGNED 32
                            (Cast CAST_LOW (ldr_str_word_bit b)
                              (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word imm 32))))
                          (Var (arm7_varid rd))
                          LittleE
                          4)
      | _ => Move V_MEM32 (Store (Var V_MEM32)
                          (Cast CAST_SIGNED 32
                            (Cast CAST_LOW (ldr_str_word_bit b)
                              (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word 0 32))))
                          (Var (arm7_varid rd))
                          LittleE
                          4)
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn) (BinOp (ldr_str_up_bit u) (Var (arm7_varid rn)) (Word imm 32))
      end)
  | ARM7_LdrS cond p u b w rn rd sa st rm =>
      cond_eval cond (
      match p with
      | 1 =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast CAST_SIGNED 32
                      (Cast CAST_LOW (ldr_str_word_bit b)
                          (BinOp (ldr_str_up_bit u)
                              (Var (arm7_varid rn))
                              (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32)))))
                   LittleE
                   4
             )
      | _ =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast CAST_SIGNED 32
                      (Cast CAST_LOW (ldr_str_word_bit b)
                          (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32))))
                   LittleE
                   4
             )
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32)))
      end)
  | ARM7_StrS cond p u b w rn rd sa st rm =>
      cond_eval cond (
      match p with
      | 1 => Move V_MEM32 (Store (Var V_MEM32)
                                 (Cast CAST_SIGNED 32
                                    (Cast CAST_LOW (ldr_str_word_bit b)
                                        (BinOp (ldr_str_up_bit u)
                                            (Var (arm7_varid rn))
                                            (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32)))))
                                 (Var (arm7_varid rd))
                                 LittleE
                                 4)
      | _ => Move V_MEM32 (Store (Var V_MEM32)
                                 (Cast CAST_SIGNED 32
                                    (Cast CAST_LOW (ldr_str_word_bit b)
                                      (Var (arm7_varid rn))))
                                 (Var (arm7_varid rd))
                                 LittleE
                                 4)
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (BinOp (arm7_st st) (Var (arm7_varid rm)) (Word sa 32)))
      end)
  | ARM7_LdrHS cond p u w rn rd s h rm =>
      cond_eval cond (
      match p with
      | 1 =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast (ldr_str_signed_bit s) 32
                   (Cast CAST_LOW (ldr_str_half_word_bit h)
                         (BinOp (ldr_str_up_bit u)
                                (Var (arm7_varid rn))
                                (Var (arm7_varid rm)))
                   ))
                   LittleE
                   4
             )
      | _ =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast (ldr_str_signed_bit s) 32
                   (Cast CAST_LOW (ldr_str_half_word_bit h)
                         (Var (arm7_varid rm))
                   ))
                   LittleE
                   4
             )
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (Var (arm7_varid rm)))
      end)
  | ARM7_StrHS cond p u w rn rd s h rm =>
      cond_eval cond (
      match p with
      | 1 => Move V_MEM32 (Store (Var V_MEM32)
                                 (Cast (ldr_str_signed_bit s) 32
                                 (Cast CAST_LOW (ldr_str_half_word_bit h)
                                       (BinOp (ldr_str_up_bit u)
                                              (Var (arm7_varid rn))
                                              (Var (arm7_varid rm)))
                                       ))
                                 (Var (arm7_varid rd))
                                 LittleE
                                 4)
      | _ => Move (arm7_varid rd)
                  (Load (Var V_MEM32)
                        (Cast (ldr_str_signed_bit s) 32
                        (Cast CAST_LOW (ldr_str_half_word_bit h)
                              (Var (arm7_varid rm))
                        ))
                        LittleE
                        4)
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (Var (arm7_varid rm)))
      end)
  | ARM7_LdrHI cond p u w rn rd s h off =>
      cond_eval cond (
      match p with
      | 1 =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast (ldr_str_signed_bit s) 32
                   (Cast CAST_LOW (ldr_str_half_word_bit h)
                         (BinOp (ldr_str_up_bit u)
                                (Var (arm7_varid rn))
                                (Word off 32))
                   ))
                   LittleE
                   4
             )
      | _ =>
        Move (arm7_varid rd)
             (Load (Var V_MEM32)
                   (Cast (ldr_str_signed_bit s) 32
                   (Cast CAST_LOW (ldr_str_half_word_bit h) (Word off 32)
                   ))
                   LittleE
                   4
             )
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (Word off 32))
      end)
  | ARM7_StrHI cond p u w rn rd s h off =>
      cond_eval cond (
      match p with
      | 1 => Move V_MEM32 (Store (Var V_MEM32)
                                 (Cast (ldr_str_signed_bit s) 32
                                 (Cast CAST_LOW (ldr_str_half_word_bit h)
                                       (BinOp (ldr_str_up_bit u)
                                              (Var (arm7_varid rn))
                                              (Word off 32))
                                       ))
                                 (Var (arm7_varid rd))
                                 LittleE
                                 4)
      | _ => Move (arm7_varid rd)
                  (Load (Var V_MEM32)
                        (Cast (ldr_str_signed_bit s) 32
                        (Cast CAST_LOW (ldr_str_half_word_bit h) (Word off 32)
                        ))
                        LittleE
                        4)
      end $;
      match w with
      | 0 => Nop
      | _ => Move (arm7_varid rn)
                  (BinOp (ldr_str_up_bit u)
                         (Var (arm7_varid rn))
                         (Word off 32))
      end)
  | ARM7_Swp cond b rn rd rm =>
      cond_eval cond (
        Move (arm7_varid rd) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW (swp_word_bit b) (Var (arm7_varid rn)))) LittleE 4) $;
        Move V_MEM32 (Store (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW (swp_word_bit b) (Var (arm7_varid rn)))) (Var (arm7_varid rm)) LittleE 4)
      )
  | ARM7_Stm cond p u s w rn r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 =>
      cond_eval cond (
        if u =? 1 then
          Move (V_TEMP ad) (Var (arm7_varid rn)) $;
          if r0 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R0) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r1 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R1) LittleE 4))
                      (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r2 =? 1 then
           pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R2) LittleE 4))
                     (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r3 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R3) LittleE 4))
                      (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r4 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R4) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r5 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R5) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r6 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R6) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r7 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R7) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r8 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R8) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r9 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R9) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r10 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R10) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r11 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R11) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r12 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R12) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
            else Nop
          $;
          if r13 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_SP) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r14 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_LR) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r15 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_PC) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
        else
          Move (V_TEMP ad) (Var (arm7_varid rn)) $;
          if r15 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_PC) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r14 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_LR) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r13 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_SP) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r12 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R12) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
            else Nop
          $;
          if r11 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R11) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r10 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R10) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r9 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R9) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r8 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R8) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r7 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R7) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r6 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R6) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r5 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R5) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r4 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R4) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r3 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R3) LittleE 4))
                      (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r2 =? 1 then
           pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R2) LittleE 4))
                     (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r1 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R1) LittleE 4))
                      (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r0 =? 1 then
            pre_post p (Move V_MEM32 (Store (Var V_MEM32) (Var (arm7_varid rn)) (Var R_R0) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
        $;
        if w =? 1 then
          Move (arm7_varid rn) (Var (V_TEMP ad))
        else Nop
      )
  | ARM7_Ldm cond p u s w rn r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 =>
      cond_eval cond (
        if u =? 1 then
          Move (V_TEMP ad) (Var (arm7_varid rn)) $;
          if r0 =? 1 then
            pre_post p (Move R_R0 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r1 =? 1 then
            pre_post p (Move R_R1 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r2 =? 1 then
            pre_post p (Move R_R2 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r3 =? 1 then
            pre_post p (Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r4 =? 1 then
            pre_post p (Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r5 =? 1 then
            pre_post p (Move R_R5 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r6 =? 1 then
            pre_post p (Move R_R6 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r7 =? 1 then
            pre_post p (Move R_R7 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r8 =? 1 then
            pre_post p (Move R_R8 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r9 =? 1 then
            pre_post p (Move R_R9 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r10 =? 1 then
            pre_post p (Move R_R10 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r11 =? 1 then
            pre_post p (Move R_R11 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r12 =? 1 then
            pre_post p (Move R_R12 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r13 =? 1 then
            pre_post p (Move R_SP (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r14 =? 1 then
            pre_post p (Move R_LR (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r15 =? 1 then
            pre_post p (Move R_PC (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_PLUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
        else
          Move (V_TEMP ad) (Var (arm7_varid rn)) $;
          if r15 =? 1 then
            pre_post p (Move R_PC (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r14 =? 1 then
            pre_post p (Move R_LR (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r13 =? 1 then
            pre_post p (Move R_SP (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r12 =? 1 then
            pre_post p (Move R_R12 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r11 =? 1 then
            pre_post p (Move R_R11 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r10 =? 1 then
            pre_post p (Move R_R10 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r9 =? 1 then
            pre_post p (Move R_R9 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r8 =? 1 then
            pre_post p (Move R_R8 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r7 =? 1 then
            pre_post p (Move R_R7 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r6 =? 1 then
            pre_post p (Move R_R6 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r5 =? 1 then
            pre_post p (Move R_R5 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r4 =? 1 then
            pre_post p (Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r3 =? 1 then
            pre_post p (Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r2 =? 1 then
            pre_post p (Move R_R2 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r1 =? 1 then
            pre_post p (Move R_R1 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
          if r0 =? 1 then
            pre_post p (Move R_R0 (Load (Var V_MEM32) (Var (V_TEMP ad)) LittleE 4))
                       (Move (V_TEMP ad) (BinOp OP_MINUS (Var (V_TEMP ad)) (Word 4 32)))
          else Nop
          $;
        if w =? 1 then
          Move (arm7_varid rn) (Var (V_TEMP ad))
        else Nop
      )
  | ARM7_InvalidOp => Exn 0
  end.

Theorem hastyp_varid:
  forall n, armtypctx (arm7_varid n) = Some (NumT 32).
Proof.
  destruct n. reflexivity.
  repeat first [ reflexivity | destruct p ].
Qed.

Theorem hastyp_bits8:
  forall n, bits8 (b 7 n) (b 6 n) (b 5 n) (b 4 n) (b 3 n) (b 2 n) (b 1 n) (b 0 n) < 2 ^ 32.
Proof.
  destruct n. reflexivity.
  repeat first [ reflexivity | destruct p ].
Qed.

Theorem hastyp_2bits4:
  forall n, 2 * bits4 (b 3 n) (b 2 n) (b 1 n) (b 0 n) < 2 ^ 32.
Proof.
  destruct n. reflexivity.
  repeat first [ reflexivity | destruct p ].
Qed.

Lemma xbits_bound:
  forall n i j w, j-i <= w -> xbits n i j < 2^w.
Proof.
  intros. unfold xbits. eapply N.lt_le_trans.
    rewrite N.land_ones. apply N.mod_upper_bound, N.pow_nonzero. discriminate 1.
    apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Lemma xbits_bound_double:
  forall n, 2 * xbits n 8 12 < 2 ^ 32.
Proof.
  intro n.
  destruct n.
  reflexivity.
  repeat first [ reflexivity | destruct p ].
Qed.

Lemma xbits_16:
  forall n, xbits n 8 12 * 16 + xbits n 0 4 < 2 ^ 32.
Proof.
  intro n.
  destruct n.
  reflexivity.
  repeat first [ reflexivity | destruct p ].
Qed.

Lemma bit_lt_o:
  forall n m o, o > 1 -> b m n < o.
Proof.
  intros.
  unfold b.
  remember (N.shiftr n m) as n'.
  destruct o.
  destruct n'.
  discriminate.
  discriminate.
  destruct n'.
  rewrite N.land_0_l. reflexivity.
  destruct p0.
  simpl. apply N.gt_lt. assumption.
  simpl. reflexivity.
  simpl. apply N.gt_lt. assumption.
Qed.

Ltac unfold_arm2il :=
repeat try unfold arm2il;
       try unfold cond_eval;
       try unfold mov_imm;
       try unfold mov_reg;
       try unfold mov_shift;
       try unfold mov_imm_op2;
       try unfold mov_reg_op2;
       try unfold mov_shift_op2;
       try unfold bit_set;
       try unfold bit_clr;
       try unfold swp_word_bit;
       try unfold ldr_str_signed_bit;
       try unfold ldr_str_half_word_bit;
       try unfold ldr_str_up_bit;
       try unfold ldr_str_word_bit;
       try unfold cpsr_update;
       try unfold cpsr_update_arith;
       try unfold cpsr_update_logical;
       try unfold arm7_st;
       try unfold pre_post.

Ltac destruct_match :=
repeat match goal with |- context [ match ?x with _ => _ end ] =>
    try destruct x
end.

Ltac solve_arm2il_subgoals :=
repeat first
  [ reflexivity
  | apply xbits_16
  | apply bit_lt_o
  | apply ofZ_bound
  | apply N.mod_lt
  | apply xbits_bound
  | apply xbits_bound_double
  | apply ofZ_bound
  | apply N.mod_lt
  | right
  | discriminate 1
  | eapply TWord
  | eapply TMove
  | apply TSeq
  | apply TIf
  | eapply hastyp_binop
  | rewrite <- store_upd_eq
  | apply hastyp_varid
  | econstructor ].

Ltac clear_exceptions := eexists; try apply TExn.

Ltac solve_arm := unfold_arm2il; destruct_match; clear_exceptions; solve_arm2il_subgoals.

Theorem arm7_il_welltyped:
  forall a n, exists c', hastyp_stmt armtypctx armtypctx (arm2il a (arm_dec_bin_opt n)) c'.
Proof.
  intros. unfold arm_dec_bin_opt.
  repeat match goal with [ |- context [ if ?x then _ else _ ] ] => destruct x end.
  all: destruct_match.
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. } 1: { solve_arm. } 1: { solve_arm. }
  1: { solve_arm. } 1: { solve_arm. }  1: { solve_arm. }
  Optimize Proof.
Qed.