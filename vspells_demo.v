(* Proof of return address safety and memory safety for Patched DARPA Challenge binary *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_amd64.
Require Import vspells_patched.

Import X64Notations.
Open Scope N.

Definition code s a :=
  match a with
  | 311 | 401 => match my_prog s a with Some (n,_) => Some (n,Nop) | _ => None end
  | _ => my_prog s a
  end.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

(* The x64 lifter models non-writable code. *)
Theorem nwc: forall s2 s1, code s1 = code s2.
Proof. reflexivity. Qed.

(* Type safety:
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strcmp_welltyped: welltyped_prog x64typctx code.
Proof.
  Picinae_typecheck.
Qed.

(* Memory safety:
   The code never corrupts the return address on the stack. *)

Definition frame_size := 84.

Definition rdi_slot := 18446744073709551560.

Definition code_invs (s:store) m rsp (a:addr) (s':store) :=
  match a with
  | 0 => Some (s' = s)
  | 55 | 81 | 104 | 137 | 208 | 223 | 233 | 258 | 329 | 357 | 401 | 461 | 587 | 594 | 599 =>
    Some (∃ m', s' V_MEM64 = Ⓜ m' /\
      m' Ⓠ[rsp] = m Ⓠ[rsp] /\
      s' R_RBP = Ⓠ (2^64 + rsp ⊖ 8) /\
      m' Ⓠ[ 2^64 + rsp ⊖ 8 ⊕ rdi_slot ] < rsp - frame_size
    )
  | _ => None
  end.

(* The post-condition says that the return address is unmodified on exit. *)
Definition code_post m rsp (_:exit) (s':store) :=
  ∃ m', s' V_MEM64 = Ⓜ m' /\ m' Ⓠ[rsp] = m Ⓠ[rsp].

Definition code_invset s m rsp :=
  invs (code_invs s m rsp) (code_post m rsp).


(*** Automation tactics (will eventually be incorporated into standard libs) ***)

Lemma init_thm v:
  forall {c s} (MDL: models c s),
  match c v with Some (NumT w) => ∃ n, s v = VaN n w
               | Some (MemT w) => ∃ m, s v = VaM m w
               | None => True
  end.
Proof.
  intros. specialize (MDL v). destruct (c v).
    destruct t; specialize (MDL _ eq_refl); inversion MDL; eexists; reflexivity.
    reflexivity.
Qed.

Ltac initialize H s v n :=
  match goal with [ MDL: models _ s |- _ ] =>
    assert (H := init_thm v MDL); destruct H as [n H]
  end.

Ltac report_failure :=
  lazymatch goal with [ H: exec_prog _ _ 0 _ _ _ (Exit ?a) |- ?g ] => fail "(possible missing bounds-check): Cannot prove memory access bound" g "in basic block at offset" a end.

Lemma invQ: forall x y, Ⓠ x = Ⓠ y -> x = y.
Proof. intros. inversion H. reflexivity. Qed.

Lemma pow2_near:
  forall w x y z (H1: y <= z) (H2: z <= 2^w),
  exists b:bool, (x+z)/2^w = (x+y)/2^w + if b then 1 else 0.
Proof.
  intros.
  rewrite (N.div_mod' x (2^w)), <- !N.add_assoc, !(N.mul_comm (2^w)).
  rewrite !N.div_add_l by (apply N.pow_nonzero; discriminate 1).
  destruct (N.lt_ge_cases (x mod 2^w + z) (2^w)) as [H3|H3].

    exists false. rewrite (N.div_small _ _ H3), (N.div_small (_+_)), !N.add_0_r. reflexivity.
    eapply N.le_lt_trans; [|eassumption]. apply N.add_le_mono_l, H1.

    rewrite <- (N.sub_add _ _ H3). setoid_rewrite <- (N.mul_1_l (2^w)) at 4.
    rewrite N.div_add, N.add_assoc by (apply N.pow_nonzero; discriminate 1).
    rewrite (N.div_small (_-_)), N.add_0_r.

      destruct (N.lt_ge_cases (x mod 2^w + y) (2^w)) as [H4|H4].
        exists true. rewrite (N.div_small _ _ H4), N.add_0_r. reflexivity.
        exists false. rewrite <- (N.sub_add _ _ H4). setoid_rewrite <- (N.mul_1_l (2^w)) at 5.
          rewrite N.div_add, N.add_assoc by (apply N.pow_nonzero; discriminate 1).
          rewrite (N.div_small (_-_)), !N.add_0_r. reflexivity.
          eapply N.add_lt_mono_r. rewrite (N.sub_add _ _ H4).
          apply N.add_lt_le_mono. apply N.mod_lt, N.pow_nonzero. discriminate 1.
          etransitivity; eassumption.

      eapply N.add_lt_mono_r. rewrite (N.sub_add _ _ H3).
      apply N.add_lt_le_mono. apply N.mod_lt, N.pow_nonzero. discriminate 1. assumption.
Qed.

Theorem disjoint_stackslots1:
  forall e1 e2 m w a off1 off2 len1 len2 v,
    (((off1 + len1 <=? off2) && (off2 + len2 <=? 2^w)) ||
     ((off2 + len2 <=? off1) && (off1 + len1 <=? 2^w)) = true)%bool ->
  getmem e1 len1 (setmem e2 len2 m ((a + off2) mod 2^w) v) ((a + off1) mod 2^w) =
  getmem e1 len1 m ((a + off1) mod 2^w).
Proof.
  intros. apply Bool.orb_prop in H.
  eassert (H0: _ \/ _). destruct H as [H|H]; [left|right];
    apply andb_prop in H; destruct H as [H1 H2];
    apply N.leb_le in H1; apply N.leb_le in H2;
    (apply conj; [ exact H1 | exact H2 ]).
  clear H.
  destruct H0 as [[H1 H2]|[H1 H2]];
  (edestruct (pow2_near w a) as [b H3]; only 1-2: etransitivity; [apply N.le_add_r| |apply N.le_add_r|eassumption|]; [eassumption|]);
  destruct b; (apply getmem_frame_high + apply getmem_frame_low); solve
  [ rewrite N.add_0_r in H3; eapply N.add_le_mono_l;
    rewrite N.add_assoc, <- N.div_mod', <- H3, <- N.div_mod', <- N.add_assoc;
    apply N.add_le_mono_l; assumption
  | eapply N.add_le_mono_l;
    rewrite N.add_assoc, <- N.div_mod', H3, N.add_1_r, N.mul_succ_r, (N.add_comm _ (2^w)), <- (N.add_assoc (2^w)),
            <- N.div_mod', (N.add_comm (2^w)), <- !(N.add_assoc a);
    apply N.add_le_mono_l; etransitivity; [ eassumption | rewrite N.add_comm; apply N.le_add_r ] ].
Qed.

Corollary disjoint_stackslots2:
  forall e1 e2 m w a off2 len1 len2 v,
    ((len1 <=? off2) && (off2 + len2 <=? 2^w) = true)%bool ->
  getmem e1 len1 (setmem e2 len2 m ((a + off2) mod 2^w) v) a =
  getmem e1 len1 m a.
Proof.
  intros. destruct (N.lt_ge_cases a (2^w)).

  rewrite <- (N.mod_small a (2^w)) at -1 by assumption. rewrite <- (N.add_0_r a) at -1.
  apply disjoint_stackslots1, Bool.orb_true_iff. left. rewrite N.add_0_l. assumption.

  apply getmem_frame_high.
  rewrite <- N.add_mod_idemp_l by (apply N.pow_nonzero; discriminate 1).
  etransitivity. apply N.add_le_mono_r, N.mod_le, N.pow_nonzero. discriminate 1.
  rewrite <- N.add_assoc. etransitivity. apply N.add_le_mono_l. eapply N.leb_le, proj2, Bool.andb_true_iff, H.
  rewrite (N.div_mod' a (2^w)) at 2. rewrite N.add_comm. apply N.add_le_mono_r.
  rewrite <- (N.mul_1_r (2^w)) at 1. apply N.mul_le_mono_l.
  apply N.div_le_lower_bound. apply N.pow_nonzero. discriminate 1. rewrite N.mul_1_r. assumption.
Qed.

Corollary disjoint_stackslots3:
  forall e1 e2 m w a off1 len1 len2 v,
    ((len2 <=? off1) && (off1 + len1 <=? 2^w) = true)%bool ->
  getmem e1 len1 (setmem e2 len2 m a v) ((a + off1) mod 2^w) =
  getmem e1 len1 m ((a + off1) mod 2^w).
Proof.
  intros. destruct (N.lt_ge_cases a (2^w)).

  rewrite <- (N.mod_small a (2^w)) at 1 by assumption. rewrite <- (N.add_0_r a) at 1.
  apply disjoint_stackslots1, Bool.orb_true_iff. right. rewrite N.add_0_l. assumption.

  apply getmem_frame_low.
  rewrite <- N.add_mod_idemp_l by (apply N.pow_nonzero; discriminate 1).
  etransitivity. apply N.add_le_mono_r, N.mod_le, N.pow_nonzero. discriminate 1.
  rewrite <- N.add_assoc. etransitivity. apply N.add_le_mono_l. eapply N.leb_le, proj2, Bool.andb_true_iff, H.
  rewrite (N.div_mod' a (2^w)) at 2. rewrite N.add_comm. apply N.add_le_mono_r.
  rewrite <- (N.mul_1_r (2^w)) at 1. apply N.mul_le_mono_l.
  apply N.div_le_lower_bound. apply N.pow_nonzero. discriminate 1. rewrite N.mul_1_r. assumption.
Qed.

Ltac simplify_stackrefs :=
  repeat rewrite ?disjoint_stackslots1, ?disjoint_stackslots2, ?disjoint_stackslots3, ?getmem_setmem by reflexivity.

Theorem msub_madd:
  forall w y z
    (H1: z <= 2^w)
    (H2: y < 2^w),
  ((2^w + y - z) mod 2^w + z) mod 2^w = y.
Proof.
  intros.
  rewrite N.add_mod_idemp_l by (apply N.pow_nonzero; discriminate 1).
  rewrite N.sub_add by (etransitivity; [ eassumption | apply N.le_add_r ]).
  rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate 1).
  apply N.mod_small. assumption.
Qed.


(* Our return address integrity theorem makes the following assumptions:
   (MDL0) Assume that on entry the processor is in a valid state.
   (MEM0 RSP0 RDI0) Let m, esp, and rdi be the values of the memory/registers on entry.
   (RSP_BND) Precondition: There must be enough stack space available on entry.
   (RDILO) Precondition: The pointer argument must not point into the stack(!).
   (RET) Assume the return address on the stack on entry is not within the callee.
   (XP0) Let x and s' be the exit condition and store after n instructions execute.
   From these, we try to prove that all invariants (including the post-condition) hold
   true for arbitrarily long executions (i.e., arbitrary n). *)
Theorem return_address_integrity:
  forall s rsp rdi m n s' x
         (MDL0: models x64typctx s)
         (MEM0: s V_MEM64 = Ⓜ m) (RSP0: s R_RSP = Ⓠ rsp) (RSP_BND: frame_size <= rsp)
         (RDI0: s R_RDI = Ⓠ rdi) (RDILO: rdi < rsp - frame_size)
         (RET: code s (m Ⓠ[rsp]) = None)
         (XP0: exec_prog fh code 0 s n s' x),
  trueif_inv (code_invset s m rsp code x s').
Proof.
  intros.
  eapply prove_invs. exact XP0. reflexivity.

  intros.
  rewrite (nwc s1) in RET.
  assert (MDL: models x64typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strcmp_welltyped. exact XP.

  initialize RBP0 s1 R_RBP rbp0.
  initialize RSI0 s1 R_RSI rsi.
  initialize RDX0 s1 R_RDX rdx.
  initialize RCX0 s1 R_RCX rcx.
  set (rbp := 2^64 + rsp ⊖ 8).
  assert (Hrsp: rsp = rbp ⊕ 8). symmetry. apply msub_madd. discriminate 1. apply (x64_regsize MDL0 RSP0).

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 64 PRE.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x64_step.

  (* Addresses 0-52 *)
  subst s1. step. fold rbp.
  do 14 step.
  eexists. fold rbp. rewrite Hrsp. split. reflexivity. simplify_stackrefs.
  repeat split. rewrite <- Hrsp. assumption.

  (* Address 55 *)
  step; cycle 1; clear BC. exact PRE.
  destruct PRE as [m1 [MEM1 PRE]].
  do 4 step; cycle 1; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.

  (* Addresses 71-76 *)
  step. step.
  eexists. simpl_stores. split. reflexivity. apply PRE.

  (* Addresses 81-91 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 3 step. step; cycle 1; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. apply PRE.

  (* Address 97 *)
  step.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.

  (* Addresses 104-109 *)
  destruct PRE as [m1 [MEM1 PRE]].
  step. step; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.

  (* Addresses 111-135 *)
  do 7 step. step; clear BC.

  (* Address 99 *)
  assert (P2 := proj1 (proj2 PRE)). rewrite RBP0 in P2. apply invQ in P2. subst rbp0. fold rbp.
  step.
    eexists. split. reflexivity. fold rbp. rewrite Hrsp. simplify_stackrefs. rewrite <- Hrsp. repeat split; apply PRE.
    eexists. split. reflexivity. rewrite <- RBP0. exact PRE.

  (* Addresses 137-162 *)
  destruct PRE as [m1 [MEM1 PRE]].
  assert (P2 := proj1 (proj2 PRE)). rewrite RBP0 in P2. apply invQ in P2. subst rbp0. fold rbp.
  do 4 step.
    eexists. simpl_stores. split. reflexivity. apply PRE.
    eexists. split. reflexivity. rewrite <- N.add_mod_idemp_l by discriminate 1. fold rbp. rewrite Hrsp. simplify_stackrefs. rewrite <- Hrsp. repeat split; apply PRE.

  (* Addresses 208-213 *)
  destruct PRE as [m1 [MEM1 PRE]].
  step. step. eexists. simpl_stores. split. eassumption. apply PRE.

  (* Addresses 223-231 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 3 step; cycle 1; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.

  (* Addresses 164-218 *)
  do 6 step. step; cycle 1; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.
  do 6 step. step; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.
  step.
  assert (P2 := proj1 (proj2 PRE)). rewrite RBP0 in P2. apply invQ in P2. subst rbp0. fold rbp.
  eexists. split. reflexivity. rewrite Hrsp. simplify_stackrefs. rewrite <- Hrsp. repeat split; apply PRE.

  (* Addresses 233-267 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 7 step.
  rewrite RBP0 in PRE. destruct PRE as [P1 [P2 P3]]. apply invQ in P2. subst rbp0. fold rbp.
  eexists. split. reflexivity. rewrite Hrsp. simplify_stackrefs. fold rdi_slot. rewrite getmem_frame_high. rewrite <- Hrsp.
    repeat split.
      apply P1.
      rewrite getmem_frame_high.
        eapply N.le_lt_trans; [|exact P3]. report_failure.
        rewrite N.add_1_r. apply N.le_succ_l. eapply N.lt_le_trans. exact P3. shelve.
    rewrite N.add_1_r. apply N.le_succ_l. eapply N.lt_le_trans. exact P3. rewrite Hrsp. apply N.le_sub_l.

  (* Addresses 258-267 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 3 step. step; cycle 1; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. apply PRE.

  (* Addresses 269-324 *)
  do 3 step; clear BC.
  do 2 step. eexists. split. reflexivity. apply PRE.
  do 10 step.
  rewrite RBP0 in PRE. destruct PRE as [P1 [P2 P3]]. apply invQ in P2. subst rbp0. fold rbp.
  eexists. split. reflexivity. rewrite Hrsp. simplify_stackrefs. rewrite <- Hrsp. apply P1.

  (* Addresses 329-351 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 3 step. step; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.
  do 3 step. step; clear BC.
  eexists. split. reflexivity. rewrite <- RBP0. exact PRE.
  eexists. split. reflexivity. apply PRE.

  (* Addresses 357-375 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 3 step. step; clear BC.
  do 2 step. eexists. split. reflexivity. apply PRE.
  do 4 step.
  rewrite RBP0 in PRE. destruct PRE as [P1 [P2 P3]]. apply invQ in P2. subst rbp0. fold rbp.
  eexists. split. reflexivity. rewrite Hrsp. simplify_stackrefs. rewrite <- Hrsp. repeat split; assumption.

  (* Addresses 401-449 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 14 step. step; clear BC.
  eexists. split. reflexivity. apply PRE. (* TODO: Address 451 not lifted (BAP bug). *)
  eexists. split. reflexivity. rewrite <- RBP0. apply PRE.

  (* Addresses 461-587 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 40 step.
  rewrite RBP0 in PRE. destruct PRE as [P1 [P2 P3]]. apply invQ in P2. subst rbp0. fold rbp.
  eexists. split. reflexivity. rewrite Hrsp. simplify_stackrefs.
  rewrite !getmem_frame_high by shelve. rewrite <- Hrsp. repeat split; assumption.

  (* Addresses 587-589 *)
  destruct PRE as [m1 [MEM1 [P1 [P2 P3]]]]. rewrite RBP0 in P2. apply invQ in P2. subst rbp0. fold rbp.
  step; clear BC. step.
  eexists. split. reflexivity. rewrite <- N.add_mod_idemp_l by discriminate 1. fold rbp. rewrite Hrsp. simplify_stackrefs.
  rewrite <- Hrsp. repeat split; assumption.
  eexists. split. eassumption. repeat split; assumption.

  (* Address 594 *)
  destruct PRE as [m1 [MEM1 [P1 [P2 P3]]]]. rewrite RBP0 in P2. apply invQ in P2. subst rbp0. fold rbp.
  step.
  eexists. split. reflexivity. rewrite <- N.add_mod_idemp_l by discriminate 1. fold rbp. rewrite Hrsp. simplify_stackrefs.
  rewrite <- Hrsp. repeat split; assumption.

  (* Address 599 *)
  destruct PRE as [m1 [MEM1 PRE]].
  do 2 step. step; clear BC.
    eexists. split. reflexivity. rewrite <- RBP0. exact PRE.
    eexists. split. reflexivity. apply PRE.
