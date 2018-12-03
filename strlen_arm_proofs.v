Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv7.
Require Import strlen_arm.

Import ARMNotations.
Open Scope N.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

Theorem strlen_nwc: forall s2 s1, strlen_arm s1 = strlen_arm s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog armtypctx strlen_arm.
Proof.
  Picinae_typecheck.
Qed.

Theorem strlen_preserves_memory:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

Theorem strlen_preserves_readable:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|exact H].
  prove_noassign.
Qed.

Theorem strlen_preserves_lr:
  forall s n s' x,
  exec_prog fh strlen_arm 0 s n s' x -> s' R_LR = s R_LR.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Tactic Notation "destN" constr(n) "until" tactic(T) "eqn" ":" ident(H) :=
  let p := fresh n in
  destruct n as [|p] eqn:H;
  [ try solve [T]
  | repeat first [ solve[T] | destruct p as [p|p|] ] ].

(* Tactic: focus_addr H n
   Shelve all goals except the goal in which hypothesis H has the form (H: _ = n).
   This retrieves the subgoal for address n from a sea of arbitrarily ordered goals.
   Use vernacular command "Unshelve" to pull back all the shelved goals afterward. *)
Tactic Notation "focus_addr" hyp(H) constr(n) :=
  match type of H with _ = n => idtac | _ => shelve end.

Lemma N_lt_m:
  forall n m, n < m -> n = m-1 \/ n < m-1.
Proof.
  intros. apply N.lt_le_pred in H.
  rewrite N.pred_sub in H. apply N.le_lteq in H.
  destruct H; [right | left]; assumption.
Qed.

Corollary N_lt_4 : forall n, n < 4 -> n = 0 \/ n = 1 \/ n = 2 \/ n = 3.
Proof.
  intros.
  do 4 try (apply N_lt_m in H; destruct H).
  all: repeat (try (try left; assumption); try right).
  apply N.nlt_0_r in H; inversion H.
Qed.

Lemma if_true : forall (A:Type) (a1 a2:A) b,
  a1 ≠ a2 ->
  b = true <-> (if b then a1 else a2) = a1.
Proof.
  intros. split.
    intros.
    destruct b; [ reflexivity | discriminate ].
  intros. destruct b. reflexivity. subst a2. contradiction.
Qed.

Lemma if_false : forall (A:Type) (a1 a2:A) b,
  a1 ≠ a2 ->
  b = false <-> (if b then a1 else a2) = a2.
Proof.
  intros. split.
    intros.
    destruct b; [ discriminate | reflexivity ].
  intros. destruct b; [ contradiction | reflexivity].
Qed.

Lemma if_neq_then : forall (A:Type) (a1 a2:A) (b:bool),
  a1 ≠ a2 ->
  (if b then a1 else a2) ≠ a1 <-> (if b then a1 else a2) = a2.
Proof.
  split; intros.
  destruct b. contradiction. reflexivity.
  destruct b. contradiction. intros H1. subst a2. contradiction.
Qed.

Lemma if_neq_else : forall (A:Type) (a1 a2:A) (b:bool),
  a1 ≠ a2 ->
  (if b then a1 else a2) ≠ a2 <-> (if b then a1 else a2) = a1.
Proof.
  split; intros.
  destruct b. reflexivity. contradiction.
  destruct b. assumption. rewrite H0 in H. contradiction.
Qed.

Lemma pos_le_0_1 : forall a b,
  N.pos a <= N.pos b ->
  N.pos a~0 <= N.pos b~1.
Proof.
  intros.
  replace (N.pos a~0) with (N.shiftl (N.pos a) 1) by reflexivity.
  replace (N.pos b~1) with ((N.shiftl (N.pos b) 1) + 1) by reflexivity.
  repeat rewrite N.shiftl_mul_pow2; replace (2^1) with 2 by reflexivity.
  apply N.le_trans with (N.pos b * 2).
  apply N.mul_le_mono_r; assumption.
  apply N.le_add_r.
Qed.

Lemma pos_le_1_1 : forall a b,
  N.pos a <= N.pos b ->
  N.pos a~1 <= N.pos b~1.
Proof.
  intros.
  replace (N.pos a~1) with ((N.shiftl (N.pos a) 1) + 1) by reflexivity.
  replace (N.pos b~1) with ((N.shiftl (N.pos b) 1) + 1) by reflexivity.
  apply N.add_le_mono_r. repeat rewrite N.shiftl_mul_pow2. 
  replace (2^1) with 2 by reflexivity. apply N.mul_le_mono_r. assumption.
Qed.

Lemma pos_le_0_0 : forall a b,
  N.pos a <= N.pos b ->
  N.pos a~0 <= N.pos b~0.
Proof.
  intros.
  replace (N.pos a~0) with (N.shiftl (N.pos a) 1) by reflexivity.
  replace (N.pos b~0) with (N.shiftl (N.pos b) 1) by reflexivity.
  repeat rewrite N.shiftl_mul_pow2; replace (2^1) with 2 by reflexivity.
  apply N.mul_le_mono_r. assumption.
Qed.

Theorem and_le_l : forall a b, a .& b <= a.
Proof.
  intros.
  destruct a, b.
  1-3: discriminate 1.
  revert dependent p0. induction p; intros.
  3: simpl; destruct p0; discriminate 1.
  simpl. destruct p0.
    destruct (Pos.land p p0) eqn:Hand. discriminate 1.
      simpl. apply pos_le_1_1. rewrite <- Hand. apply IHp.
    destruct (Pos.land p p0) eqn:Hand. discriminate 1.
      simpl. apply pos_le_0_1. rewrite <- Hand. apply IHp.
  discriminate 1.
  simpl. destruct p0.
    destruct (Pos.land p p0) eqn:Hand. discriminate 1.
      simpl. apply pos_le_0_0. rewrite <- Hand. apply IHp.
    destruct (Pos.land p p0) eqn:Hand. discriminate 1.
      simpl. apply pos_le_0_0. rewrite <- Hand. apply IHp.
  discriminate 1.
Qed.

Theorem and_le_r : forall a b, a .& b <= b.
Proof.
  intros. rewrite N.land_comm. apply and_le_l.
Qed.

Lemma mod_and_3 : forall a, a mod 2 ^ 2 = a .& 3.
Proof.
  intros. rewrite <- N.land_ones. reflexivity.
Qed.

Lemma n_lt_mul : forall n m,
  m > 0 ->
  n <= n * m.
Proof.
  intros.
  destruct m. discriminate. clear H.
  induction p.
    replace (N.pos p~1) with (2*N.pos p + 1) by reflexivity.
    rewrite N.mul_add_distr_l, N.mul_1_r, N.add_comm. 
    apply N.le_add_r.

    replace (N.pos p~0) with (2*N.pos p) by reflexivity.
    rewrite N.mul_comm, N.mul_shuffle0.
    apply N.le_trans with (n*N.pos p). assumption.
    rewrite <- N.mul_assoc. replace 2 with (1+1) by reflexivity.
    rewrite N.mul_add_distr_r, N.mul_1_l.
    apply N.le_add_r.

    rewrite N.mul_1_r. apply N.le_refl. 
Qed.

Lemma N_land_lo_hi_eq0 : forall a b,
  a < 2 ^ 8 ->
  a .& (b << 8) = 0.
Proof.
  intros.
  destruct a,b; try reflexivity.
  do 8 (destruct p; try reflexivity).
  all: destruct p; inversion H.
Qed.

Lemma N_add_lnot_land_3 : forall a,
  a < 2^32 ->
  (a .& N.lnot 3 32) + (a .& 3) = a.
Proof.
  intros. destruct a. reflexivity.
  destruct p; try reflexivity;
  destruct p; try reflexivity; simpl.
  1: replace (N.pos p~1~1) with ((Pos.Ndouble (Pos.Ndouble (N.pos p))) + 3)
       by reflexivity.
  2: replace (N.pos p~0~1) with ((Pos.Ndouble (Pos.Ndouble (N.pos p))) + 1)
       by reflexivity.
  3: replace (N.pos p~1~0) with ((Pos.Ndouble (Pos.Ndouble (N.pos p))) + 2)
       by reflexivity.
  4: replace (N.pos p~0~0) with ((Pos.Ndouble (Pos.Ndouble (N.pos p))) + 0)
       by reflexivity.
  all: apply N.add_cancel_r, f_equal, f_equal.
  all: rewrite <- N.mod_small with (b:=2^30), <- N.land_ones;
       try reflexivity.
  all: apply N.mul_lt_mono_pos_l with (p:=4); try reflexivity.
  all: replace (4*2^30) with (2^32) by reflexivity.
  1: replace (N.pos p~1~1) with (4 * (N.pos p) + 3) in H by reflexivity.
  2: replace (N.pos p~0~1) with (4 * (N.pos p) + 1) in H by reflexivity.
  3: replace (N.pos p~1~0) with (4 * (N.pos p) + 2) in H by reflexivity.
  4: replace (N.pos p~0~0) with (4 * (N.pos p) + 0) in H by reflexivity.
  4: assumption.
  all: eapply N.lt_trans; [apply N.lt_add_pos_r|eassumption]; reflexivity.
Qed.

Lemma mod_n_le: forall a b n,
  n ≠ 0 ->
  a mod n = b ->
  b <= a.
Proof.
  intros. rewrite <- H0. apply N.mod_le. assumption.
Qed.

Lemma and_mod_eq: forall a,
  a < 2^32 ->
  a .& N.lnot 3 32 = a - (a .& 3).
Proof.
  intros. symmetry.
  replace (a - (a .& 3)) with ((a .& N.lnot 3 32) + (a .& 3) - (a .& 3)).
  2:{ rewrite N_add_lnot_land_3 at 1. reflexivity. assumption. }
  rewrite N.add_sub. reflexivity.
Qed.

Theorem mem_ff_gt0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 255 > 0 ->
  m a > 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H.
  replace ((m (N.succ a) 
        .| (m (N.succ (N.succ a)) 
        .| m (N.succ (N.succ (N.succ a))) << 8) << 8) << 8 .& 255)
    with 0 in H.
  rewrite N.lor_0_r in H. replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  assumption.
  clear H. symmetry.
  remember (m (N.succ a) 
        .| (m (N.succ (N.succ a)) 
        .| m (N.succ (N.succ (N.succ a))) << 8) << 8)
  as z.
  destruct z; try reflexivity.
Qed.

Theorem mem_ff00_gt0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 65280 > 0 ->
  m (a+1) > 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H.
  replace (m a .& 65280) with 0 in H.
  replace 65280 with (255 << 8) in H by reflexivity.
  rewrite N.lor_0_l, <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H.
  rewrite N.land_lor_distr_l in H.
  replace ((m (N.succ (N.succ a)) 
         .| m (N.succ (N.succ (N.succ a))) << 8) << 8 .& 255)
    with 0 in H.
  rewrite N.lor_0_r in H. replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  rewrite N.add_1_r.
  assumption.
  clear H. symmetry.
  remember (m (N.succ (N.succ a)) 
         .| m (N.succ (N.succ (N.succ a))) << 8)
  as z.
  destruct z; try reflexivity.
  reflexivity.
  remember (m a) as z. destruct z; try reflexivity.
  symmetry. replace 65280 with (255 << 8) by reflexivity.
  apply N_land_lo_hi_eq0. rewrite Heqz. apply WTM.
Qed.

Theorem mem_ff0000_gt0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 16711680 > 0 ->
  m (a+2) > 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H.
  replace (m a .& 16711680) with 0 in H.
  replace 16711680 with (255 << 8 << 8) in H by reflexivity.
  rewrite N.lor_0_l, <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H; try reflexivity.
  rewrite N.land_lor_distr_l in H.
  replace (m (N.succ a) .& 255 << 8) with 0 in H.
  rewrite N.lor_0_l, <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H; try reflexivity.
  rewrite N.land_lor_distr_l in H.
  replace (m (N.succ (N.succ (N.succ a))) << 8 .& 255) with 0 in H.
  rewrite N.lor_0_r in H. replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  replace (a+2) with (a+(1+1)) by reflexivity.
  rewrite N.add_assoc, N.add_1_r, N.add_1_r.
  assumption.
  all: clear H; symmetry.
  remember (m (N.succ (N.succ (N.succ a)))) as z.
  destruct z; try reflexivity.
  apply N_land_lo_hi_eq0. apply WTM.
  replace 16711680 with (65280 << 8) by reflexivity.
  apply N_land_lo_hi_eq0. apply WTM.
Qed.

Theorem mem_ff000000_gt0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 4278190080 > 0 ->
  m (a+3) > 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H.
  replace (m a .& 4278190080) with 0 in H.
  replace 4278190080 with (255 << 8 << 8 << 8) in H by reflexivity.
  rewrite N.lor_0_l, <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H; try reflexivity.
  rewrite N.land_lor_distr_l in H.
  replace (m (N.succ a) .& 255 << 8 << 8) with 0 in H.
  rewrite N.lor_0_l, <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H; try reflexivity.
  rewrite N.land_lor_distr_l in H.
  replace (m (N.succ (N.succ a)) .& 255 << 8) with 0 in H.
  rewrite N.lor_0_l in H. replace 255 with (N.ones 8) in H by reflexivity.
  rewrite <- N.shiftl_land, N.land_ones, N.mod_small in H by apply WTM.
  replace (a+3) with (a+(1+1+1)) by reflexivity.
  rewrite N.add_assoc, N.add_assoc, N.add_1_r, N.add_1_r, N.add_1_r.
  replace 0 with (0*2^8) in H by reflexivity.
  rewrite N.shiftl_mul_pow2 in H.
  apply N.gt_lt, N.mul_lt_mono_pos_r, N.lt_gt in H; try reflexivity.
  assumption.
  all: clear H; symmetry.
  apply N_land_lo_hi_eq0. apply WTM.
  apply N_land_lo_hi_eq0. apply WTM.
  replace 4278190080 with (16711680 << 8) by reflexivity.
  apply N_land_lo_hi_eq0. apply WTM.
Qed.

Theorem mem_ff_eq0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 255 = 0 ->
  m a = 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_l in H.
  replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  assumption.
Qed.

Theorem mem_ff00_eq0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 65280 = 0 ->
  m (a+1) = 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  replace 65280 with (255 << 8) in H by reflexivity.
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_l in H.
  replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  rewrite N.add_1_r.
  assumption.
Qed.

Theorem mem_ff0000_eq0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 16711680 = 0 ->
  m (a+2) = 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  replace 16711680 with (255 << 8 << 8) in H by reflexivity.
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_l in H.
  replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  replace 2 with (1+1) by reflexivity.
  rewrite N.add_assoc, N.add_1_r, N.add_1_r.
  assumption.
Qed.

Theorem mem_ff000000_eq0 : forall m a,
  welltyped_memory m ->
  m Ⓓ[a] .& 4278190080 = 0 ->
  m (a+3) = 0.
Proof.
  intros m a WTM H.
  simpl in H. unfold getmem_little, Mb, mem_bits in H. simpl in H.
  rewrite N.land_lor_distr_l, N.lor_0_r in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  replace 4278190080 with (255 << 8 << 8 << 8) in H by reflexivity.
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_iff in H.
  destruct H as [_ H].
  rewrite <- N.shiftl_land, N.shiftl_mul_pow2 in H.
  replace 0 with (0*2^8) in H by reflexivity.
  apply N.mul_cancel_r in H; try discriminate.
  replace 255 with (N.ones 8) in H by reflexivity.
  rewrite N.land_ones, N.mod_small in H by apply WTM.
  replace 3 with (1+1+1) by reflexivity.
  rewrite N.add_assoc, N.add_assoc, N.add_1_r, N.add_1_r, N.add_1_r.
  assumption.
Qed.

Definition nilfree (m:addr->N) (start:addr) (len:N) :=
  forall i, i < len -> m (start+i) > 0.

Theorem nilfree_split : forall m a j k,
  nilfree m a j ->
  nilfree m (a+j) k ->
  nilfree m a (j+k).
Proof.
  unfold nilfree. intros.
  assert (Hlt: j <= i \/ i < j) by apply N.le_gt_cases.
  inversion Hlt. 2: apply H, H2.
  specialize H0 with (i-j).
  rewrite N.add_sub_assoc in H0 by assumption.
  rewrite N.add_sub_swap, N.add_sub in H0.
  apply H0. clear H H0 Hlt.
  assert (i <= j + k) by (apply N.lt_le_incl; assumption).
  assert (∃ x, i = j + x). exists (i-j).
  rewrite N.add_sub_assoc, N.add_comm, N.add_sub by assumption; reflexivity.
  destruct H0. rewrite H0, N.add_comm, N.add_sub.
  rewrite H0, <- N.add_lt_mono_l in H1; assumption.
  rewrite N.add_comm. apply N.le_add_r.
Qed.

Definition nilfree_dword (n:N) : N :=
  if N.eqb (n .& 255) 0 then 0 else
  if N.eqb (n .& 65280) 0 then 1 else
  if N.eqb (n .& 16711680) 0 then 2 else
  if N.eqb (n .& 4278190080) 0 then 3 else 4.

Definition loop_inv (n _r0 r0 r1 r2:N) (m:addr->N) :=
  ((n ≠ 0 /\ r2 = m Ⓓ[r1 - 4] /\ nilfree m _r0 r0 
          /\ r0 + 4 <= r1 /\ r0 = 4*n - (_r0 .& 3)) \/
   (n = 0 /\ ((_r0 mod 4 = 0 /\ r2 = m Ⓓ[r1 - 4]) \/
              (_r0 mod 4 = 1 /\ r2 = m Ⓓ[r1 - 4] .| 255) \/
              (_r0 mod 4 = 2 /\ r2 = m Ⓓ[r1 - 4] .| 255 .| 65280) \/
              (_r0 mod 4 = 3 /\ r2 = m Ⓓ[r1 - 4] .| 255 .| 65280 .| 16711680))
          /\ r0 = (2^32 ⊖ (_r0 .& 3)))).

Definition strlen_invs (m:addr->N) (_r0:N) (a:addr) (s:store) :=
  match a with
  | 0 => Some (s R_R0 = Ⓓ_r0)
  | 40 => Some (∃ n r0 r1 r2,
                   s R_R0 = Ⓓr0 /\ s R_R1 = Ⓓr1 /\ s R_R2 = Ⓓr2
                /\ r1 = (_r0 .& N.lnot 3 32) + 4 * (n + 1)
                /\ r1 < 2^32
                /\ loop_inv n _r0 r0 r1 r2 m)
  | 68 => Some (∃ n r0 r1 r2,
                   s R_R0 = Ⓓr0 /\ s R_R1 = Ⓓr1 /\ s R_R2 = Ⓓr2
                /\ r1 = (_r0 .& N.lnot 3 32) + 4 * (n + 1)
                /\ r1 < 2^32
                /\ loop_inv n _r0 r0 r1 r2 m
                /\ nilfree_dword r2 < 4)
  | 92 => Some (∃ r0,
                   s R_R0 = Ⓓr0 
                /\ nilfree m _r0 r0
                /\ m (_r0 + r0) = 0)
  | _ => None
  end.

Definition strlen_post (mem:addr->N) (_r0:N) (_:exit) (s:store) :=
  exists r0, s R_R0 = VaN r0 32 /\
             mem (_r0 + r0) = 0 /\
             forall i, i < r0 -> mem (_r0+i) > 0.

Definition strlen_invset (mem:addr->N) (_r0:N) :=
  invs (strlen_invs mem _r0) (strlen_post mem _r0).

Theorem strlen_partial_correctness:
  forall s _r0 lr mem n s' x
         (HI0: ~ mem_readable s (2^32 - 1)%N)
         (MDL0: models armtypctx s)
         (_R0LO: _r0 < 2^32-3)
         (_R00: s R_R0 = VaN _r0 32)
         (LR0: s R_LR = VaN lr 32)
         (MEM0: s V_MEM32 = VaM mem 32)
         (RET: strlen_arm s lr = None)
         (XP0: exec_prog fh strlen_arm 0 s n s' x),
  trueif_inv (strlen_invset mem _r0 strlen_arm x s').
Proof.
  intros.
  eapply prove_invs. exact XP0.
  assumption.
  intros.
  assert (MEM: s1 V_MEM32 = VaM mem 32).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  assert (HI: ~ mem_readable s1 (2^32 - 1)%N).
    unfold mem_readable. intro H.
    destruct H as [r [H1 H2]]. apply HI0. exists r.
    split; [|exact H2].
    erewrite <- strlen_preserves_readable; eassumption.
  assert (MDL: models armtypctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strlen_welltyped. exact XP.
  assert (LR: s1 R_LR = VaN lr 32).
    rewrite <- LR0. eapply strlen_preserves_lr. eassumption.
  rewrite (strlen_nwc s1) in RET.
  clear s _R00 LR0 HI0 MDL0 MEM0 XP XP0.
  assert (WTM:=arm_wtm MDL MEM). simpl in WTM.

  shelve_cases 32 PRE. Unshelve.

  Local Ltac step := time arm_step.
  2-4: shelve.
  do 2 step.
    (* just read 4 bytes, show that this didn't overflow *)
    assert (LM4: (_r0 .& N.lnot 3 32) + 4 < 2 ^ 32).
      apply N.lt_nge. intro H. apply HI.
      replace (_r0 .& N.lnot 3 32) with (2^32-4) in ACC.
      apply (ACC 3); reflexivity.
      apply N.le_antisymm.
        apply N.le_sub_le_add_r. exact H.
        eapply N.le_trans. eapply and_le_l.
        replace (2^32-4) with (2^32-3-1) by reflexivity.
        rewrite <- N.pred_sub.
        apply N.lt_le_pred. exact _R0LO.
  do 3 step.
  (* 0 -> 40, 4-byte aligned, stepped *)
  apply Neqb_ok, if_true, Neqb_ok in BC; [|discriminate].
  rename BC into Hmod.
  (* step all unaligned until 40 since inv proofs are similar *)
  all: cycle 1.
  apply N.eqb_neq, if_neq_then, if_false, N.eqb_neq in BC; try discriminate.
  assert (Hlt: _r0 mod 2^2 < 4) by (apply N.mod_lt; discriminate 1).
  apply N_lt_4 in Hlt; destruct Hlt as [Hmod|Hmod]; [contradiction|].

  do 3 step.
    destruct Hmod as [Hmod|[Hmod|Hmod]];
    try (rewrite Hmod in BC0; discriminate);
    clear BC BC0.
  do 2 step.
  2: rewrite Hmod in BC; discriminate.
  clear BC tmp tmp0 tmp1.

  all: cycle 1.
  destruct Hmod as [Hmod|Hmod];
  try (rewrite Hmod in BC0; discriminate).
  clear BC BC0.

  do 2 step.
  1,2: destruct Hmod as [Hmod|Hmod];
  try (rewrite Hmod in BC; discriminate);
  clear BC tmp tmp0 tmp1.
  all: cycle 2.
  (* at instruction 40, after executing all paths from 0 *)
  (* goals should be:
     1. byte aligned
     2. r0 % 4 = 1 (one byte padded)
     3. r0 % 4 = 2 (two bytes padded)
     4. r0 % 4 = 3 (three bytes padded)
  *)
  all: exists 0; do 3 eexists;
       split;[|split;[|split;[|split;[|split]]]];
       try reflexivity; try assumption.
  all: right; split; try reflexivity;
       rewrite N.add_sub, <- mod_and_3.
  1: split; [left|reflexivity].
  2: split; [right; left|reflexivity].
  3: split; [right; right; left|reflexivity].
  4: split; [right; right; right|reflexivity].
  all: split; [assumption|].
  all: reflexivity.

  Unshelve.
  2-3: shelve.
  destruct PRE as [n0[r0[r1[r2[R0[R1[R2[R1eq[R1lt Iter]]]]]]]]].

  step.
  step; [apply Neqb_ok, if_false in BC; [| discriminate 1]|].
  step; [apply Neqb_ok, if_false in BC0; [| discriminate 1]|].
  step; [apply Neqb_ok, if_false in BC1; [| discriminate 1]|].
  step; [apply Neqb_ok, if_false in BC2; [| discriminate 1]|].
  step. 2: rewrite BC2 in BC3; discriminate.
    (* all 4 bytes nilfree, read 4 bytes *)
    assert (LM4: r1 + 4 < 2 ^ 32).
    apply N.lt_nge. intro H. apply HI.
    replace (2^32-1) with (r1 + (N.pred(2^32) - r1)).
    apply ACC. apply (N.add_lt_mono_r _ _ r1).
    rewrite N.sub_add, N.add_comm
         by apply N.lt_le_pred, (arm_regsize MDL R1).
    apply N.lt_le_trans with (2^32); [reflexivity | assumption].
    rewrite N.add_sub_assoc, N.add_comm, N.add_sub
         by apply N.lt_le_pred, (arm_regsize MDL R1).
    reflexivity.
  step. 2: discriminate.
  clear BC3 BC4 tmp tmp0 tmp1 tmp2 tmp3.
  (* loops back to 40, all 4 bytes non-nil *)
  exists (n0+1); do 3 eexists.
    split;[|split;[|split;[|split;[|split]]]];
    try reflexivity; try assumption.
    rewrite N.mul_add_distr_l, N.add_assoc, <- R1eq
      by discriminate 1.
    reflexivity.
    left. split;[|split;[|split;[|split]]].
    rewrite N.add_comm, N.add_1_l; apply N.neq_succ_0.
    rewrite N.add_sub; reflexivity.
    destruct Iter as [[Neq0[HR2[NF[R0lt R0eq]]]]|[Hn0 [Hmod R0eq]]].
    (* nilfree, show that 4 bytes were checked *)
    rewrite N.mod_small.
    apply nilfree_split; [assumption|].
    unfold nilfree; intros.
    (* do a whole bunch of rewriting and substitutions *)
    (* eventually boil down to showing r2 = mem[_r0 + r0] *)
    apply N.add_cancel_r with (p:=(_r0 .& 3)) in R0eq.
    rewrite N.sub_add in R0eq
      by (rewrite <- mod_and_3; replace (2^2) with 4 by reflexivity;
          apply N.le_trans with 4;
          [ apply N.lt_le_incl, N.mod_lt; discriminate 1
          | apply n_lt_mul, N.gt_lt_iff, N.neq_0_lt_0; assumption]).
    rewrite N.mul_add_distr_l, N.add_assoc, <- R0eq, N.add_assoc in R1eq.
    rewrite N.add_comm, N.add_shuffle0, <- N.add_comm, N_add_lnot_land_3 in R1eq
      by (eapply N.lt_trans; [eassumption | reflexivity]).
    rewrite R1eq, N.add_sub in HR2.
    (* done rewriting *)
    subst r2.
    (* go through each byte, and show it's nilfree *)
    apply N_lt_4 in H; destruct H as [Hi|[Hi|[Hi|Hi]]]; subst i.
    (* byte 0 *)
    rewrite N.add_0_r. rewrite <- N.land_ones in BC.
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
    apply mem_ff_gt0; assumption.
    (* byte 1 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
    apply mem_ff00_gt0; assumption.
    (* byte 2 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
    apply mem_ff0000_gt0; assumption.
    (* byte 3 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC2.
    apply mem_ff000000_gt0; assumption.

    apply N.le_lt_trans with (m:=r1);
     [ assumption
     | apply N.lt_trans with (m:=r1+4);
       [ apply N.lt_add_pos_r; reflexivity
       | assumption]].

    (* first time looping, some bytes could be padded *)
    subst n0.
    simpl (4*(0+1)) in R1eq.
    rewrite <- mod_and_3 in R0eq by discriminate 1.
    replace (2^2) with 4 in R0eq by reflexivity.
    rewrite and_mod_eq, <- mod_and_3 in R1eq
      by (eapply N.lt_trans; [eassumption | reflexivity]).
    replace (2^2) with 4 in R1eq by reflexivity.
    (* check all 4 cases of padding *)
    destruct Hmod as [[Hmod HR2]|[[Hmod HR2]|[[Hmod HR2]|[Hmod HR2]]]];
    rewrite Hmod in *.
    (* no padding, 4-byte aligned *)
    rewrite N.sub_0_r, N.mod_same in R0eq by discriminate.
    rewrite N.sub_0_r in R1eq.
    subst r0 r1.
    rewrite N.add_sub in HR2.
    subst r2.
    rewrite N.add_0_l, N.mod_small by reflexivity.
    (* essentially identical to just before *)
    (* show each byte is nilfree *)
    unfold nilfree; intros.
    apply N_lt_4 in H; destruct H as [Hi|[Hi|[Hi|Hi]]]; subst i.

    rewrite N.add_0_r. rewrite <- N.land_ones in BC.
    (* byte 0 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
    apply mem_ff_gt0; assumption.
    (* byte 1 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
    apply mem_ff00_gt0; assumption.
    (* byte 2 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
    apply mem_ff0000_gt0; assumption.
    (* byte 3 *)
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC2.
    apply mem_ff000000_gt0; assumption.

    (* 1 byte padded, _r0 % 4 = 1 *)
    replace _r0 with (_r0-1+1)
      by (rewrite N.sub_add; 
         [ reflexivity
         | apply mod_n_le with (n:=4); [discriminate|assumption]]).
    subst r0 r1; rewrite N.add_sub in HR2; subst r2.
    replace (2 ^ 32 ⊖ 1 ⊕ 4) with 3 by reflexivity.
    (* show 3 bytes are nilfree *)
    unfold nilfree; intros.
    assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
    apply N_lt_4 in Hi;
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
      try discriminate H; clear H.
    1-3: rewrite <- N.add_assoc.
    (* byte 0 *)
    rewrite N.land_lor_distr_l, N.lor_0_r in BC0.
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
    apply mem_ff00_gt0; assumption.
    (* byte 1 *)
    rewrite N.land_lor_distr_l, N.lor_0_r in BC1.
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
    apply mem_ff0000_gt0; assumption.
    (* byte 2 *)
    rewrite N.land_lor_distr_l, N.lor_0_r in BC2.
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC2.
    apply mem_ff000000_gt0; assumption.

    (* 2 bytes padded, _r0 % 4 = 2 *)
    replace _r0 with (_r0-2+2)
      by (rewrite N.sub_add; 
         [ reflexivity
         | apply mod_n_le with (n:=4); [discriminate|assumption]]).
    subst r0 r1; rewrite N.add_sub in HR2; subst r2.
    replace (2 ^ 32 ⊖ 2 ⊕ 4) with 2 by reflexivity.
    (* show 2 bytes are nilfree *)
    unfold nilfree; intros.
    assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
    apply N_lt_4 in Hi;
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
      try discriminate H; clear H.
    1-2: rewrite <- N.add_assoc.
    do 2 (rewrite N.land_lor_distr_l, N.lor_0_r in BC1).
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
    apply mem_ff0000_gt0; assumption.

    do 2 (rewrite N.land_lor_distr_l, N.lor_0_r in BC2).
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC2.
    apply mem_ff000000_gt0; assumption.

    (* 3 bytes padded, _r0 % 4 = 3 *)
    replace _r0 with (_r0-3+3)
      by (rewrite N.sub_add; 
         [ reflexivity
         | apply mod_n_le with (n:=4); [discriminate|assumption]]).
    subst r0 r1; rewrite N.add_sub in HR2; subst r2.
    replace (2 ^ 32 ⊖ 3 ⊕ 4) with 1 by reflexivity.
    (* show 1 byte nilfree *)
    unfold nilfree; intros.
    assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
    apply N_lt_4 in Hi;
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
      try discriminate H; clear H.

    rewrite N.add_0_r.
    do 3 (rewrite N.land_lor_distr_l, N.lor_0_r in BC2).
    apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC2.
    apply mem_ff000000_gt0; assumption.
    (* r0 ⊕ 4 + 4 <= r1 + 4 *)
    apply N.add_le_mono_r.
    destruct Iter as [[Hn[HR2[NF[R0lt R0eq]]]]|[Hn[R2eq R0eq]]].
    rewrite N.mod_small 
      by (apply N.le_lt_trans with (m:=r1); 
          [ assumption
          | apply N.lt_trans with (m:=r1+4); 
            [ apply N.lt_add_pos_r; reflexivity
            | assumption]]); assumption.
    rewrite N.mul_add_distr_l, N.add_assoc, <- N.add_comm in R1eq.
    subst r0 r1.
    assert (Hmod: _r0 .& 3 < 4)
      by (rewrite <- mod_and_3; apply N.mod_lt; discriminate).
    apply N_lt_4 in Hmod.
    destruct Hmod as [Hmod|[Hmod|[Hmod|Hmod]]]; rewrite Hmod.
    1-4: apply N.le_trans with (m:=4); [discriminate | apply N.le_add_r].
    (* r0 ⊕ 4 = 4 * (n0 + 1) - _r0 mod 2 ^ 2 *)
    destruct Iter as [[Hn[HR2[NF[R0lt R0eq]]]]|[Hn[R2eq R0eq]]].
    rewrite N.mod_small.
    subst r0.
    rewrite N.mul_add_distr_l, N.add_comm, N.add_sub_assoc,
            N.add_comm.
    reflexivity.
    destruct n0; try contradiction.
    assert (Hmod: _r0 .& 3 < 4)
      by (rewrite <- mod_and_3; apply N.mod_lt; discriminate).
    apply N_lt_4 in Hmod.
    destruct Hmod as [Hmod|[Hmod|[Hmod|Hmod]]];
    rewrite Hmod; discriminate.
    apply N.le_lt_trans with (m:=r1);
     [ assumption
     | apply N.lt_trans with (m:=r1+4);
       [ apply N.lt_add_pos_r; reflexivity
       | assumption]].
    subst n0 r0.
    assert (Hmod: _r0 .& 3 < 4)
      by (rewrite <- mod_and_3; apply N.mod_lt; discriminate).
    apply N_lt_4 in Hmod.
    destruct Hmod as [Hmod|[Hmod|[Hmod|Hmod]]]; rewrite Hmod.
    1-4: reflexivity.

  (* rest of these cases eventually step to 68 *)
  (* byte 3 was nil *)
  apply N.eqb_neq, if_neq_else, if_true in BC2; try discriminate 1.
  step; [rewrite BC2 in BC3; discriminate | clear BC3].
  step; [rewrite BC2 in BC3; discriminate | clear BC3].
  all: cycle 1.
  (* byte 2 was nil *)
  apply N.eqb_neq, if_neq_else, if_true in BC1; try discriminate 1.
  step; [rewrite BC1 in BC2; discriminate | clear BC2].
  step; [rewrite BC1 in BC2; discriminate | clear BC2].
  step; [rewrite BC1 in BC2; discriminate | clear BC2].
  all: cycle 1.
  (* byte 1 was nil *)
  apply N.eqb_neq, if_neq_else, if_true in BC0; try discriminate 1.
  step; [rewrite BC0 in BC1; discriminate | clear BC1].
  step; [rewrite BC0 in BC1; discriminate | clear BC1].
  step; [rewrite BC0 in BC1; discriminate | clear BC1].
  step; [rewrite BC0 in BC1; discriminate | clear BC1].
  all: cycle 1.
  (* byte 0 was nil *)
  apply N.eqb_neq, if_neq_else, if_true in BC; try discriminate 1.
  step; [rewrite BC in BC0; discriminate | clear BC0].
  step; [rewrite BC in BC0; discriminate | clear BC0].
  step; [rewrite BC in BC0; discriminate | clear BC0].
  step; [rewrite BC in BC0; discriminate | clear BC0].
  step; [rewrite BC in BC0; discriminate | clear BC0].
  (* Now at instruction 68 where a nil byte was detected *)
  (* somewhere in the dword (4 sub-goals)                *)
  all: exists n0; do 3 eexists;
       split;[|split;[|split;[|split;[|split;[|split]]]]];
       try reflexivity; try rewrite mod_and_3; try assumption.
  all: unfold nilfree_dword; replace 255 with (N.ones 8) by reflexivity;
       rewrite N.land_ones, BC;
       try rewrite BC0; try rewrite BC1; try rewrite BC2;
       reflexivity.

  Unshelve.
  2: shelve.
  destruct PRE as [n0[r0[r1[r2[R0[R1[R2[R1eq[R1lt[Iter DW]]]]]]]]]].
  (* step all paths to 92 *)
  do 2 step.
  apply Neqb_ok, if_false in BC; try discriminate 1.
  step; [clear BC0 | rewrite BC in BC0; discriminate].
  rewrite <- N.land_ones in BC;
  replace (N.ones 8) with 255 in BC by reflexivity.
  step. apply Neqb_ok, if_false in BC0; try discriminate 1.
  step; [clear BC1 | rewrite BC0 in BC1; discriminate].
  step. apply Neqb_ok, if_false in BC1; try discriminate 1.
  clear tmp tmp0 tmp1 tmp2 tmp3 tmp4.

  all: cycle 1.
  apply N.eqb_neq, if_neq_else, if_true in BC1; try discriminate 1.
  clear tmp tmp0 tmp1 tmp2 tmp3.

  all: cycle 1.
  step. discriminate. clear BC0.
  apply N.eqb_neq, if_neq_else, if_true in BC1; try discriminate 1.
  step. apply Neqb_ok, if_false in BC0; try discriminate 1.
  rewrite BC0 in BC1. discriminate.
  clear BC0 tmp tmp0 tmp1.

  all: cycle 1.
  step. discriminate. clear BC.
  apply N.eqb_neq, if_neq_else, if_true in BC0; try discriminate 1.
  step; [rewrite BC0 in BC; discriminate | clear BC].
  step; [rewrite BC0 in BC; discriminate | clear BC].
  step; [rewrite BC0 in BC; discriminate | clear BC].
  rewrite <- N.land_ones in BC0;
  replace (N.ones 8) with 255 in BC0 by reflexivity.
  (* at instruction 92
     the last byte has either 0, 1, 2, or 3 non-nil bytes before the nil *)
  all: eexists;
       split;[|split];
       try reflexivity; try rewrite <- R1eq; try assumption.
  (* show that r0 bytes are nilfree *)
  (* this should put them at the top of the goal list *)
  all: destruct Iter as [[Hn[HR2[NF[R0lt R0eq]]]]|[Hn[R2eq R0eq]]].
  (* r2 = [ 00 ?? ?? ?? ] *)
  (* looped at least once *)
  assumption.
  (* didn't loop *)
  (* must be 4-byte aligned, and first byte is 0 *)
  subst n0.
  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]].
  rewrite <- mod_and_3 in R0eq.
  replace (2^2) with 4 in R0eq by reflexivity.
  rewrite Hmod, N.mod_same in R0eq by discriminate.
  subst r0.
  unfold nilfree; intros. apply N.nlt_0_r in H. inversion H.
  (* padded with at least 1 byte, so these 3 cases are contradictions *)
  1-3: subst r2; apply Neqb_ok in BC0;
       repeat (
         rewrite N.land_lor_distr_l, N.lor_comm in BC0;
         try rewrite N.lor_0_l in BC0);
       apply N.lor_eq_0_l in BC0; inversion BC0.
  all: cycle 2.
  (* looped at least once *)
  1,5,9: assert (R2val: r2 = mem Ⓓ[ _r0 + r0]).
  1,3,5: apply N.add_cancel_r with (p:=(_r0 .& 3)) in R0eq; 
         rewrite N.sub_add in R0eq
           by (rewrite <- mod_and_3; replace (2^2) with 4 by reflexivity;
               apply N.le_trans with 4; 
               [ apply N.lt_le_incl, N.mod_lt; discriminate
               | apply n_lt_mul, N.gt_lt_iff, N.neq_0_lt_0; assumption]);
         symmetry in R0eq;
         rewrite N.mul_add_distr_l, N.add_assoc, R0eq, N.add_assoc in R1eq;
         rewrite N.add_comm, N.add_shuffle0, <- N.add_comm, N_add_lnot_land_3 in R1eq;
         rewrite R1eq, N.add_sub in HR2; subst r2; try reflexivity.
  1-3: eapply N.lt_trans; [eassumption | reflexivity].
  1-3: clear HR2; subst r2.
  (* r2 = [ nn nn nn 00 ] *)
  replace (r0 ⊕ 1 ⊕ 1 ⊕ 1) with (r0 + 3)
    by (rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc,
                N.add_mod_idemp_l, <- N.add_assoc by discriminate;
        rewrite N.mod_small;
        [ reflexivity 
        | apply N.lt_trans with (m:=r0+4);
          [ apply N.add_lt_mono_l; reflexivity
          | apply N.le_lt_trans with (m:=r1); assumption ]]).
  apply nilfree_split; try assumption.
  unfold nilfree; intros.
  assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i;
  try discriminate H; clear H.
  (* byte 0 nilfree *)
  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.
  (* byte 1 nilfree *)
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.
  (* byte 2 nilfree *)
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
  apply mem_ff0000_gt0; assumption.

  (* r2 = [ nn nn 00 ?? ] *)
  replace (r0 ⊕ 1 ⊕ 1) with (r0 + 2)
    by (rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc by discriminate;
        rewrite N.mod_small;
        [ reflexivity
        | apply N.lt_trans with (m:=r0+4);
          [ apply N.add_lt_mono_l; reflexivity
          | apply N.le_lt_trans with (m:=r1); assumption ]]).
  apply nilfree_split; try assumption.
  unfold nilfree; intros.
  assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i;
  try discriminate H; clear H.
  (* byte 0 nilfree *)
  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.
  (* byte 1 nilfree *)
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.

  (* r2 = [ nn 00 ?? ?? ] *)
  replace (r0 ⊕ 1) with (r0 + 1)
    by (rewrite N.mod_small;
        [ reflexivity
        | apply N.lt_trans with (m:=r0+4);
          [ apply N.add_lt_mono_l; reflexivity
          | apply N.le_lt_trans with (m:=r1); assumption ]]).
  apply nilfree_split; try assumption.
  unfold nilfree; intros.
  apply N.lt_1_r in H; subst i.
  (* byte 0 nilfree *)
  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.

  (* didn't loop, so string < 4 bytes *)
  1,4,7: subst n0.
  replace (r0 ⊕ 1 ⊕ 1 ⊕ 1) with (r0 ⊕ 3)
    by (rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc,
                N.add_mod_idemp_l, <- N.add_assoc by discriminate;
                reflexivity).
  rewrite and_mod_eq, <- mod_and_3 in R1eq
    by (eapply N.lt_trans; [eassumption | reflexivity]).
  replace (2^2) with 4 in R1eq by reflexivity.
  simpl (4*(0+1)) in R1eq.
  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  1: replace (2 ^ 32 ⊖ 0 ⊕ 3) with 3 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 3) with 2 by reflexivity.
  3: replace (2 ^ 32 ⊖ 2 ⊕ 3) with 1 by reflexivity.
  4: replace (2 ^ 32 ⊖ 3 ⊕ 3) with 0 by reflexivity.
  1-4: rewrite Hmod in *; subst r1; rewrite N.add_sub in R2eq;
       try rewrite N.sub_0_r in R2eq; subst r2.
  (* 4-byte aligned *)
  unfold nilfree; intros.
  assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i;
    try discriminate H; clear H.

  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
  apply mem_ff0000_gt0; assumption.

  (* 1 byte padded *)
  replace _r0 with (_r0-1+1)
    by (rewrite N.sub_add; 
         [ reflexivity
         | apply mod_n_le with (n:=4); [discriminate|assumption]]).
  unfold nilfree; intros.
  assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
    try discriminate H; clear H.

  rewrite N.add_0_r. rewrite N.land_lor_distr_l, N.lor_0_r in BC0.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.

  rewrite N.land_lor_distr_l, N.lor_0_r in BC1.
  rewrite <- N.add_assoc.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
  apply mem_ff0000_gt0; assumption.
  (* 2 bytes padded *)
  replace _r0 with (_r0-2+2)
    by (rewrite N.sub_add; 
         [ reflexivity
         | apply mod_n_le with (n:=4); [discriminate|assumption]]).
  unfold nilfree; intros.
  assert (Hi: i < 4) by (eapply N.lt_trans; [eassumption|reflexivity]).
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
    try discriminate H; clear H.

  rewrite N.add_0_r.
  rewrite N.land_lor_distr_l, N.lor_0_r,
          N.land_lor_distr_l, N.lor_0_r in BC1.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC1.
  apply mem_ff0000_gt0; assumption.
  (* 3 bytes padded *)
  unfold nilfree; intros. apply N.nlt_0_r in H. inversion H.

  replace (r0 ⊕ 1 ⊕ 1) with (r0 ⊕ 2).
  2: rewrite N.add_mod_idemp_l, <- N.add_assoc by discriminate 1;
       simpl (1+1); reflexivity.
  rewrite and_mod_eq, <- mod_and_3 in R1eq; replace (2^2) with 4 in R1eq by reflexivity.
  2: eapply N.lt_trans; [eassumption | reflexivity].
  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  4:{ subst r2; apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  1: replace (2 ^ 32 ⊖ 0 ⊕ 2) with 2 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 2) with 1 by reflexivity.
  3: replace (2 ^ 32 ⊖ 2 ⊕ 2) with 0 by reflexivity.
  1-3: simpl (4*(0+1)) in R1eq;
       rewrite Hmod in *; subst r1; rewrite N.add_sub in R2eq.
  (* %4 = 0 *)
  rewrite N.sub_0_r in R2eq. subst r2.
  unfold nilfree; intros.
  assert (Hi: i < 4). eapply N.lt_trans; [eassumption|reflexivity].
    apply N_lt_4 in Hi;
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i;
      try discriminate H; clear H.

  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.

  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.

  (* %4  = 1 *)
  replace _r0 with (_r0-1+1).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  unfold nilfree; intros.
  subst r2.
  assert (Hi: i < 4). eapply N.lt_trans; [eassumption|reflexivity].
  apply N_lt_4 in Hi;
  destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i; 
    try discriminate H; clear H.

  rewrite N.add_0_r. rewrite N.land_lor_distr_l, N.lor_0_r in BC0.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC0.
  apply mem_ff00_gt0; assumption.

  unfold nilfree; intros. apply N.nlt_0_r in H. inversion H.

  rewrite and_mod_eq, <- mod_and_3 in R1eq; replace (2^2) with 4 in R1eq by reflexivity.
  2: eapply N.lt_trans; [eassumption | reflexivity].
  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  3:{ subst r2; apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  3:{ subst r2; apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm,
          N.lor_0_l, N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  1: replace (2 ^ 32 ⊖ 0 ⊕ 1) with 1 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 1) with 0 by reflexivity.
  1-2: simpl (4*(0+1)) in R1eq;
       rewrite Hmod in *; subst r1; rewrite N.add_sub in R2eq.
  (* %4 = 0 *)
  rewrite N.sub_0_r in R2eq. subst r2.
  unfold nilfree; intros.
  assert (Hi: i < 4). eapply N.lt_trans; [eassumption|reflexivity].
    apply N_lt_4 in Hi;
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; subst i;
      try discriminate H; clear H.

  rewrite N.add_0_r.
  apply N.eqb_neq, N.neq_0_lt_0, N.lt_gt in BC.
  apply mem_ff_gt0; assumption.

  (* %4  = 1 *)
  unfold nilfree; intros. apply N.nlt_0_r in H. inversion H.

  (* show last byte is nil *)
  (* looped *)
  1,3,5,7: assert (R2val: r2 = mem Ⓓ[ _r0 + r0]).
  1,3,5,7: apply N.add_cancel_r with (p:=(_r0 .& 3)) in R0eq; 
           rewrite N.sub_add in R0eq
           by (rewrite <- mod_and_3; replace (2^2) with 4 by reflexivity;
               apply N.le_trans with 4; 
               [ apply N.lt_le_incl, N.mod_lt; discriminate
               | apply n_lt_mul, N.gt_lt_iff, N.neq_0_lt_0; assumption]);
           symmetry in R0eq;
       rewrite N.mul_add_distr_l, N.add_assoc, R0eq, N.add_assoc in R1eq;
       simpl (4*1) in R1eq;
       rewrite N.add_comm, N.add_shuffle0, <- N.add_comm, N_add_lnot_land_3 in R1eq;
       rewrite R1eq, N.add_sub in HR2; subst r2; try reflexivity.
  1-4: eapply N.lt_trans; [eassumption | reflexivity].
  1-4: clear HR2; subst r2.

  unfold nilfree_dword in DW. rewrite BC, BC0, BC1 in DW.
  destruct (mem Ⓓ[ _r0 + r0] .& 4278190080 =? 0) eqn:BC2; try discriminate.
  apply Neqb_ok in BC2.
  replace (r0 ⊕ 1 ⊕ 1 ⊕ 1) with (r0 + 3).
  2: rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc,
          N.add_mod_idemp_l, <- N.add_assoc by discriminate 1;
       simpl (1+1+1);
       rewrite N.mod_small;
       [ reflexivity 
       | apply N.lt_trans with (m:=r0+4);
         [ apply N.add_lt_mono_l; reflexivity
         | apply N.le_lt_trans with (m:=r1); assumption ]].
  rewrite N.add_assoc. apply mem_ff000000_eq0 in BC2; assumption.

  replace (r0 ⊕ 1 ⊕ 1) with (r0 + 2).
  2: rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc by discriminate;
       simpl (1+1); 
       rewrite N.mod_small;
       [ reflexivity
       | apply N.lt_trans with (m:=r0+4);
         [ apply N.add_lt_mono_l; reflexivity
         | apply N.le_lt_trans with (m:=r1); assumption ]].
  rewrite N.add_assoc.
  apply Neqb_ok in BC1.
  apply mem_ff0000_eq0 in BC1; assumption.

  replace (r0 ⊕ 1) with (r0 + 1).
  2: rewrite N.mod_small;
     [ reflexivity
     | apply N.lt_trans with (m:=r0+4);
       [ apply N.add_lt_mono_l; reflexivity
       | apply N.le_lt_trans with (m:=r1); assumption ]].
  rewrite N.add_assoc.
  apply Neqb_ok in BC1.
  apply mem_ff00_eq0 in BC1; assumption.

  apply Neqb_ok in BC0.
  apply mem_ff_eq0 in BC0; assumption.

  (* didn't loop *)
  all: subst n0; rewrite and_mod_eq, <- mod_and_3, N.mul_add_distr_l, N.add_assoc in R1eq;
       replace (2^2) with 4 in R1eq by reflexivity;
       simpl (4*(0+1)) in R1eq.
  2,4,6,8: eapply N.lt_trans; [eassumption | reflexivity].
  all: cycle -1.
  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]].
  rewrite <- mod_and_3 in R0eq. replace (2^2) with 4 in R0eq by reflexivity.
  rewrite Hmod, N.mod_same in R0eq by discriminate.
  subst r0. rewrite Hmod, N.sub_0_r in R1eq.
  subst r1. rewrite N.add_sub in R2eq.
  subst r2.
  rewrite N.add_0_r. rewrite N.add_0_r in BC0.
  apply Neqb_ok in BC0. apply mem_ff_eq0 in BC0; assumption.

  1-3: subst r2; apply Neqb_ok in BC0.

  rewrite N.land_lor_distr_l, N.lor_comm in BC0.
  apply N.lor_eq_0_l in BC0. inversion BC0.

  rewrite N.land_lor_distr_l, N.lor_comm,
          N.lor_0_l, N.land_lor_distr_l, N.lor_comm in BC0.
  apply N.lor_eq_0_l in BC0. inversion BC0.

  rewrite N.land_lor_distr_l, N.lor_comm,
          N.lor_0_l, N.land_lor_distr_l, N.lor_comm,
          N.lor_0_l, N.land_lor_distr_l, N.lor_comm in BC0.
  apply N.lor_eq_0_l in BC0. inversion BC0.

  replace (r0 ⊕ 1 ⊕ 1 ⊕ 1) with (r0 ⊕ 3).
  2: rewrite N.add_mod_idemp_l with (a:=r0 + 1), <- N.add_assoc,
          N.add_mod_idemp_l, <- N.add_assoc by discriminate 1;
       simpl (1+1+1); reflexivity.

  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  1: replace (2 ^ 32 ⊖ 0 ⊕ 3) with 3 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 3) with 2 by reflexivity.
  3: replace (2 ^ 32 ⊖ 2 ⊕ 3) with 1 by reflexivity.
  4: replace (2 ^ 32 ⊖ 3 ⊕ 3) with 0 by reflexivity.
  1-4: rewrite Hmod in *; subst r1; rewrite N.add_sub, N.add_0_r in R2eq.
  (* %4 = 0 *)
  rewrite N.sub_0_r in R2eq.
  1-4: subst r2; unfold nilfree_dword in DW; rewrite BC, BC0, BC1 in DW.
  destruct (mem Ⓓ[ _r0] .& 4278190080 =? 0) eqn:BC2; try discriminate.
  apply Neqb_ok in BC2. apply mem_ff000000_eq0 in BC2; assumption.

  replace _r0 with (_r0-1+1).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  destruct (mem Ⓓ[ _r0 - 1 ] .| 255 .& 4278190080 =? 0) eqn:BC2; try discriminate.
  apply Neqb_ok in BC2.
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l in BC2.
  rewrite <- N.add_assoc.
  apply mem_ff000000_eq0 in BC2; assumption.

  replace _r0 with (_r0-2+2).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  destruct (mem Ⓓ[ _r0 - 2] .| 255 .| 65280 .& 4278190080 =? 0) eqn:BC2; try discriminate.
  apply Neqb_ok in BC2.
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l,
          N.land_lor_distr_l, N.lor_comm, N.lor_0_l in BC2.
  rewrite <- N.add_assoc.
  apply mem_ff000000_eq0 in BC2; assumption.

  replace _r0 with (_r0-3+3).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  destruct (mem Ⓓ[ _r0 - 3] .| 255 .| 65280 .| 16711680 .& 4278190080 =? 0) eqn:BC2; try discriminate.
  apply Neqb_ok in BC2.
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l,
          N.land_lor_distr_l, N.lor_comm, N.lor_0_l,
          N.land_lor_distr_l, N.lor_comm, N.lor_0_l in BC2.
  rewrite <- N.add_assoc.
  apply mem_ff000000_eq0 in BC2; assumption.

  replace (r0 ⊕ 1 ⊕ 1) with (r0 ⊕ 2).
  2: rewrite N.add_mod_idemp_l, <- N.add_assoc by discriminate 1;
       simpl (1+1); reflexivity.

  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  4:{ subst r2. apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  1: replace (2 ^ 32 ⊖ 0 ⊕ 2) with 2 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 2) with 1 by reflexivity.
  3: replace (2 ^ 32 ⊖ 2 ⊕ 2) with 0 by reflexivity.
  1-3: rewrite Hmod in *; subst r1; rewrite N.add_sub, N.add_0_r in R2eq.
  (* %4 = 0 *)
  rewrite N.sub_0_r in R2eq.
  1-3: subst r2; apply Neqb_ok in BC1. 
  apply mem_ff0000_eq0 in BC1; assumption.

  replace _r0 with (_r0-1+1).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l in BC1.
  rewrite <- N.add_assoc.
  apply mem_ff0000_eq0 in BC1; assumption.

  replace _r0 with (_r0-2+2).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l,
          N.land_lor_distr_l, N.lor_comm, N.lor_0_l in BC1.
  rewrite <- N.add_assoc.
  apply mem_ff0000_eq0 in BC1; assumption.

  destruct R2eq as [[Hmod R2eq]|[[Hmod R2eq]|[[Hmod R2eq]|[Hmod R2eq]]]];
  rewrite <- mod_and_3 in R0eq; replace (2^2) with 4 in R0eq by reflexivity;
  rewrite Hmod in R0eq by discriminate;
  subst r0.
  3:{ subst r2. apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  3:{ subst r2. apply Neqb_ok in BC1.
      rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l,
              N.land_lor_distr_l, N.lor_comm in BC1.
      apply N.lor_eq_0_l in BC1. inversion BC1. }
  1: replace (2 ^ 32 ⊖ 0 ⊕ 1) with 1 by reflexivity.
  2: replace (2 ^ 32 ⊖ 1 ⊕ 1) with 0 by reflexivity.
  1-2: rewrite Hmod in *; subst r1; rewrite N.add_sub in R2eq.
  (* %4 = 0 *)
  rewrite N.sub_0_r, N.add_0_r in R2eq.
  1-2: subst r2; apply Neqb_ok in BC1.
  apply mem_ff00_eq0 in BC1; assumption.

  replace _r0 with (_r0-1+1).
  2:{ rewrite N.sub_add. reflexivity. apply mod_n_le with (n:=4); [discriminate|assumption]. }
  rewrite N.land_lor_distr_l, N.lor_comm, N.lor_0_l, N.add_0_r in BC1.
  rewrite <- N.add_assoc.
  apply mem_ff00_eq0 in BC1; assumption.

  Unshelve.
  destruct PRE as [r0[R0[NF LB]]].
  step.
  unfold strlen_post.
  exists r0. split; [|split].
  rewrite update_frame by discriminate 1; assumption.
  assumption. assumption.
Qed.
