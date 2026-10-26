Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia FunctionalExtensionality.
Require Import amd64_common.
Open Scope N.

(* Specifications for the vector idioms of glibc's AVX2 string functions.
   VPCMPEQB against zero followed by VPMOVMSKB lifts to hundreds of
   expression nodes; symbolic execution of the two together exhausts memory.
   The proofs therefore cut right after each of them and carry only these
   relations across the cut.  Written by Claude Opus 5.5 (claude-opus-5-5)
   and checked by Rocq. *)

(* Byte i of x, and whether it is zero. *)
Definition byte (x i:N) := xbits x (8*i) (8*i+8).
Definition zbyte (x i:N) := byte x i =? 0.

(* y = VPCMPEQB(0, x): byte i of y is 0xff where byte i of x is 0, else 0. *)
Definition cmpz_spec (L y x:N) :=
  forall i, i < L -> byte y i = if zbyte x i then 255 else 0.

(* r = VPMOVMSKB(y) for such a y: bit j of r says whether byte j of x is 0. *)
Definition msk_spec (L r x:N) :=
  forall j, j < L -> N.testbit r j = zbyte x j.

Lemma xbits_lor: forall x y lo hi, xbits (x .| y) lo hi = xbits x lo hi .| xbits y lo hi.
Proof.
  intros. apply N.bits_inj. intro j. rewrite N.lor_spec, !xbits_spec, N.lor_spec.
  apply Bool.andb_orb_distrib_l.
Qed.

Lemma xbits_if: forall (b:bool) c lo hi, xbits (if b then c else 0) lo hi = if b then xbits c lo hi else 0.
Proof. intros [|] c lo hi; [reflexivity|]. unfold xbits. rewrite N.shiftr_0_l. reflexivity. Qed.

Lemma lor_if0_l: forall (b:bool) c y, (if b then c else 0) .| y = if b then c .| y else y.
Proof. intros [|] c y; reflexivity. Qed.

Lemma if_00: forall (b:bool), (if b then 0 else 0) = 0.
Proof. intros [|]; reflexivity. Qed.

(* byte i of a value built as an OR of guarded constants, for a concrete i *)
Ltac byte_of_or :=
  unfold byte; repeat rewrite xbits_lor; repeat rewrite xbits_if;
  repeat match goal with |- context [xbits ?c ?lo ?hi] =>
    let v := eval vm_compute in (xbits c lo hi) in change (xbits c lo hi) with v end;
  repeat rewrite if_00;
  repeat rewrite N.lor_0_l; repeat rewrite N.lor_0_r.

Lemma lt32_cases: forall i, i < 32 -> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31.
Proof. intros i I. lia. Qed.

Lemma zbyte_getmem: forall (m:memory) p L i, i < L -> zbyte (getmem 64 LittleE L m p) i = (m Ⓑ[i + p] =? 0).
Proof.
  intros m p L i I. unfold zbyte, byte. rewrite byte_of_getmem by exact I.
  rewrite getmem_mod_l, N.add_comm. reflexivity.
Qed.

(* Under cmpz_spec, bit 7 of byte j of y is whether byte j of x is zero. *)
Lemma cmpz_bit: forall L y x j, cmpz_spec L y x -> j < L -> N.testbit y (8*j+7) = zbyte x j.
Proof.
  intros L y x j C J. specialize (C j J). unfold byte in C.
  replace (N.testbit y (8*j+7)) with (N.testbit (xbits y (8*j) (8*j+8)) 7)
    by (rewrite xbits_spec; replace (7 + 8*j) with (8*j+7) by lia;
        replace (8*j+7 <? 8*j+8) with true by (symmetry; apply N.ltb_lt; lia); apply Bool.andb_true_r).
  rewrite C. destruct (zbyte x j); reflexivity.
Qed.

Lemma mod2_bits: forall x i, N.testbit (x mod 2) i = (i =? 0) && N.testbit x i.
Proof.
  intros x i. change 2 with (2^1). destruct (N.eqb_spec i 0) as [->|I].
  - rewrite N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite N.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* msk_spec for a lifted VPMOVMSKB result over a register y with cmpz_spec. *)
Ltac msk_tac C :=
  let j := fresh "j" in let J := fresh "J" in
  intros j J; rewrite <- (cmpz_bit _ _ _ j C J);
  apply lt32_cases in J; repeat destruct J as [J|J]; subst j;
  repeat (rewrite mod2_bits || bits_rewrite); cbn [N.eqb Pos.eqb andb]; bits_norm_idx; bits_cases.

(* A repeat loop whose body acts on the store as the function G. *)
Lemma rep_iter_gen:
  forall c s n w q (G: store -> store) c' s' x,
  (forall s0 c1 s1 x1, exec_stmt c s0 q c1 s1 x1 -> x1 = None /\ c1 = c /\ s1 = G s0) ->
  exec_stmt c s (Rep (Word n w) q) c' s' x -> x = None /\ c' = c /\ s' = N.iter n G s.
Proof.
  intros c s n w q G c' s' x BODY XS. inversion XS; subst. inversion E; subst. clear XS E.
  match goal with H: exec_stmt _ _ (N.iter ?k _ _) _ _ _ |- _ =>
    revert s x H; induction k as [|k IH] using N.peano_ind; intros s x XS0 end.
  - inversion XS0; subst. repeat split.
  - rewrite N.iter_succ in XS0. inversion XS0; subst.
    + match goal with H: exec_stmt c s q _ _ (Some _) |- _ => apply BODY in H; destruct H as [D _]; discriminate end.
    + match goal with H1: exec_stmt c s q _ _ None, H2: exec_stmt _ _ (N.iter _ _ _) _ _ _ |- _ =>
        destruct (BODY _ _ _ _ H1) as [_ [-> ->]]; destruct (IH _ _ H2) as [X1 [C1 S1]] end.
      subst. repeat split. rewrite N.iter_succ, <- Niter_swap. reflexivity.
Qed.

(* One step of the lifted W-bit TZCNT loop on (count, value): stop once bit 0
   is set, else count up and shift right inserting a 1 at bit W-1. *)
Definition tz_step (W:N) (ct: N * N) :=
  let (c, t) := ct in if N.testbit t 0 then (c, t) else ((c + 1) mod 2^W, (t >> 1) .| 2^(W-1)).

(* After k steps with bits 0..k-1 of x all zero, the count is k and the value
   holds x >> k below bit W-k and ones above. *)
Definition tz_inv (W x k:N) (ct: N * N) :=
  fst ct = k /\
  (forall i, i < W - k -> N.testbit (snd ct) i = N.testbit x (i + k)) /\
  (forall i, W - k <= i < W -> N.testbit (snd ct) i = true).

Lemma tz_iter_low: forall W x k, 1 <= W -> k <= W -> (forall j, j < k -> N.testbit x j = false) ->
  tz_inv W x k (N.iter k (tz_step W) (0, x)).
Proof.
  intros W x k W1. induction k as [|k IH] using N.peano_ind; intros K Z.
  - cbn. split. reflexivity. split.
    + intros i _. rewrite N.add_0_r. reflexivity.
    + intros i I. lia.
  - rewrite N.iter_succ. destruct (IH ltac:(lia) ltac:(intros; apply Z; lia)) as [C [LO HI]].
    destruct (N.iter k (tz_step W) (0, x)) as [c t]. cbn [fst snd] in C, LO, HI. subst c. cbn [tz_step].
    assert (B0: N.testbit t 0 = false).
    { destruct (N.lt_ge_cases 0 (W - k)) as [P|P].
      - rewrite (LO 0 P). apply Z. lia.
      - lia. }
    rewrite B0. split; [cbn [fst]; rewrite N.mod_small; [lia|]; pose proof (lt_pow2_lin W); lia|]. split.
    + intros i I. cbn [snd]. rewrite N.lor_spec, N.shiftr_spec'.
      rewrite (N.pow2_bits_false (W-1) i) by lia. rewrite Bool.orb_false_r.
      rewrite LO by lia. f_equal. lia.
    + intros i I. cbn [snd]. rewrite N.lor_spec, N.shiftr_spec'.
      destruct (N.eq_dec i (W-1)) as [->|NE].
      * rewrite N.pow2_bits_true. apply Bool.orb_true_r.
      * rewrite HI by lia. reflexivity.
Qed.

Lemma tz_iter_frozen: forall W n ct, N.testbit (snd ct) 0 = true -> N.iter n (tz_step W) ct = ct.
Proof.
  intros W n [c t] B. induction n as [|n IH] using N.peano_ind. reflexivity.
  rewrite N.iter_succ, IH. cbn [tz_step]. cbn in B. rewrite B. reflexivity.
Qed.

Lemma Niter_add: forall {A} (f:A -> A) p q x, N.iter (p + q) f x = N.iter p f (N.iter q f x).
Proof.
  intros A f p q x. induction p as [|p IH] using N.peano_ind. reflexivity.
  rewrite N.add_succ_l, !N.iter_succ, IH. reflexivity.
Qed.

(* The result of the lifted W-bit TZCNT loop (W+1 iterations from (0, x)). *)
Lemma tz_result: forall W x, 1 <= W -> x < 2^W ->
  let r := fst (N.iter (N.succ W) (tz_step W) (0, x)) in
  (x = 0 -> r = W) /\
  (x <> 0 -> r < W /\ N.testbit x r = true /\ forall j, j < r -> N.testbit x j = false).
Proof.
  intros W x W1 X r. split.
  - intro X0. subst x. subst r.
    destruct (tz_iter_low W 0 W W1 ltac:(lia) ltac:(intros; apply N.bits_0)) as [C [_ HI]].
    rewrite <- N.add_1_l, Niter_add.
    rewrite tz_iter_frozen. exact C. apply HI. lia.
  - intro NZ. destruct (lowest_set_bit W x X NZ) as [k [K [BK LK]]].
    destruct (tz_iter_low W x k W1 ltac:(lia) LK) as [C [LO _]].
    assert (B0: N.testbit (snd (N.iter k (tz_step W) (0, x))) 0 = true) by (rewrite LO by lia; exact BK).
    subst r. replace (N.succ W) with ((N.succ W - k) + k) by lia. rewrite Niter_add, tz_iter_frozen by exact B0.
    rewrite C. split. exact K. split. exact BK. exact LK.
Qed.

(* Two moves repeated n times (the lifted TZCNT/BSF scan loops after
   step_stmt has unfolded the Rep): the first move's value may read both
   variables, the second only its own. *)
Lemma iter_move2:
  forall c v1 v2 e1 e2 w1 w2 (F1: N -> N -> N) (F2: N -> N),
  v1 <> v2 -> c v1 = Some w1 -> c v2 = Some w2 ->
  forall_exps_in_exp not_unknown e1 -> forall_exps_in_exp not_unknown e2 ->
  (forall s, eval_exp c s e1 (F1 (s v1) (s v2)) w1) ->
  (forall s, eval_exp c s e2 (F2 (s v2)) w2) ->
  forall n s c' s' x,
  exec_stmt c s (N.iter n (Seq (Seq (Move v1 e1) (Move v2 e2))) Nop) c' s' x ->
  let G := fun p : N * N => (F1 (fst p) (snd p), F2 (snd p)) in
  x = None /\ c' = c /\ s' v1 = fst (N.iter n G (s v1, s v2)) /\ s' v2 = snd (N.iter n G (s v1, s v2)) /\
  (forall v, v <> v1 -> v <> v2 -> s' v = s v).
Proof.
  intros c v1 v2 e1 e2 w1 w2 F1 F2 NE C1 C2 NU1 NU2 EV1 EV2 n.
  induction n as [|n IH] using N.peano_ind; intros s c' s' x XS G.
  - inversion XS; subst. repeat split.
  - rewrite N.iter_succ in XS.
    assert (CU1: update c v1 (Some w1) = c)
      by (extensionality z; unfold update; destruct (z == v1); [subst; symmetry; assumption | reflexivity]).
    assert (CU2: update c v2 (Some w2) = c)
      by (extensionality z; unfold update; destruct (z == v2); [subst; symmetry; assumption | reflexivity]).
    inversion XS; subst.
    + (* the body exits: impossible, it is two moves *)
      match goal with H: exec_stmt _ _ (Seq (Move _ _) (Move _ _)) _ _ (Some _) |- _ =>
        inversion H; subst;
        repeat match goal with H': exec_stmt _ _ (Move _ _) _ _ _ |- _ => inversion H'; subst; clear H' end end;
      discriminate.
    + match goal with
        H1: exec_stmt _ _ (Seq (Move _ _) (Move _ _)) _ _ None,
        H2: exec_stmt _ _ (N.iter _ _ _) _ _ _ |- _ => rename H1 into XB; rename H2 into XR end.
      inversion XB; subst;
        try solve [ match goal with H': exec_stmt _ _ (Move _ _) _ _ (Some _) |- _ => inversion H' end ].
      match goal with
        M1: exec_stmt _ _ (Move v1 e1) _ _ None, M2: exec_stmt _ _ (Move v2 e2) _ _ _ |- _ =>
          inversion M1; subst; inversion M2; subst end.
      match goal with
        E1: eval_exp c s e1 ?n1 ?t1, E2: eval_exp _ (update s v1 ?a) e2 ?n2 ?t2 |- _ =>
          pose proof (eval_exp_deterministic NU1 E1 (EV1 s)) as D1;
          injection D1 as -> ->
      end.
      rewrite CU1 in *.
      match goal with
        E2: eval_exp c (update s v1 ?a) e2 ?n2 ?t2 |- _ =>
          pose proof (eval_exp_deterministic NU2 E2 (EV2 (update s v1 a))) as D2;
          injection D2 as -> ->
      end.
      rewrite CU2 in XR.
      destruct (IH _ _ _ _ XR) as [X1 [C1' [S1 [S2 SO]]]]. subst.
      assert (NE': v2 <> v1) by (intro EQ; apply NE; symmetry; exact EQ).
      rewrite update_updated in S1, S2. rewrite (update_frame s v1 _ v2 NE') in S1, S2.
      rewrite (update_frame _ v2 _ v1 NE), update_updated in S1, S2.
      repeat split.
      * rewrite S1, N.iter_succ, <- Niter_swap. reflexivity.
      * rewrite S2, N.iter_succ, <- Niter_swap. reflexivity.
      * intros v V1 V2. rewrite SO by assumption. rewrite !update_frame by assumption. reflexivity.
Qed.
