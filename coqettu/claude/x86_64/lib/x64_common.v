(* Shared lemmas and tactics for the amd64 libc proofs in this directory.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List FunctionalExtensionality.
Open Scope N.

Lemma testbit_shiftl_ltb:
  forall a n m, N.testbit (a << n) m = if m <? n then false else N.testbit a (m - n).
Proof.
  intros. destruct (N.ltb_spec m n).
    apply N.shiftl_spec_low. assumption.
    apply N.shiftl_spec_high'. assumption.
Qed.

Lemma testbit_const_high:
  forall c i, N.size c <= i -> N.testbit c i = false.
Proof.
  intros. destruct c as [|c]. apply N.bits_0.
  apply N.bits_above_log2. rewrite N.size_log2 in H by discriminate. lia.
Qed.

(* Rewrite N.testbit of a bitwise expression into N.testbit of its leaves. *)
Ltac bits_rewrite :=
  repeat first
    [ rewrite N.lor_spec | rewrite N.land_spec | rewrite N.lxor_spec
    | rewrite N.shiftr_spec' | rewrite testbit_shiftl_ltb | rewrite Nmod_pow2_bits
    | rewrite xbits_spec | rewrite revbytes_spec ].

(* Close a goal between boolean combinations of testbits at concrete indices. *)
(* Normalize the (closed) index of every non-constant testbit leaf. *)
Ltac bits_norm_idx :=
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      let k' := eval vm_compute in k in
      tryif constr_eq k k' then fail else change (N.testbit x k) with (N.testbit x k')
    end end.

Ltac bits_close :=
  bits_rewrite; bits_norm_idx;
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      destruct (N.testbit x k) end end;
  reflexivity.

(* Decide every comparison in the goal by case analysis + lia, then every
   remaining testbit leaf. *)
Ltac bits_cases :=
  repeat match goal with |- context [?a <? ?b] =>
    destruct (N.ltb_spec a b); try (exfalso; lia) end;
  repeat match goal with |- context [N.testbit ?c ?k] =>
    lazymatch c with Npos _ =>
      lazymatch k with Npos _ => fail | N0 => fail | _ =>
        let sz := eval vm_compute in (N.size c) in
        rewrite (testbit_const_high c k) by (change (N.size c) with sz; lia)
      end end end;
  cbn [andb orb negb];
  rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r;
  cbn [andb orb negb];
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      destruct (N.testbit x k) end end;
  cbn [andb orb negb];
  rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r;
  try reflexivity.

(* Prove an equation between two bitwise expressions of width at most w
   whose leaves are opaque numbers or constants, by checking each of the
   w bits.  Bits at and above w must be shown false by the side tactic. *)
Ltac bitblast_upto w :=
  apply N.bits_inj; let i := fresh "i" in intro i;
  let IW := fresh "IW" in
  destruct (N.lt_ge_cases i w) as [IW|IW];
  [ let rec go k :=
      lazymatch eval compute in (k <? w) with
      | true => destruct (N.eq_dec i k) as [->|?];
                [ bits_close | let k1 := eval compute in (N.succ k) in go k1 ]
      | false => exfalso; lia
      end in go 0
  | bits_rewrite; bits_cases ].

Lemma toZ32_range: forall n, Z.le (-2^31) (toZ 32 n) /\ Z.lt (toZ 32 n) (2^31).
Proof. intro n. apply (canonicalZ_bounds 32). Qed.

Lemma toZ64_range: forall n, Z.le (-2^63) (toZ 64 n) /\ Z.lt (toZ 64 n) (2^63).
Proof. intro n. apply (canonicalZ_bounds 64). Qed.

Lemma quot_range:
  forall (n d m:Z), (0 < m)%Z -> (-m <= n < m)%Z -> (-m <= d < m)%Z -> d <> 0%Z ->
  ~ (n = -m /\ d = -1)%Z -> (-m <= Z.quot n d < m)%Z.
Proof.
  intros n d m M RN RD DNZ NOVF.
  destruct (Z.eq_dec d 1) as [->|D1]. rewrite Z.quot_1_r. lia.
  destruct (Z.eq_dec d (-1)) as [->|D2].
    pose proof (Z.quot_opp_r n 1 ltac:(lia)) as Q. simpl (Z.opp 1) in Q. rewrite Q, Z.quot_1_r. lia.
  assert (A: (Z.abs (Z.quot n d) <= Z.abs n / 2)%Z).
    rewrite <- Z.quot_abs, Z.quot_div_nonneg by lia.
    apply Z.div_le_compat_l; lia.
  assert (B: (Z.abs n / 2 <= m / 2)%Z) by (apply Z.div_le_mono; lia).
  assert (C: (m / 2 < m)%Z) by (apply Z.div_lt; lia).
  lia.
Qed.

Lemma rem_range:
  forall (n d m:Z), (-m <= d < m)%Z -> d <> 0%Z -> (-m <= Z.rem n d < m)%Z.
Proof.
  intros. pose proof (Z.rem_bound_abs n d H0). lia.
Qed.

(* Reassembling a 2w-bit value from its high and low halves. *)
Lemma recombine:
  forall w w2 s x, w2 = 2*w -> s < 2^w2 -> s mod 2^w = x ->
  ((s >> w) mod 2^w << w) mod 2^w2 .| x = s.
Proof.
  intros w w2 s x W2 LT <-. subst w2. apply N.bits_inj. intro i.
  rewrite N.lor_spec, !Nmod_pow2_bits, testbit_shiftl_ltb.
  destruct (N.ltb_spec i w); destruct (N.ltb_spec i (2*w)); cbn [andb orb].
    reflexivity.
    lia.
    rewrite Nmod_pow2_bits, N.shiftr_spec', N.sub_add by assumption.
      replace (i - w <? w) with true by (symmetry; apply N.ltb_lt; lia).
      apply Bool.orb_false_r.
    rewrite <- (N.mod_small s (2^(2*w))) by assumption. rewrite Nmod_pow2_bits.
      replace (i <? 2*w) with false by (symmetry; apply N.ltb_ge; lia). reflexivity.
Qed.

(* The high half of a value packed as (hi << w) .| lo. *)
Lemma packed_hi:
  forall w w2 hi lo, w2 = 2*w -> lo < 2^w ->
  ((hi << w) .| lo) mod 2^w2 >> w = hi mod 2^w.
Proof.
  intros w w2 hi lo W2 LT. subst w2. apply N.bits_inj. intro i.
  rewrite N.shiftr_spec', Nmod_pow2_bits, N.lor_spec, testbit_shiftl_ltb, Nmod_pow2_bits.
  replace (i + w <? w) with false by (symmetry; apply N.ltb_ge; lia).
  rewrite N.add_sub.
  replace (N.testbit lo (i + w)) with false.
    rewrite Bool.orb_false_r. f_equal. destruct (N.ltb_spec (i+w) (2*w)), (N.ltb_spec i w); lia.
  symmetry. rewrite <- (N.mod_small lo (2^w)) by assumption. rewrite Nmod_pow2_bits.
  replace (i + w <? w) with false by (symmetry; apply N.ltb_ge; lia). reflexivity.
Qed.

Lemma ofZ_mod_narrow:
  forall w w' z, w' <= w -> ofZ w z mod 2^w' = ofZ w' z.
Proof.
  intros. rewrite <- ofZ_N2Z.
  replace (Z.of_N (ofZ w z)) with (z mod 2^Z.of_N w)%Z.
    apply ofZ_mod_pow2. assumption.
  unfold ofZ. rewrite Z2N.id. reflexivity.
  apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
Qed.

Lemma scast_low: forall w w' x, w <= w' -> scast w w' x mod 2^w = x mod 2^w.
Proof.
  intros. unfold scast. rewrite ofZ_mod_narrow by assumption.
  apply ofZ_toZ_bitcast. reflexivity.
Qed.

Lemma toZ_scast: forall w w' x, 0 < w -> w <= w' -> toZ w' (scast w w' x) = toZ w x.
Proof.
  intros. unfold scast. rewrite toZ_ofZ_canonicalZ by reflexivity.
  apply (canonicalZ_id w). lia.
  apply canonicalZ_bounds.
Qed.

(* Splitting a 16-byte non-overlap into its two 8-byte halves. *)
Lemma noverlap16_lo:
  forall a b len, ~ overlap 64 a 16 b len -> ~ overlap 64 a 8 b len.
Proof.
  intros a b len NO [i [j [I [J EQ]]]]. apply NO. exists i, j. split; [lia | split; [exact J | exact EQ]].
Qed.

Lemma noverlap16_hi:
  forall a b len, ~ overlap 64 a 16 b len -> ~ overlap 64 (a ⊕ 8) 8 b len.
Proof.
  intros a b len NO [i [j [I [J EQ]]]]. apply NO. exists (8+i), j.
  split; [lia | split; [exact J |]].
  rewrite <- EQ, mp2_add_l, N.add_assoc, (N.add_comm a 8). reflexivity.
Qed.

Lemma noverlap_sym:
  forall w a1 len1 a2 len2, ~ overlap w a1 len1 a2 len2 -> ~ overlap w a2 len2 a1 len1.
Proof.
  intros w a1 len1 a2 len2 NO [i [j [I [J EQ]]]]. apply NO. exists j, i. auto.
Qed.

(* Simplify reads through a stack of writes, using getmem_setmem for a read
   of the address just written and getmem_noverlap (with a non-overlap fact
   from the context) otherwise. *)
Ltac getmem_simpl :=
  repeat first
    [ rewrite getmem_setmem by discriminate
    | rewrite getmem_noverlap by (assumption || (apply noverlap_sym; assumption)) ];
  repeat match goal with |- context [?v mod 2^(?l*8)] =>
    let w := eval compute in (l*8) in change (2^(l*8)) with (2^w) end.

(* Flags of CMP x,1 as tested by JLE, and their signed meaning. *)
Lemma shiftr63: forall y, y < 2^64 -> y >> 63 = if y <? 2^63 then 0 else 1.
Proof.
  intros. rewrite N.shiftr_div_pow2. destruct (N.ltb_spec y (2^63)).
    apply N.div_small. assumption.
    apply N.le_antisymm.
      apply N.lt_succ_r, N.div_lt_upper_bound. discriminate. change (2^63 * N.succ 1) with (2^64). assumption.
      apply N.div_le_lower_bound. discriminate. rewrite N.mul_1_r. assumption.
Qed.

Lemma slt64_0: forall y, y < 2^64 -> slt 64 y 0 = negb (y <? 2^63).
Proof.
  intros. unfold slt. change (toZ 64 0) with 0%Z.
  destruct (N.ltb_spec y (2^63)).
    rewrite (proj1 (toZ_nonneg 64 y)) by (rewrite N.mod_small; assumption).
    apply Z.ltb_ge. lia.
    apply Z.ltb_lt. apply Z.nle_gt. intro H1. apply toZ_sign in H1.
    rewrite N.mod_small in H1 by assumption. simpl in H1. lia.
Qed.

Lemma toZ64_le1: forall x, x < 2^64 ->
  Z.leb (toZ 64 x) 1 = orb (x <? 2) (2^63 <=? x).
Proof.
  intros. destruct (N.ltb_spec x (2^63)).
    rewrite (proj1 (toZ_nonneg 64 x)) by (rewrite N.mod_small; assumption).
    rewrite N.mod_small by assumption.
    destruct (N.ltb_spec x 2), (N.leb_spec (2^63) x), (Z.leb_spec (Z.of_N x) 1); simpl; lia.
    assert (NEG: Z.lt (toZ 64 x) 0).
      apply Z.nle_gt. intro H1. apply toZ_sign in H1. rewrite N.mod_small in H1 by assumption. simpl in H1. lia.
    destruct (Z.leb_spec (toZ 64 x) 1); [|lia].
    destruct (N.leb_spec (2^63) x); [|lia]. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma cmp1_jle:
  forall x, x < 2^64 ->
  (if x =? 1 then 1 else 0)
  .| (if negb (((x >> 63) .^ (x ⊖ 1 >> 63)) .& ((x ⊖ 1 >> 63) .^ 1) =?
               (if slt 64 (x ⊖ 1) 0 then 1 else 0)) then 1 else 0)
  = if Z.leb (toZ 64 x) 1 then 1 else 0.
Proof.
  intros x LT. rewrite toZ64_le1 by assumption.
  assert (M: x ⊖ 1 = if x =? 0 then 2^64 - 1 else x - 1).
    unfold msub. destruct (N.eqb_spec x 0) as [->|NZ]. reflexivity.
    change (1 mod 2^64) with 1. rewrite N.add_sub_assoc by (change 1 with (2^0); apply N.pow_le_mono_r; discriminate).
    replace (x + 2^64 - 1) with (x - 1 + 1 * 2^64) by lia. rewrite N.mod_add, N.mod_small by (discriminate || lia). reflexivity.
  assert (ML: x ⊖ 1 < 2^64) by apply msub_lt.
  rewrite slt64_0, !shiftr63 by assumption. rewrite M in *.
  destruct (N.eqb_spec x 0) as [->|NZ]. reflexivity.
  destruct (N.eqb_spec x 1) as [->|N1]. reflexivity.
  destruct (N.ltb_spec x (2^63)) as [A|A];
  destruct (N.ltb_spec (x - 1) (2^63)) as [B|B];
  destruct (N.ltb_spec x 2), (N.leb_spec (2^63) x); try lia; reflexivity.
Qed.

(* Modular address arithmetic and single-byte memory access. *)
Lemma msub_add_l: forall a b x, x < 2^64 -> a mod 2^64 = (b + x) mod 2^64 -> msub 64 a b = x.
Proof.
  intros a b x LT EQ. unfold msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Lemma getmem1_setmem1:
  forall m a b v,
  (setmem 64 LittleE 1 m b v) Ⓑ[a] = if a mod 2^64 =? b mod 2^64 then v mod 2^8 else m Ⓑ[a].
Proof.
  intros. destruct (N.eqb_spec (a mod 2^64) (b mod 2^64)) as [E|NE].
    rewrite <- (getmem_mod_l _ _ _ _ a), E, getmem_mod_l, getmem_setmem; reflexivity + discriminate.
    apply getmem_noverlap. intros [i [j [I [J EQ]]]].
    apply NE. replace i with 0 in EQ by lia. replace j with 0 in EQ by lia.
    rewrite !N.add_0_r in EQ. exact EQ.
Qed.


(* ---------------------------------------------------------------------------
   Reasoning about the bounded loops (Rep) that pcode2coq emits for bit-scan
   instructions (BSF/BSR/TZCNT/LZCNT).
   --------------------------------------------------------------------------- *)

Lemma update_id {A B} {_: EqDec A}: forall (s:A->B) x, update s x (s x) = s.
Proof.
  intros. extensionality z. unfold update. destruct (z == x). subst. reflexivity. reflexivity.
Qed.

(* A repeat-loop whose body is a single assignment v := e, where e's value
   depends on v only through a function F, computes N.iter n F. *)
Lemma rep_move_iter:
  forall c s n w v e wv F c' s' x
    (CV: c v = Some wv) (NU: forall_exps_in_exp not_unknown e)
    (EV: forall t, eval_exp c (update s v t) e (F t) wv)
    (XS: exec_stmt c s (Rep (Word n w) (Move v e)) c' s' x),
  x = None /\ c' = c /\ s' = update s v (N.iter n F (s v)).
Proof.
  intros. inversion XS; subst. inversion E; subst. clear XS E.
  revert s x XS0 EV. induction n0 as [|k IH] using N.peano_ind; intros s x XS0 EV.
  - inversion XS0; subst. simpl. rewrite update_id. repeat split.
  - rewrite N.iter_succ in XS0. inversion XS0; subst;
      match goal with H: exec_stmt _ _ (Move _ _) _ _ _ |- _ => inversion H; subst end.
    match goal with
      H1: eval_exp c s e ?n1 ?w1, H2: exec_stmt _ _ (N.iter _ _ _) _ _ _ |- _ =>
        rename H1 into E0; rename H2 into XS2 end.
    assert (E1 := EV (s v)). rewrite update_id in E1.
    assert (EQ := eval_exp_deterministic NU E1 E0). injection EQ as <- <-.
    replace (update c v (Some wv)) with c in XS2 by
      (extensionality z; unfold update; destruct (z == v); [subst; assumption | reflexivity]).
    destruct (IH (update s v (F (s v))) x XS2) as [X1 [C1 S1]].
      intro t. rewrite update_cancel. apply EV.
    subst. repeat split.
    rewrite update_cancel, update_updated, Niter_swap, N.iter_succ. reflexivity.
Qed.

Lemma exec_seq_none:
  forall c s q1 q2 c' s' x
    (XS: exec_stmt c s (Seq q1 q2) c' s' x)
    (NX: forall c1 s1 x1, exec_stmt c s q1 c1 s1 x1 -> x1 = None),
  exists c1 s1, exec_stmt c s q1 c1 s1 None /\ exec_stmt c1 s1 q2 c' s' x.
Proof.
  intros. inversion XS; subst.
    apply NX in XS0. discriminate.
    exists c2, s2. split; assumption.
Qed.

Lemma eval_exp_eq:
  forall c s e n n' w, eval_exp c s e n w -> n = n' -> eval_exp c s e n' w.
Proof. intros. subst. assumption. Qed.

(* Build an eval_exp derivation for a concrete expression, leaving the value
   to be computed. *)
Ltac eval_exp_build :=
  repeat first
    [ reflexivity
    | lazymatch goal with |- eval_exp _ _ (BinOp ?b _ _) _ ?w =>
        lazymatch b with OP_EQ => fail | OP_NEQ => fail | OP_LT => fail | OP_LE => fail
        | OP_SLT => fail | OP_SLE => fail | _ =>
          tryif is_evar w then fail else
          change w with (widthof_binop b w); econstructor end end
    | econstructor ].

Lemma shiftr_land1: forall x t, (x >> t) .& 1 = N.b2n (N.testbit x t).
Proof.
  intros. change 1 with (N.ones 1) at 1. rewrite N.land_ones, N.shiftr_div_pow2.
  symmetry. apply N.testbit_spec'.
Qed.


(* Every nonzero number below 2^n has a least set bit, below n. *)
Lemma lowest_set_bit:
  forall n x, x < 2^n -> x <> 0 ->
  exists k, k < n /\ N.testbit x k = true /\ forall j, j < k -> N.testbit x j = false.
Proof.
  induction n as [|n IH] using N.peano_ind; intros x LT NZ.
    change (2^0) with 1 in LT. lia.
  destruct (N.testbit x 0) eqn:B0.
    exists 0. split; [lia | split; [assumption | intros; lia]].
  assert (H2: x = 2 * N.div2 x).
    pose proof (N.div2_odd x) as D. rewrite <- N.bit0_odd, B0 in D. simpl N.b2n in D. lia.
  destruct (IH (N.div2 x)) as [k [K [BK LK]]].
    rewrite N.pow_succ_r' in LT. lia.
    intro D. rewrite D in H2. lia.
  rewrite N.div2_div in BK, LK.
  exists (N.succ k). repeat split.
    lia.
    rewrite <- N.div2_bits. exact BK.
    intros j J. destruct (N.eq_dec j 0) as [->|NZj]. exact B0.
      replace j with (N.succ (N.pred j)) by lia. rewrite <- N.div2_bits. apply LK. lia.
Qed.

(* The bit-scan iteration of Ghidra's BSF finds the least set bit. *)
Lemma bsf_iter:
  forall w x, 0 < w -> x < 2^w -> x <> 0 ->
  let F := fun t => if N.testbit x t then t else (t+1) mod 2^w in
  let k := N.iter (N.succ w) F 0 in
  k < w /\ N.testbit x k = true /\ forall j, j < k -> N.testbit x j = false.
Proof.
  intros w x W LT NZ F k.
  destruct (lowest_set_bit w x LT NZ) as [k0 [K0 [B0 L0]]].
  assert (IT: forall m, N.iter m F 0 = N.min m k0).
    induction m as [|m IHm] using N.peano_ind. simpl. symmetry. apply N.min_0_l.
    rewrite N.iter_succ, IHm. unfold F.
    destruct (N.lt_ge_cases m k0) as [M|M].
      rewrite N.min_l by lia. rewrite L0 by assumption.
      rewrite N.mod_small. lia.
      apply N.le_lt_trans with k0. lia. eapply N.lt_trans. eassumption.
      apply N.pow_gt_lin_r. reflexivity.
      rewrite N.min_r by lia. rewrite B0. lia.
  subst k. rewrite IT, N.min_r by lia. repeat split; assumption.
Qed.

(* glibc's encoding of dev_t (see amd64_gnu_dev_*_proof.v). *)
Definition dev_make (maj min:N) :=
  (min .& 0xff) .| ((maj .& 0xfff) << 8) .| ((min .& 0xffffff00) << 12) .|
  ((maj .& 0xfffff000) << 32).
Definition dev_major (dev:N) := ((dev >> 8) .& 0xfff) .| ((dev >> 32) .& 0xfffff000).
Definition dev_minor (dev:N) := (dev .& 0xff) .| ((dev >> 12) .& 0xffffff00).

Theorem dev_major_make:
  forall maj min, dev_major (dev_make maj min) = maj mod 2^32.
Proof. intros. unfold dev_major, dev_make. bitblast_upto 32. Qed.

Theorem dev_minor_make:
  forall maj min, dev_minor (dev_make maj min) = min mod 2^32.
Proof. intros. unfold dev_minor, dev_make. bitblast_upto 32. Qed.

(* IPv4 classful decomposition (see amd64_inet_netof_proof.v and
   amd64_inet_lnaof_proof.v).  ntohl32 is network-to-host byte order. *)
Definition ntohl32 (x:N) :=
  (xbits x 0 8 << 24) .| (xbits x 8 16 << 16) .| (xbits x 16 24 << 8) .| xbits x 24 32.
Definition is_classA (a:N) := a .& 0x80000000 =? 0.
Definition is_classB (a:N) := a .& 0xc0000000 =? 0x80000000.
Definition inet_net (a:N) :=
  if is_classA a then a >> 24 else if is_classB a then a >> 16 else a >> 8.
Definition inet_lna (a:N) :=
  if is_classA a then a .& 0xffffff else if is_classB a then a .& 0xffff else a .& 0xff.

(* Sign bit / bit 31 facts for 32-bit values. *)
Lemma land_mod32: forall a m, m < 2^32 -> (a mod 2^32) .& m = a .& m.
Proof.
  intros a m LT. rewrite <- (N.land_ones a 32).
  replace m with (m .& N.ones 32) at 2.
    rewrite <- N.land_assoc, (N.land_comm (N.ones 32) m). reflexivity.
  rewrite N.land_ones. apply N.mod_small. assumption.
Qed.

Lemma land_bit31: forall y, y .& 0x80000000 = if N.testbit y 31 then 2^31 else 0.
Proof.
  intro y. change 0x80000000 with (2^31). apply N.bits_inj. intro i.
  rewrite N.land_spec, N.pow2_bits_eqb.
  destruct (N.eqb_spec 31 i) as [<-|NE]; destruct (N.testbit y 31) eqn:B.
    reflexivity. reflexivity.
    rewrite N.pow2_bits_eqb, (proj2 (N.eqb_neq _ _) NE). apply Bool.andb_false_r.
    rewrite N.bits_0. apply Bool.andb_false_r.
Qed.

Lemma testbit31_ge: forall y, y < 2^32 -> N.testbit y 31 = (2^31 <=? y).
Proof.
  intros y LT. rewrite N.testbit_odd, N.shiftr_div_pow2.
  destruct (N.leb_spec (2^31) y).
    replace (y / 2^31) with 1. reflexivity.
    symmetry. apply N.le_antisymm.
      apply N.lt_succ_r, N.div_lt_upper_bound. discriminate. assumption.
      apply N.div_le_lower_bound. discriminate. lia.
    rewrite N.div_small by assumption. reflexivity.
Qed.

Lemma slt32_0: forall y, y < 2^32 -> slt 32 y 0 = N.testbit y 31.
Proof.
  intros y LT. rewrite testbit31_ge by assumption.
  unfold slt. change (toZ 32 0) with 0%Z.
  destruct (N.leb_spec (2^31) y).
    apply Z.ltb_lt. apply Z.nle_gt. intro H1. apply toZ_sign in H1.
    rewrite N.mod_small in H1 by assumption. simpl in H1. lia.
    rewrite (proj1 (toZ_nonneg 32 y)) by (rewrite N.mod_small; assumption).
    apply Z.ltb_ge. lia.
Qed.

(* The form psimpl gives BSWAP of a 32-bit register. *)
Lemma bswap_ntohl:
  forall r, ((r .& 4278190080) >> 24 .| (r .& 16711680) >> 8 .| (r .& 65280) << 8 .| r << 24)
            mod 2^32 = ntohl32 (r mod 2^32).
Proof. intro r. unfold ntohl32. bitblast_upto 32. Qed.

Lemma bswap_land:
  forall r m, m < 2^32 ->
  ((r .& 4278190080) >> 24 .| (r .& 16711680) >> 8 .| (r .& 65280) << 8 .| r << 24) .& m =
  ntohl32 (r mod 2^32) .& m.
Proof. intros r m LT. rewrite <- bswap_ntohl, land_mod32 by assumption. reflexivity. Qed.

Lemma ntohl32_mod: forall x, ntohl32 x mod 2^32 = ntohl32 x.
Proof. intro x. unfold ntohl32. bitblast_upto 32. Qed.

Lemma ntohl32_lt: forall x, ntohl32 x < 2^32.
Proof. intro x. rewrite <- ntohl32_mod. apply mp2_mod_lt. Qed.

Lemma ifb31_eqb0: forall b:bool, ((if b then 2^31 else 0) =? 0) = negb b.
Proof. destruct b; reflexivity. Qed.

Lemma land_mod_pow2: forall a k m, m < 2^k -> (a mod 2^k) .& m = a .& m.
Proof.
  intros a k m LT. rewrite <- (N.land_ones a k).
  replace m with (m .& N.ones k) at 2.
    rewrite <- N.land_assoc, (N.land_comm (N.ones k) m). reflexivity.
  rewrite N.land_ones. apply N.mod_small. assumption.
Qed.

(* psimpl narrows a 4-byte load to 2 bytes when only the low bits are used. *)
Lemma getmem_dw_w: forall (m:memory) a, m Ⓦ[a] = m Ⓓ[a] mod 2^16.
Proof. intros. rewrite (getmem_mod 64 LittleE 2 4). reflexivity. Qed.

(* ---------------------------------------------------------------------------
   Byte-scanning loops (the __str*_c1/_c2 helpers and similar).
   --------------------------------------------------------------------------- *)

(* MOVSX of a byte to 32 bits: signed char promoted to int. *)
Definition sx (b:N) := scast 8 32 b.

Lemma sx_mod: forall b, sx b mod 2^32 = sx b.
Proof. intro. apply N.mod_small, ofZ_bound. Qed.

Lemma sx_low8: forall b, b < 2^8 -> sx b mod 2^8 = b.
Proof. intros. unfold sx. rewrite scast_low by discriminate. apply N.mod_small. assumption. Qed.

Lemma byte_addr: forall (m:memory) p r, m Ⓑ[p + r] = m Ⓑ[p ⊕ r].
Proof. intros. symmetry. apply getmem_mod_l. Qed.

Lemma byte_addr_succ: forall (m:memory) p r, m Ⓑ[1 + p + r] = m Ⓑ[p ⊕ (1 ⊕ r)].
Proof.
  intros. rewrite <- (getmem_mod_l _ _ _ _ (1 + p + r)). f_equal.
  change (2^64) with 18446744073709551616. lia.
Qed.

Lemma succ_le: forall r, 1 ⊕ r <= r + 1.
Proof. intro. rewrite N.add_comm. apply mp2_mod_le. Qed.

Lemma mul1_mod: forall j, j < 2^64 -> j ⊗ 1 = j.
Proof. intros. rewrite N.mul_1_r. apply N.mod_small. assumption. Qed.

(* Turn a branch condition comparing a sign-extended byte with an argument
   register into a Prop. *)
Ltac norm_byte_bc H :=
  try rewrite mul1_mod in H by apply mp2_mod_lt;
  repeat match type of H with context [scast 8 32 ?b] => fold (sx b) in H end;
  rewrite ?sx_mod in H;
  first [ apply N.eqb_eq in H | apply N.eqb_neq in H | idtac ].

(* Reflexivity only when both sides are syntactically identical.  Plain
   reflexivity on terms that differ syntactically can trigger very expensive
   conversion checks, e.g. on bit expressions over opaque values. *)
Ltac sreflexivity := match goal with |- ?a = ?a => reflexivity end.

(* Single-bit masks and small sign-extensions. *)
Lemma pow2_land_eqb0: forall k w, (2^k .& w =? 0) = negb (N.testbit w k).
Proof.
  intros. destruct (N.testbit w k) eqn:B.
    apply N.eqb_neq. intro Z. assert (H := f_equal (fun z => N.testbit z k) Z). cbv beta in H.
      rewrite N.land_spec, N.pow2_bits_true, B, N.bits_0 in H. discriminate.
    apply N.eqb_eq. apply N.bits_inj_0. intro i. rewrite N.land_spec, N.pow2_bits_eqb.
      destruct (N.eqb_spec k i). subst. rewrite B. reflexivity. reflexivity.
Qed.

Lemma scast_32_64_small: forall y, y < 2^31 -> scast 32 64 y = y.
Proof.
  intros. unfold scast. rewrite (proj1 (toZ_nonneg 32 y)).
    rewrite ofZ_N2Z, !N.mod_small. reflexivity.
    change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in H. lia.
    change (2^32) with 4294967296. change (2^31) with 2147483648 in H. lia.
    rewrite N.mod_small. assumption. change (2^32) with 4294967296. change (2^31) with 2147483648 in H. lia.
Qed.


(* A sub-range of a region that doesn't overlap b doesn't overlap b either. *)
Lemma noverlap_sub:
  forall a la b lb o l, ~ overlap 64 a la b lb -> o + l <= la ->
  ~ overlap 64 (a ⊕ o) l b lb.
Proof.
  intros a la b lb o l NO LE [i [j [I [J EQ]]]]. apply NO. exists (o + i), j.
  split; [lia|]. split; [exact J|]. rewrite <- EQ, mp2_add_l, N.add_assoc. reflexivity.
Qed.

Lemma noverlap_sub0:
  forall a la b lb l, ~ overlap 64 a la b lb -> l <= la -> ~ overlap 64 a l b lb.
Proof.
  intros a la b lb l NO LE [i [j [I [J EQ]]]]. apply NO. exists i, j. split; [lia|]. split; [exact J|exact EQ].
Qed.

(* Bits below 32 of 64-bit arithmetic (IMUL r32 etc.). *)
Lemma shiftr_mask_low32:
  forall X k mask, k <= 32 -> mask < 2^(32-k) -> (X >> k) .& mask = ((X mod 2^32) >> k) .& mask.
Proof.
  intros X k mask K M. apply N.bits_inj. intro i.
  rewrite !N.land_spec, !N.shiftr_spec', Nmod_pow2_bits.
  destruct (N.ltb_spec (i + k) 32). reflexivity.
  replace (N.testbit mask i) with false. rewrite !Bool.andb_false_r. reflexivity.
  symmetry. rewrite <- (N.mod_small mask (2^(32-k))) by exact M. rewrite Nmod_pow2_bits.
  replace (i <? 32 - k) with false by (symmetry; apply N.ltb_ge; lia). reflexivity.
Qed.

Lemma shiftr_mod_low32:
  forall X k j, k + j <= 32 -> (X >> k) mod 2^j = ((X mod 2^32) >> k) mod 2^j.
Proof.
  intros X k j K. apply N.bits_inj. intro i.
  rewrite !Nmod_pow2_bits, !N.shiftr_spec', Nmod_pow2_bits.
  destruct (N.ltb_spec i j). replace (i + k <? 32) with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
  reflexivity.
Qed.

Lemma imul32_low:
  forall a c d, (d + scast 32 64 a * c) mod 2^32 = (a * c + d) mod 2^32.
Proof.
  intros. rewrite N.add_comm, <- mp2_add_l, <- mp2_mul_l, scast_low, mp2_mul_l, mp2_add_l by discriminate.
  reflexivity.
Qed.

(* Byte k of a little-endian load is the byte at offset k. *)
Lemma byte_of_getmem:
  forall (m:memory) s L k, k < L ->
  xbits (getmem 64 LittleE L m s) (8*k) (8*k+8) = m Ⓑ[s ⊕ k].
Proof.
  intros m s L k K. apply N.bits_inj. intro j.
  rewrite xbits_spec, !getmem_spec.
  destruct (N.ltb_spec (j + 8*k) (8*k+8)) as [J|J].
  - replace (j + 8*k <? L*8) with true by (symmetry; apply N.ltb_lt; lia).
    replace (j <? 1*8) with true by (symmetry; apply N.ltb_lt; lia).
    rewrite Bool.andb_true_r, Bool.andb_true_l.
    rewrite Bool.andb_true_l. f_equal. change (2^64*8) with 147573952589676412928. change (2^64) with 18446744073709551616. lia.
  - rewrite Bool.andb_false_r.
    replace (j <? 1*8) with false by (symmetry; apply N.ltb_ge; lia). reflexivity.
Qed.

(* Reading a byte after a store: either the stored byte or the old one. *)
Lemma byte_setmem_cases:
  forall (m:memory) a L v b, 0 < L -> L <= 2^64 ->
  (setmem 64 LittleE L m a v) Ⓑ[b] =
  if msub 64 b a <? L then xbits v (8 * msub 64 b a) (8 * msub 64 b a + 8) else m Ⓑ[b].
Proof.
  intros m a L v b L0 LL. destruct (N.ltb_spec (msub 64 b a) L) as [I|I].
  - set (i := msub 64 b a) in *.
    assert (B: b mod 2^64 = (a + i) mod 2^64) by (subst i; unfold msub; change (2^64) with 18446744073709551616 in *; lia).
    rewrite <- getmem_mod_l, B, getmem_mod_l.
    replace L with (i + 1 + (L - i - 1)) at 1 by lia.
    rewrite getmem_setmem_xbits by lia. f_equal; lia.
  - apply getmem_noverlap. intros [i [j [Ii [Jj E]]]].
    assert (i = 0) by lia. subst i. rewrite N.add_0_r in E.
    assert (msub 64 b a = j) by (unfold msub; change (2^64) with 18446744073709551616 in *; lia). lia.
Qed.
