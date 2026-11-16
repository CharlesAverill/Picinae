(* Bit identities shared by the Codex i386 proofs. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith ZArith Lia.
Import X86Notations.
Open Scope N.

Lemma lt_eq_word : forall x y,
  N.lor (if x <? y then 1 else 0) (if x =? y then 1 else 0) =
  (if x <=? y then 1 else 0).
Proof.
  intros x y.
  destruct (x <? y) eqn:L; destruct (x =? y) eqn:E;
    destruct (x <=? y) eqn:LE; try reflexivity;
    csimpl; lia.
Qed.

Lemma classify_interval : forall x lo hi,
  x < 2^32 -> lo <= hi -> hi < 2^32 ->
  N.lor (if msub 32 x lo <? hi-lo then 1 else 0)
        (if x =? hi then 1 else 0) =
  (if (lo <=? x) && (x <=? hi) then 1 else 0).
Proof.
  intros x lo hi XB LH HB.
  assert (LB : lo < 2^32) by lia.
  assert (TEST : msub 32 x lo < hi-lo <-> lo <= x /\ x < hi).
  { rewrite <- msub_lt_iff.
    rewrite (N.mod_small x (2^32) XB), (N.mod_small lo (2^32) LB).
    lia. }
  destruct TEST as [FORWARD BACKWARD].
  destruct (msub 32 x lo <? hi-lo) eqn:T;
    destruct (x =? hi) eqn:E;
    destruct (lo <=? x) eqn:L;
    destruct (x <=? hi) eqn:H; try reflexivity; csimpl;
    exfalso; try solve [destruct (FORWARD T); lia |
      apply (N.le_ngt _ _ T), BACKWARD; lia | lia].
Qed.

Ltac solve_loaded_word_bits :=
  let i := fresh "i" in let LO := fresh "LO" in
  let HI := fresh "HI" in let CASES := fresh "CASES" in
  apply N.bits_inj; intro i;
  destruct (N.lt_ge_cases i 32) as [LO | HI];
  [ assert (CASES : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
          i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
          i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
          i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/
          i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/
          i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/
          i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/
          i = 28 \/ i = 29 \/ i = 30 \/ i = 31)
        by (clear - LO; lia);
      repeat destruct CASES as [CASES | CASES]; subst i;
        repeat first [rewrite N.lor_spec | rewrite N.land_spec |
          rewrite N.shiftr_spec' | rewrite Nshiftl_spec |
          rewrite revbytes_spec | rewrite getmem_spec];
        cbn; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r,
          ?Bool.orb_false_r, ?Bool.orb_false_l; reflexivity
  | solve bits inj ].

Lemma bswap_load32 : forall m a,
  N.lor
    (N.lor
      (N.lor (N.shiftr (N.land (getmem 32 LittleE 4 m a) 4278190080) 24)
             (N.shiftr (N.land (getmem 32 LittleE 3 m a) 16711680) 8))
      (N.shiftl (N.land (getmem 32 LittleE 2 m a) 65280) 8))
    (N.shiftl (getmem 32 LittleE 1 m a) 24) =
  revbytes (getmem 32 LittleE 4 m a) 4.
Proof.
  intros m a. solve_loaded_word_bits.
Qed.

Lemma bswap_load16 : forall m a,
  N.lor
    (N.lor (N.shiftl (getmem 32 LittleE 1 m a) 8)
           (N.shiftr (getmem 32 LittleE 2 m a) 8))
    (N.land (getmem 32 LittleE 4 m a) 4294901760) =
  revbytes (getmem 32 LittleE 4 m a) 2.
Proof. intros m a. solve_loaded_word_bits. Qed.

Lemma cdq_sign : forall x, x < 2^32 ->
  N.shiftr (scast 32 64 x) 32 =
  if x <? 2^31 then 0 else 4294967295.
Proof.
  intros x XB. rewrite N.shiftr_div_pow2.
  unfold scast, ofZ, toZ, canonicalZ.
  destruct (x <? 2^31) eqn:SIGN; csimpl;
    apply N2Z.inj; rewrite N2Z.inj_div, Z2N.id
      by (apply Z.mod_pos_bound; reflexivity);
    cbn in *; lia.
Qed.

Lemma abs_branchless : forall x, x < 2^32 ->
  msub 32 (N.lxor x (N.shiftr (scast 32 64 x) 32))
    (N.shiftr (scast 32 64 x) 32) =
  if x <? 2^31 then x else 2^32-x.
Proof.
  intros x XB. rewrite (cdq_sign x XB).
  destruct (x <? 2^31) eqn:SIGN.
  - rewrite N.lxor_0_r, msub_0_r. apply N.mod_small, XB.
  - change 4294967295 with (N.ones 32).
    change (N.lxor x (N.ones 32)) with (N.lnot x 32).
    rewrite lnot_sub_low2 by exact XB.
    apply N.ltb_ge in SIGN.
    unfold msub. change (((4294967295-x)+1) mod 4294967296 = 4294967296-x).
    rewrite N.mod_small by lia. lia.
Qed.

Lemma toZ32_small : forall x, x < 2^31 -> toZ 32 x = Z.of_N x.
Proof.
  intros x X.
  assert (B : x < 2^32) by lia.
  pose proof (proj1 (toZ_nonneg 32 x)) as T.
  rewrite (N.mod_small x (2^32) B) in T. apply T. exact X.
Qed.

Lemma abs_word_signed : forall x, x < 2^32 -> x <> 2^31 ->
  toZ 32 (if x <? 2^31 then x else 2^32-x) = Z.abs (toZ 32 x).
Proof.
  intros x XB MIN. destruct (x <? 2^31) eqn:SIGN; csimpl.
  - rewrite (toZ32_small x SIGN), Z.abs_eq; [reflexivity|apply N2Z.is_nonneg].
  - assert (D : 2^32-x < 2^31) by lia.
    rewrite (toZ32_small _ D).
    pose proof (proj1 (toZ_neg 32 x)) as T.
    rewrite (N.mod_small x (2^32) XB) in T.
    specialize (T SIGN). rewrite T, Z.abs_neq by lia.
    rewrite N2Z.inj_sub by lia.
    change (4294967296 - Z.of_N x = -(Z.of_N x - 4294967296))%Z.
    lia.
Qed.
