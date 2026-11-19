(* Two-word absolute values and the i386 EDX:EAX result pair. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits.
From Stdlib Require Import NArith ZArith Lia.
Import X86Notations.
Open Scope N.

Definition abs64_low (lo hi:N) := if hi<?2^31 then lo else (4294967296-lo) mod 2^32.
Definition abs64_high (lo hi:N) :=
  if hi<?2^31 then hi else 4294967296-hi-(if lo=?0 then 0 else 1).
Definition abs64_value (lo hi:N) :=
  if hi<?2^31 then lo+4294967296*hi else 18446744073709551616-(lo+4294967296*hi).

Lemma complement32 : forall x,x<2^32 -> N.lxor x 4294967295=4294967295-x.
Proof.
  intros x X. change 4294967295 with (N.ones 32).
  change (N.lnot x 32=4294967295-x). apply lnot_sub_low2. exact X.
Qed.
Lemma negate32_complement : forall x,x<2^32 ->
  msub 32 (N.lxor x 4294967295) 4294967295=(4294967296-x) mod 2^32.
Proof.
  intros x X. rewrite (complement32 x X). unfold msub.
  change ((4294967295-x+1) mod 4294967296=(4294967296-x) mod 4294967296).
  replace (4294967295-x+1) with (4294967296-x) by lia. reflexivity.
Qed.

Lemma abs64_branchless : forall lo hi,lo<2^32 -> hi<2^32 ->
  let mask:=if hi<?2^31 then 0 else 4294967295 in
  msub 32 (N.lxor lo mask) mask=abs64_low lo hi /\
  msub 32 (msub 32 (N.lxor hi mask) mask)
    (if N.lxor lo mask <? mask then 1 else 0)=abs64_high lo hi.
Proof.
  intros lo hi L H. unfold abs64_low,abs64_high.
  destruct (hi<?2^31) eqn:SIGN; cbn zeta.
  - rewrite !N.lxor_0_r, !msub_0_r.
    rewrite (proj2 (N.ltb_ge lo 0) (N.le_0_l lo)).
    rewrite !msub_0_r, !(N.mod_small lo _ L), !(N.mod_small hi _ H). split; reflexivity.
  - apply N.ltb_ge in SIGN. rewrite (negate32_complement lo L), (negate32_complement hi H).
    rewrite (complement32 lo L). split; [reflexivity|].
    assert (HI:4294967296-hi<2^32) by lia.
    rewrite (N.mod_small _ _ HI).
    destruct (lo=?0) eqn:ZERO.
    + apply N.eqb_eq in ZERO. subst lo. rewrite N.sub_0_r, N.ltb_irrefl.
      rewrite msub_0_r, (N.mod_small _ _ HI), N.sub_0_r. reflexivity.
    + apply N.eqb_neq in ZERO.
      assert (BORROW:(4294967295-lo<?4294967295)=true) by (apply N.ltb_lt; lia).
      rewrite BORROW, msub_sub by lia. apply N.mod_small. lia.
Qed.

Lemma abs64_pair_value : forall lo hi,lo<2^32 -> hi<2^32 ->
  abs64_low lo hi+4294967296*abs64_high lo hi=abs64_value lo hi.
Proof.
  intros lo hi L H. unfold abs64_low,abs64_high,abs64_value.
  destruct (hi<?2^31) eqn:SIGN; [reflexivity|]. apply N.ltb_ge in SIGN.
  destruct (lo=?0) eqn:ZERO.
  - apply N.eqb_eq in ZERO. subst lo. rewrite N.sub_0_r, N.mod_same by discriminate. lia.
  - apply N.eqb_neq in ZERO. rewrite N.mod_small by lia. lia.
Qed.

Lemma cdecl_ret_preserves_edx : forall p ret s x s',
  p s ret=Some (1,i386_ret) -> can_step p ((x,s'),(Addr ret,s)) -> s' R_EDX=s R_EDX.
Proof.
  intros p ret s x s' LOOK STEP. inversion STEP; subst.
  rewrite LOOK in LU. injection LU as SZ CODE. subst sz q.
  unfold i386_ret in XS. step_stmt XS. psimpl in XS.
  destruct XS as [[STORE JUMP] ACC]. rewrite STORE. simpl_stores. reflexivity.
Qed.

Lemma ashiftr31_mask : forall hi,hi<2^32 ->
  ashiftr 32 hi 31 = if hi<?2^31 then 0 else 4294967295.
Proof.
  intros hi H. assert (BIT:N.testbit hi 31=negb (hi<?2^31)).
  { destruct (hi<?2^31) eqn:SIGN; csimpl; cbn [negb].
    - apply N.testbit_false. cbn. lia.
    - apply N.testbit_true. cbn. lia. }
  destruct (hi<?2^31) eqn:SIGN; cbn [negb] in BIT;
    apply N.bits_inj; intro i; rewrite ashiftr_spec;
    replace (N.pred 32) with 31 by reflexivity;
    replace (N.min (i+31) 31) with 31 by (symmetry; apply N.min_r; lia);
    rewrite BIT.
  - rewrite N.bits_0, Bool.andb_false_r. reflexivity.
  - change 4294967295 with (N.ones 32). rewrite N_ones_spec_ltb, Bool.andb_true_r. reflexivity.
Qed.

Lemma toZ64_small : forall x,x<2^63 -> toZ 64 x=Z.of_N x.
Proof.
  intros x X. assert (B:x<2^64) by lia.
  pose proof (proj1 (toZ_nonneg 64 x)) as T.
  rewrite (N.mod_small x (2^64) B) in T. exact (T X).
Qed.
Lemma abs_word64_signed : forall x,x<2^64 -> x<>2^63 ->
  toZ 64 (if x<?2^63 then x else 2^64-x)=Z.abs (toZ 64 x).
Proof.
  intros x X MIN. destruct (x<?2^63) eqn:SIGN; csimpl.
  - rewrite (toZ64_small x SIGN), Z.abs_eq; [reflexivity|apply N2Z.is_nonneg].
  - assert (D:2^64-x<2^63) by lia. rewrite (toZ64_small _ D).
    pose proof (proj1 (toZ_neg 64 x)) as T.
    rewrite (N.mod_small x (2^64) X) in T. specialize (T SIGN).
    rewrite T, Z.abs_neq by lia. rewrite N2Z.inj_sub by lia.
    change (18446744073709551616-Z.of_N x = -(Z.of_N x-18446744073709551616))%Z. lia.
Qed.
Lemma abs64_value_signed : forall lo hi,lo<2^32 -> hi<2^32 ->
  lo+4294967296*hi<>2^63 ->
  toZ 64 (abs64_value lo hi)=Z.abs (toZ 64 (lo+4294967296*hi)).
Proof.
  intros lo hi L H MIN.
  assert (SIGN:(hi<?2^31)=(lo+4294967296*hi<?2^63)).
  { destruct (hi<?2^31) eqn:A; destruct (lo+4294967296*hi<?2^63) eqn:B;
      try reflexivity; csimpl; exfalso; lia. }
  unfold abs64_value. rewrite SIGN. apply abs_word64_signed; [lia|exact MIN].
Qed.
