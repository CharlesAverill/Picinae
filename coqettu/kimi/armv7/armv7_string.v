From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_zero32.
Import ARM7Notations.
Open Scope N.

Definition nonzero_prefix (m : memory) (p k : N) : Prop :=
  forall i, i < k -> m Ⓑ[p+i] <> 0.

Lemma getmem32_byte (m : memory) (a i : N) (I : i < 4) :
  m Ⓑ[a+i] = (m Ⓓ[a] / 2^(8*i)) mod 2^8.
Proof.
  apply N.bits_inj. intro b. destruct (N.ltb_spec b 8) as [HB|HB].
  - rewrite N.mod_pow2_bits_low by exact HB. rewrite N.div_pow2_bits.
    rewrite !getmem_spec.
    change (b <? 1*8) with (b <? 8).
    change (b+8*i <? 4*8) with (b+8*i <? 32).
    rewrite (proj2 (N.ltb_lt b 8) HB).
    assert (HBI : b+8*i < 32) by lia.
    rewrite (proj2 (N.ltb_lt _ _) HBI).
    cbn [andb]. apply (f_equal (N.testbit m)).
    apply (f_equal (fun x => x mod (2^32*8))). lia.
  - rewrite N.mod_pow2_bits_high by exact HB.
    rewrite getmem_spec. change (b <? 1*8) with (b <? 8).
    rewrite (proj2 (N.ltb_ge b 8) HB). reflexivity.
Qed.

Lemma nonzero_prefix_succ (m : memory) (p k : N) :
  nonzero_prefix m p k -> m Ⓑ[p+k] <> 0 -> nonzero_prefix m p (k+1).
Proof.
  intros P NZ i HI. rewrite N.add_1_r in HI.
  apply N.lt_succ_r, N.le_lteq in HI. destruct HI as [LT|EQ].
  - apply P. exact LT.
  - subst i. exact NZ.
Qed.

Lemma nonzero_prefix_word (m : memory) (p k : N) :
  nonzero_prefix m p k -> zero32 (m Ⓓ[p+k]) = 0 ->
  nonzero_prefix m p (k+4).
Proof.
  intros P Z i HI. destruct (N.lt_ge_cases i k) as [LT|GE].
  - apply P. exact LT.
  - remember (i-k) as j. assert (EJ : i = k+j) by lia.
    assert (J : j < 4) by lia. subst i. intros B.
    apply (zero32_byte (m Ⓓ[p+k]) j (getmem_bound _ _ _ _ _) J).
    pose proof (getmem32_byte m (p+k) j J) as G.
    replace (p+(k+j)) with (p+k+j) in B by lia.
    rewrite <- G. exact B. exact Z.
Qed.
