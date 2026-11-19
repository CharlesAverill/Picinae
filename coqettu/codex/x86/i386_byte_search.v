(* Repeated-byte XOR and word skips for musl's optimized byte search. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_strings.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition repeated_byte32 (c:N):=c*16843009.
Definition nonmatching_prefix (m:memory) (p c k:N):=
  forall i,i<k ->getmem 32 LittleE 1 m (p+i)<>c.
Lemma repeated_byte32_bound:forall c,c<256 ->repeated_byte32 c<2^32.
Proof. intros c C. unfold repeated_byte32. lia. Qed.
Lemma repeated_byte32_lane:forall c i,c<256 ->i<4 ->
  (repeated_byte32 c / 2^(i*8)) mod 256=c.
Proof.
  intros c i C I. unfold repeated_byte32.
  assert (CASES:i=0 \/ i=1 \/ i=2 \/ i=3) by lia.
  repeat destruct CASES as [EQ|CASES];subst i.
  - change ((c*16843009/1) mod 256=c). rewrite N.div_1_r.
    rewrite N.Div0.mul_mod,(N.mod_small c 256 C).
    change ((c*1) mod 256=c). rewrite N.mul_1_r. apply N.mod_small;exact C.
  - change ((c*16843009/256) mod 256=c).
    replace (c*16843009) with (c*65793*256+c) by lia.
    rewrite N.div_add_l by discriminate. rewrite N.div_small,N.add_0_r by lia.
    rewrite N.Div0.mul_mod,(N.mod_small c 256 C).
    change ((c*1) mod 256=c). rewrite N.mul_1_r. apply N.mod_small;exact C.
  - change ((c*16843009/65536) mod 256=c).
    replace (c*16843009) with (c*257*65536+c*257) by lia.
    rewrite N.div_add_l by discriminate. rewrite N.div_small,N.add_0_r by lia.
    rewrite N.Div0.mul_mod,(N.mod_small c 256 C).
    change ((c*1) mod 256=c). rewrite N.mul_1_r. apply N.mod_small;exact C.
  - change ((c*16843009/16777216) mod 256=c).
    replace (c*16843009) with (c*16777216+c*65793) by lia.
    rewrite N.div_add_l by discriminate. rewrite N.div_small,N.add_0_r by lia.
    apply N.mod_small;exact C.
Qed.
Lemma xor_repeated_byte32_lane:forall m a c i,c<256 ->i<4 ->
  (N.lxor (getmem 32 LittleE 4 m a) (repeated_byte32 c)/2^(i*8)) mod 256=
  N.lxor (getmem 32 LittleE 1 m (a+i)) c.
Proof.
  intros m a c i C I.
  pose proof (repeated_byte32_lane c i C I) as LANE.
  rewrite <- N.shiftr_div_pow2 in LANE |- *.
  change 256 with (2^(1*8)) in LANE |- *.
  rewrite N.shiftr_lxor,N_lxor_mod_pow2,LANE,shiftr_getmem.
  rewrite getmem_mod,N.min_r by (clear - I;lia). reflexivity.
Qed.
Lemma xor_mask32_nonmatching:forall m a c,
  c<256 ->zero_mask32 (N.lxor (getmem 32 LittleE 4 m a) (repeated_byte32 c))=0 ->
  forall i,i<4 ->getmem 32 LittleE 1 m (a+i)<>c.
Proof.
  intros m a c C MASK i I.
  pose proof (zero_mask32_nozero _ MASK i I) as BYTE.
  rewrite (xor_repeated_byte32_lane m a c i C I) in BYTE.
  intro EQ. rewrite EQ,N.lxor_nilpotent in BYTE. contradiction.
Qed.
Lemma nonmatching_prefix_advance1:forall m p c k,
  nonmatching_prefix m p c k ->getmem 32 LittleE 1 m ((p+k) mod 2^32)<>c ->
  nonmatching_prefix m p c (k+1).
Proof.
  intros m p c k PRE BYTE i I. rewrite getmem_mod_l in BYTE.
  destruct (N.lt_ge_cases i k) as [LT|GE];[exact (PRE i LT)|].
  replace i with k by (clear - I GE;lia). exact BYTE.
Qed.
Lemma nonmatching_prefix_advance4:forall m p c k,
  c<256 ->nonmatching_prefix m p c k ->
  zero_mask32 (N.lxor (getmem 32 LittleE 4 m ((p+k) mod 2^32)) (repeated_byte32 c))=0 ->
  nonmatching_prefix m p c (k+4).
Proof.
  intros m p c k C PRE MASK i I.
  destruct (N.lt_ge_cases i k) as [LT|GE];[exact (PRE i LT)|].
  assert (J:i-k<4) by (clear - I GE;lia).
  pose proof (xor_mask32_nonmatching m _ c C MASK (i-k) J) as BYTE.
  rewrite byte_add_mod in BYTE. replace (k+(i-k)) with i in BYTE by (clear - GE;lia).
  exact BYTE.
Qed.

Lemma align_down4_32:forall n,n<2^32 ->N.land n 4294967292=n-n mod 4.
Proof.
  intros n BOUND.
  change (N.land n (N.lnot (N.ones 2) 32)=n-n mod 2^2).
  rewrite <- ldiff_land_low2 by exact BOUND.
  rewrite ldiff_sub,N.land_ones. reflexivity.
Qed.
Lemma align_down4_32_bounds:forall n,n<2^32 ->
  N.land n 4294967292<=n /\ n<N.land n 4294967292+4.
Proof.
  intros n BOUND. rewrite (align_down4_32 n BOUND).
  pose proof (N.mod_lt n 4 ltac:(discriminate)) as MOD.
  pose proof (N.Div0.mod_le n 4) as LE. lia.
Qed.
Lemma align_down4_32_multiple:forall n,n<2^32 ->(N.land n 4294967292) mod 4=0.
Proof.
  intros n BOUND. rewrite (align_down4_32 n BOUND).
  pose proof (N.div_mod n 4 ltac:(discriminate)) as DIV.
  replace (n-n mod 4) with (n/4*4) by lia. apply N.Div0.mod_mul.
Qed.

Definition forward_search_result (m:memory) (p c n result:N):=
  (exists k,k<n /\ nonmatching_prefix m p c k /\
    getmem 32 LittleE 1 m (p+k)=c /\ result=(p+k) mod 2^32) \/
  (result=0 /\ nonmatching_prefix m p c n).

Lemma zero_mask32_machine:forall x,
  N.land (N.land (msub 32 x 16843009) (N.lnot x 32)) 2155905152=zero_mask32 x.
Proof.
  intro x. unfold zero_mask32,N.lnot,msub.
  change (N.land (N.land ((x+4278124287) mod 2^32) (N.lxor x 4294967295)) 2155905152=
    N.land (N.land (N.lxor x 4294967295) ((x+4278124287) mod 2^32)) 2155905152).
  rewrite (N.land_comm ((x+4278124287) mod 2^32) (N.lxor x 4294967295)). reflexivity.
Qed.
