(* Arithmetic facts for musl's four-byte string scanning idiom. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition zero_mask32 (x : N) : N :=
  N.land (N.land (N.lxor x 4294967295)
    ((x + 4278124287) mod 2^32)) 2155905152.

Lemma zero_byte_sets_bits : forall x i,
  i < 4 -> (x / 2^(i*8)) mod 256 = 0 ->
  N.testbit (x + 4278124287) (i*8+7) = true /\
  N.testbit x (i*8+7) = false.
Proof.
  intros x i I BYTE.
  assert (CASES : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by (clear - I; lia).
  repeat destruct CASES as [CASES | CASES]; subst i;
    rewrite N.testbit_true, N.testbit_false in *;
    cbn in *; lia.
Qed.

Definition nonzero_prefix (m : memory) (p k : N) : Prop :=
  forall i, i < k -> getmem 32 LittleE 1 m (p+i) <> 0.

Definition first_nul (m : memory) (p k : N) : Prop :=
  k < 2^32 /\ nonzero_prefix m p k /\
  getmem 32 LittleE 1 m (p+k) = 0.

Lemma first_nul_unique : forall m p i j,
  first_nul m p i -> first_nul m p j -> i = j.
Proof.
  intros m p i j (IB & IP & IZ) (JB & JP & JZ).
  destruct (N.lt_trichotomy i j) as [LT|[EQ|GT]]; [|exact EQ|].
  - exfalso. exact (JP i LT IZ).
  - exfalso. exact (IP j GT JZ).
Qed.

Lemma byte_add_mod : forall m p k j,
  getmem 32 LittleE 1 m ((p+k) mod 2^32+j) =
  getmem 32 LittleE 1 m (p+(k+j)).
Proof.
  intros. rewrite <- getmem_mod_l at 1.
  rewrite mp2_add_l, getmem_mod_l, N.add_assoc. reflexivity.
Qed.

Lemma byte_offset_mod : forall m p k,
  getmem 32 LittleE 1 m (p+k mod 2^32) =
  getmem 32 LittleE 1 m (p+k).
Proof.
  intros. rewrite <- getmem_mod_l at 1.
  rewrite mp2_add_r, getmem_mod_l. reflexivity.
Qed.

Lemma prefix_advance1 : forall m p k,
  nonzero_prefix m p k ->
  getmem 32 LittleE 1 m ((p+k) mod 2^32) <> 0 ->
  nonzero_prefix m p (k+1).
Proof.
  unfold nonzero_prefix. intros m p k PRE BYTE i I.
  rewrite getmem_mod_l in BYTE.
  destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (PRE i LT)|].
  replace i with k by (clear - I GE; lia). exact BYTE.
Qed.

Lemma zero_mask32_nozero : forall x,
  zero_mask32 x = 0 -> forall i,
  i < 4 -> (x / 2^(i*8)) mod 256 <> 0.
Proof.
  intros x MASK i I BYTE.
  destruct (zero_byte_sets_bits x i I BYTE) as [ADD CLEAR].
  apply (f_equal (fun n => N.testbit n (i*8+7))) in MASK.
  unfold zero_mask32 in MASK.
  rewrite !N.land_spec, N.lxor_spec,
    N.mod_pow2_bits_low, ADD, CLEAR, N.bits_0 in MASK
    by (clear - I; lia).
  assert (CASES : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by (clear - I; lia).
  repeat destruct CASES as [CASES | CASES]; subst i; discriminate MASK.
Qed.

Lemma word_mask_nozero : forall m a,
  zero_mask32 (getmem 32 LittleE 4 m a) = 0 ->
  forall j, j < 4 -> getmem 32 LittleE 1 m (a+j) <> 0.
Proof.
  intros m a MASK j J.
  pose proof (zero_mask32_nozero _ MASK j J) as BYTE.
  rewrite <- N.shiftr_div_pow2, shiftr_getmem in BYTE.
  change 256 with (2^(1*8)) in BYTE.
  rewrite getmem_mod, N.min_r in BYTE by (clear - J; lia).
  exact BYTE.
Qed.

Lemma prefix_advance4 : forall m p k,
  nonzero_prefix m p k ->
  zero_mask32 (getmem 32 LittleE 4 m ((p+k) mod 2^32)) = 0 ->
  nonzero_prefix m p (k+4).
Proof.
  intros m p k PRE MASK i I.
  destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (PRE i LT)|].
  assert (J : i-k < 4) by (clear - I GE; lia).
  pose proof (word_mask_nozero m _ MASK (i-k) J) as BYTE.
  rewrite byte_add_mod in BYTE.
  replace (k+(i-k)) with i in BYTE by (clear - GE; lia).
  exact BYTE.
Qed.

Lemma prefix_stop : forall m p k,
  nonzero_prefix m p k ->
  getmem 32 LittleE 1 m ((p+k) mod 2^32) = 0 ->
  first_nul m p (k mod 2^32).
Proof.
  intros m p k PRE BYTE. unfold first_nul. split.
  - apply mp2_mod_lt.
  - split.
    + intros i I. apply PRE. pose proof (mp2_mod_le k 32).
      clear - I H. lia.
    + rewrite byte_offset_mod. rewrite getmem_mod_l in BYTE. exact BYTE.
Qed.

Definition wide_prefix (m : memory) (p c k : N) : Prop :=
  forall i, i < k -> getmem 32 LittleE 4 m (p+4*i) <> c.

Lemma wide_prefix_advance : forall m p c k,
  wide_prefix m p c k ->
  getmem 32 LittleE 4 m ((p+4*k) mod 2^32) <> c ->
  wide_prefix m p c (k+1).
Proof.
  unfold wide_prefix. intros m p c k PRE WORD i I.
  rewrite getmem_mod_l in WORD.
  destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (PRE i LT)|].
  replace i with k by (clear - I GE; lia). exact WORD.
Qed.

Lemma remaining_decrement : forall n k,
  n < 2^32 -> k < n ->
  msub 32 (n-k) 1 = n-(k+1).
Proof.
  intros n k N K. rewrite msub_sub by lia.
  rewrite N.mod_small by lia. lia.
Qed.
