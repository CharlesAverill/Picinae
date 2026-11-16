(* Shared bounded byte-comparison specifications and frame transport. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_bits.
From Stdlib Require Import NArith ZArith Lia.
Import X86Notations.
Open Scope N.

Definition equal_prefix (m : memory) (p q k : N) : Prop :=
  forall i, i < k -> getmem 32 LittleE 1 m (p+i) = getmem 32 LittleE 1 m (q+i).

Definition compare_result (m : memory) (p q n result : N) : Prop :=
  (result = 0 /\ equal_prefix m p q n) \/
  (exists k, k < n /\ equal_prefix m p q k /\
    getmem 32 LittleE 1 m (p+k) <> getmem 32 LittleE 1 m (q+k) /\
    result = msub 32 (getmem 32 LittleE 1 m (p+k)) (getmem 32 LittleE 1 m (q+k))).

Lemma equal_prefix_advance : forall m p q k,
  equal_prefix m p q k ->
  getmem 32 LittleE 1 m (p+k) = getmem 32 LittleE 1 m (q+k) ->
  equal_prefix m p q (k+1).
Proof.
  unfold equal_prefix. intros m p q k PRE EQ i I.
  destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (PRE i LT)|].
  replace i with k by (clear - I GE; lia). exact EQ.
Qed.

Lemma compare_result_transport : forall m1 m2 p q n result,
  (forall i, i < n -> getmem 32 LittleE 1 m1 (p+i) = getmem 32 LittleE 1 m2 (p+i)) ->
  (forall i, i < n -> getmem 32 LittleE 1 m1 (q+i) = getmem 32 LittleE 1 m2 (q+i)) ->
  compare_result m1 p q n result -> compare_result m2 p q n result.
Proof.
  intros m1 m2 p q n result P Q RESULT.
  assert (PREFIX : forall k, k <= n -> equal_prefix m1 p q k -> equal_prefix m2 p q k).
  { intros k K EQ i I. assert (IN : i < n) by (clear - K I; lia).
    rewrite <- (P i IN), <- (Q i IN). exact (EQ i I). }
  destruct RESULT as [[ZERO EQ]|(k & K & EQ & DIFF & VALUE)].
  - left. split; [exact ZERO|]. exact (PREFIX n (N.le_refl n) EQ).
  - right. exists k. repeat split; try exact K.
    + apply PREFIX; [exact (N.lt_le_incl _ _ K)|exact EQ].
    + rewrite <- (P k K), <- (Q k K). exact DIFF.
    + rewrite <- (P k K), <- (Q k K). exact VALUE.
Qed.

Lemma byte_difference_signed : forall a b, a < 256 -> b < 256 ->
  toZ 32 (msub 32 a b) = (Z.of_N a - Z.of_N b)%Z.
Proof.
  intros a b A B. rewrite msub_sbop.
  rewrite (toZ32_small a), (toZ32_small b) by lia.
  apply toZ_ofZ. unfold signed_range.
  change (-2147483648 <= Z.of_N a - Z.of_N b < 2147483648)%Z.
  lia.
Qed.

Lemma compare_result_zero : forall m p q n,
  compare_result m p q n 0 -> equal_prefix m p q n.
Proof.
  intros m p q n [[_ EQ]|(k & K & EQ & DIFF & VALUE)]; [exact EQ|].
  exfalso. apply DIFF. symmetry in VALUE. apply msub_move_0_r in VALUE.
  psimpl in VALUE. exact VALUE.
Qed.

Lemma compare_result_sign : forall m p q n result,
  compare_result m p q n result ->
  (result = 0 /\ equal_prefix m p q n) \/
  exists k, k < n /\ equal_prefix m p q k /\
    getmem 32 LittleE 1 m (p+k) <> getmem 32 LittleE 1 m (q+k) /\
    (getmem 32 LittleE 1 m (p+k) ?= getmem 32 LittleE 1 m (q+k)) =
      (toZ 32%N result ?= 0)%Z.
Proof.
  intros m p q n result [EQ|(k & K & PREFIX & DIFF & VALUE)].
  - left. exact EQ.
  - right. exists k. repeat split; try assumption.
    rewrite VALUE, byte_difference_signed by apply getmem_bound.
    rewrite <- Z.compare_sub, N2Z.inj_compare. reflexivity.
Qed.

Definition wide_equal_prefix (m : memory) (p q k : N) : Prop :=
  forall i, i < k -> getmem 32 LittleE 4 m (p+4*i) = getmem 32 LittleE 4 m (q+4*i).

Definition wide_order (a b : N) : N :=
  if (toZ 32%N a <? toZ 32%N b)%Z then 4294967295 else 1.

Definition wide_compare_result (m : memory) (p q n result : N) : Prop :=
  (result = 0 /\ wide_equal_prefix m p q n) \/
  (exists k, k < n /\ wide_equal_prefix m p q k /\
    getmem 32 LittleE 4 m (p+4*k) <> getmem 32 LittleE 4 m (q+4*k) /\
    result = wide_order (getmem 32 LittleE 4 m (p+4*k)) (getmem 32 LittleE 4 m (q+4*k))).

Lemma wide_equal_prefix_advance : forall m p q k,
  wide_equal_prefix m p q k ->
  getmem 32 LittleE 4 m (p+4*k) = getmem 32 LittleE 4 m (q+4*k) ->
  wide_equal_prefix m p q (k+1).
Proof.
  unfold wide_equal_prefix. intros m p q k PRE EQ i I.
  destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (PRE i LT)|].
  replace i with k by (clear - I GE; lia). exact EQ.
Qed.

Lemma wide_compare_result_transport : forall m1 m2 p q n result,
  (forall i, i < n -> getmem 32 LittleE 4 m1 (p+4*i) = getmem 32 LittleE 4 m2 (p+4*i)) ->
  (forall i, i < n -> getmem 32 LittleE 4 m1 (q+4*i) = getmem 32 LittleE 4 m2 (q+4*i)) ->
  wide_compare_result m1 p q n result -> wide_compare_result m2 p q n result.
Proof.
  intros m1 m2 p q n result P Q RESULT.
  assert (PREFIX : forall k, k <= n -> wide_equal_prefix m1 p q k -> wide_equal_prefix m2 p q k).
  { intros k K EQ i I. assert (IN : i < n) by (clear - K I; lia).
    rewrite <- (P i IN), <- (Q i IN). exact (EQ i I). }
  destruct RESULT as [[ZERO EQ]|(k & K & EQ & DIFF & VALUE)].
  - left. split; [exact ZERO|]. exact (PREFIX n (N.le_refl n) EQ).
  - right. exists k. repeat split; try exact K.
    + apply PREFIX; [exact (N.lt_le_incl _ _ K)|exact EQ].
    + rewrite <- (P k K), <- (Q k K). exact DIFF.
    + rewrite <- (P k K), <- (Q k K). exact VALUE.
Qed.
