Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import amd64_common.
Open Scope N.

(* Lemmas for amd64_memcpy_proof.v.  memcpy copies in pieces of up to 16
   bytes, often overlapping and in an order that depends on loops, so instead
   of peeling bytes we track the set W of destination offsets written so far:

     cpy m m' d s W:  m' holds src byte s+i at d+i for every i in W, and
                      agrees with m at every address whose offset from d is
                      not in W.

   One store of a source piece adds its offsets to W (cpy_store).  When the
   buffers don't overlap, loads from the source read the original bytes
   whatever W is (cpy_load).  Written by Claude Opus 5.5 (claude-opus-5-5)
   and checked by Rocq. *)

(* The postcondition: m' holds src[0,n) at dest[0,n) and agrees with m
   everywhere else (addresses mod 2^64). *)
Definition copied (m m':memory) (d s n:N) :=
  (forall i, i < n -> m' Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b d < n) -> m' Ⓑ[b] = m Ⓑ[b]).

Definition cpy (m m':memory) d s (W:N->Prop) :=
  (forall i, W i -> m' Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ W (msub 64 b d) -> m' Ⓑ[b] = m Ⓑ[b]).

(* The man page's precondition: the areas [d, d+n) and [s, s+n) are disjoint. *)
Definition nov d s n := forall i j, i < n -> j < n -> d ⊕ i <> s ⊕ j.

Lemma cpy_empty: forall m d s, cpy m m d s (fun _ => False).
Proof. intros. split. intros i []. reflexivity. Qed.

Lemma cpy_equiv:
  forall m m' d s (W W':N->Prop), (forall i, W i <-> W' i) -> cpy m m' d s W -> cpy m m' d s W'.
Proof.
  intros m m' d s W W' E [C F]. split.
  intros i I. apply C, E, I.
  intros b B. apply F. rewrite E. exact B.
Qed.

Lemma cpy_copied:
  forall m m' d s n (W:N->Prop), (forall i, W i <-> i < n) -> cpy m m' d s W -> copied m m' d s n.
Proof.
  intros m m' d s n W E [C F]. split.
  intros i I. apply C, E, I.
  intros b B. apply F. rewrite E. exact B.
Qed.

Lemma addmsub: forall a b, (b + msub 64 a b) mod 2^64 = a mod 2^64.
Proof.
  intros a b. unfold msub. rewrite N.add_mod_idemp_r by discriminate.
  rewrite (N.div_mod b (2^64)) at 1 by discriminate.
  pose proof (N.mod_lt b (2^64) ltac:(discriminate)).
  replace (2^64 * (b / 2^64) + b mod 2^64 + (a + (2^64 - b mod 2^64)))
    with (a + (b / 2^64 + 1) * 2^64) by lia.
  apply N.mod_add. discriminate.
Qed.

Lemma cpy_load:
  forall m m' d s (W:N->Prop) n o L a,
  cpy m m' d s W -> (forall i, W i -> i < n) -> nov d s n -> o + L <= n ->
  a mod 2^64 = (s + o) mod 2^64 ->
  getmem 64 LittleE L m' a = getmem 64 LittleE L m a.
Proof.
  intros m m' d s W n o L a [C F] WN NOV OL A.
  apply getmem_frame_mem. intros b B.
  rewrite <- !(getmem_1 64 LittleE).
  apply F. intro Wb. apply (NOV (msub 64 b d) (o + msub 64 b a)).
    apply WN, Wb.
    lia.
    rewrite addmsub. rewrite N.add_assoc, <- N.add_mod_idemp_l, <- A, N.add_mod_idemp_l by discriminate.
    rewrite addmsub. reflexivity.
Qed.

(* Offset of d+i from a store address a = d+o. *)
Lemma msub_off:
  forall d i o a, i < 2^64 -> o < 2^64 -> a mod 2^64 = (d + o) mod 2^64 ->
  msub 64 (d ⊕ i) a = if o <=? i then i - o else 2^64 + i - o.
Proof.
  intros d i o a I O A. destruct (N.leb_spec o i); apply msub_add_l; [lia| |lia|].
  all: rewrite N.mod_mod by discriminate; rewrite <- (N.add_mod_idemp_l a), A, N.add_mod_idemp_l by discriminate.
  replace (d + o + (i - o)) with (d + i) by lia. reflexivity.
  replace (d + o + (2^64 + i - o)) with ((d + i) + 1 * 2^64) by lia. symmetry. apply N.mod_add. discriminate.
Qed.

Lemma cpy_store:
  forall m m' d s (W:N->Prop) o L a sa,
  cpy m m' d s W -> (forall i, W i -> i < 2^64) -> 0 < L -> o + L <= 2^64 ->
  a mod 2^64 = (d + o) mod 2^64 -> sa mod 2^64 = (s + o) mod 2^64 ->
  cpy m (setmem 64 LittleE L m' a (getmem 64 LittleE L m sa)) d s (fun i => W i \/ o <= i < o + L).
Proof.
  intros m m' d s W o L a sa [C F] WB L0 OL A SA.
  assert (O: o < 2^64) by lia.
  assert (OFF: forall i, i < 2^64 -> (msub 64 (d ⊕ i) a <? L) = (o <=? i) && (i <? o + L)).
    intros i I. rewrite (msub_off d i o a) by assumption.
    change (2^64) with 18446744073709551616 in *.
    destruct (N.leb_spec o i), (N.ltb_spec i (o + L)); cbn [andb];
      [apply N.ltb_lt | apply N.ltb_ge | apply N.ltb_ge | apply N.ltb_ge]; lia.
  split.
  - intros i Wi.
    assert (Ib: i < 2^64) by (destruct Wi as [Wi|Wi]; [apply WB, Wi | lia]).
    rewrite byte_setmem_cases, OFF by lia.
    destruct (N.leb_spec o i), (N.ltb_spec i (o + L)); cbn [andb].
    + rewrite (msub_off d i o a) by assumption. destruct (N.leb_spec o i); [|lia].
      rewrite byte_of_getmem by lia.
      rewrite <- getmem_mod_l, <- N.add_mod_idemp_l, SA, N.add_mod_idemp_l by discriminate.
      rewrite getmem_mod_l. f_equal. f_equal. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
  - intros b B. set (j := msub 64 b d) in B.
    assert (Bj: b mod 2^64 = d ⊕ j) by (subst j; rewrite add_msub; reflexivity).
    assert (J: j < 2^64) by apply msub_lt.
    rewrite byte_setmem_cases by lia.
    rewrite <- (msub_mod_l 64 64 b) by reflexivity. rewrite Bj, OFF by exact J.
    destruct (N.leb_spec o j), (N.ltb_spec j (o + L)); cbn [andb].
    + exfalso. apply B. right. lia.
    + apply F. intro Wb. apply B. left. exact Wb.
    + apply F. intro Wb. apply B. left. exact Wb.
    + apply F. intro Wb. apply B. left. exact Wb.
Qed.

(* The man-page precondition, as distances between the two areas. *)
Lemma nov_ds: forall d s n, nov d s n -> 0 < n -> n <= msub 64 d s.
Proof.
  intros d s n NOV N0. destruct (N.le_gt_cases n (msub 64 d s)) as [H|H]. exact H.
  exfalso. apply (NOV 0 (msub 64 d s) N0 H).
  rewrite N.add_0_r, (N.add_comm s), msub_add. reflexivity.
Qed.

Lemma nov_sd: forall d s n, nov d s n -> 0 < n -> n <= msub 64 s d.
Proof.
  intros d s n NOV N0. destruct (N.le_gt_cases n (msub 64 s d)) as [H|H]. exact H.
  exfalso. apply (NOV (msub 64 s d) 0 H N0).
  rewrite N.add_0_r, (N.add_comm d), msub_add. reflexivity.
Qed.

(* Writing a 16-byte value into the low lane of a YMM register. *)
Lemma ymm_low: forall x p, p < 2^128 -> (x >> 2^7 << 2^7 .| p) mod 2^128 = p.
Proof.
  intros x p P. apply N.bits_inj. intro i.
  destruct (N.ltb_spec i 128) as [I|I].
  - rewrite N.mod_pow2_bits_low, N.lor_spec by exact I.
    rewrite N.shiftl_spec_low by (change (2^7) with 128; exact I). reflexivity.
  - rewrite N.mod_pow2_bits_high by exact I.
    rewrite <- (N.mod_small p (2^128)) by exact P. rewrite N.mod_pow2_bits_high by exact I. reflexivity.
Qed.

Lemma getmem16_lt: forall m a, getmem 64 LittleE 16 m a < 2^128.
Proof. intros. apply getmem_bound. Qed.

(* Alignment arithmetic. *)
Lemma land_low: forall x k, x .& (N.ones k) = x mod 2^k.
Proof. intros. apply N.land_ones. Qed.


Lemma lor15: forall d, d .| 15 = d - d mod 16 + 15.
Proof.
  intro d.
  assert (E: d - d mod 16 = d >> 4 << 4).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^4) with 16.
    rewrite (N.div_mod d 16) at 1 by discriminate. lia. }
  assert (B: d .| 15 = (d >> 4 << 4) .| 15).
  { apply N.bits_inj. intro i. rewrite !N.lor_spec. destruct (N.ltb_spec i 4).
    - assert (T: N.testbit 15 i = true) by
        (assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia;
         destruct Hc as [E0|Hc]; [subst; reflexivity|];
         destruct Hc as [E0|Hc]; [subst; reflexivity|];
         destruct Hc as [E0|E0]; subst; reflexivity).
      rewrite T, !Bool.orb_true_r. reflexivity.
    - rewrite N.shiftl_spec_high by lia. rewrite N.shiftr_spec by lia.
      replace (i - 4 + 4) with i by lia. reflexivity. }
  rewrite B, E. apply lor_plus.
  apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0. destruct (N.ltb_spec i 4).
  - rewrite N.shiftl_spec_low by lia. reflexivity.
  - replace (N.testbit 15 i) with false. apply Bool.andb_false_r.
    symmetry. apply N.bits_above_log2. change (N.log2 15) with 3. lia.
Qed.

Lemma land_align16: forall x, x < 2^64 -> x .& 18446744073709551600 = x - x mod 16.
Proof.
  intros x X.
  assert (E: x - x mod 16 = x >> 4 << 4).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^4) with 16.
    rewrite (N.div_mod x 16) at 1 by discriminate. lia. }
  rewrite E. change 18446744073709551600 with (N.ldiff (N.ones 64) (N.ones 4)).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i 4).
  - rewrite (N.ones_spec_low 4 i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high 4 i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - 4 + 4) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct x as [|p]. apply N.bits_0.
      apply N.bits_above_log2. apply N.lt_le_trans with 64; [|lia].
      apply N.log2_lt_pow2; [reflexivity|exact X].
Qed.
