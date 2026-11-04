(* PARTIAL Astra handoff: first full build failed; no repair cycle or rebuild.
   Unchecked declarations are aborted, not exported proof constants. *)
(* 64-bit byte/frame helpers for the ARM8 memcpy proof.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, 2026-11-03.
   The byte and written-offset arguments below are adapted from the baseline
   amd64_common.v and amd64_memcpy_sets.v (Claude Opus 5.5 attribution there).
   Only pure memory arguments are reused: no AMD64 imports or ABI assumptions.
   These are mathematical memory helpers, not a replacement executable map. *)
Require Import Picinae_armv8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.

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
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

Lemma cpy_store:
  forall m m' d s (W:N->Prop) o L a sa,
  cpy m m' d s W -> (forall i, W i -> i < 2^64) -> 0 < L -> o + L <= 2^64 ->
  a mod 2^64 = (d + o) mod 2^64 -> sa mod 2^64 = (s + o) mod 2^64 ->
  cpy m (setmem 64 LittleE L m' a (getmem 64 LittleE L m sa)) d s (fun i => W i \/ o <= i < o + L).
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)


Print Assumptions byte_of_getmem.
Print Assumptions byte_setmem_cases.
Print Assumptions cpy_empty.
Print Assumptions cpy_equiv.
Print Assumptions cpy_copied.
Print Assumptions addmsub.
Print Assumptions cpy_load.
