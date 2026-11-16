(* Word-granular (32-bit) copy predicates for the wide-character copy
   functions (wmemcpy, wmemmove, wcscpy, ...).  The frame of each predicate
   is exactly the words written so far, so a source word can be shown intact
   even when the source and destination overlap (as wmemmove allows):
   a forward copy is safe whenever the destination is at least 4n bytes past
   the source modulo 2^64, a backward copy whenever it is less than 4n past.

   Model:   Written by Claude Fable 5.1 (claude-fable-5-1), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* the n words at d hold the n words at s (as in m); every byte outside the
   4n bytes at d is as in m *)
Definition wmoved (m M:memory) (d s n:N) :=
  (forall i, i < n -> M Ⓓ[d ⊕ 4*i] = m Ⓓ[s ⊕ 4*i]) /\
  (forall b, ~ (msub 64 b d < 4*n) -> M Ⓑ[b] = m Ⓑ[b]).

Lemma wmoved_refl: forall m d n, wmoved m m d d n.
Proof. intros. split. intros i I. reflexivity. intros b B. reflexivity. Qed.

(* the source words 0..k are nonzero *)
Definition nzw (m s k:N) := forall i, i < k -> m Ⓓ[s ⊕ 4*i] <> 0.

Lemma nzw_succ: forall m s k, nzw m s k -> m Ⓓ[s ⊕ 4*k] <> 0 -> nzw m s (k + 1).
Proof.
  intros m s k NZ B i I. destruct (N.lt_ge_cases i k). apply NZ. assumption.
  replace i with k by lia. exact B.
Qed.

(* ---- forward copy: words 0..k done ---- *)

Definition wcpf (m M:memory) (d s k:N) :=
  (forall i, i < k -> M Ⓓ[d ⊕ 4*i] = m Ⓓ[s ⊕ 4*i]) /\
  (forall b, ~ (msub 64 b d < 4*k) -> M Ⓑ[b] = m Ⓑ[b]).

Lemma wcpf_empty: forall m d s, wcpf m m d s 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma wcpf_moved: forall m M d s n, wcpf m M d s n -> wmoved m M d s n.
Proof. intros m M d s n [C F]. split; assumption. Qed.

(* source word k is still intact when the destination is at least 4n bytes
   past the source (true for disjoint areas, and for a destination below an
   overlapping source) *)
Lemma wcpf_src:
  forall m M d s k n, wcpf m M d s k -> k < n -> 4*n <= msub 64 d s -> 4*n < 2^63 ->
  M Ⓓ[s ⊕ 4*k] = m Ⓓ[s ⊕ 4*k].
Proof.
  intros m M d s k n [_ F] K DS NB. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply F. intro H. mlia.
Qed.

Lemma wcpf_store:
  forall m M d s k a v, wcpf m M d s k -> 4*(k+1) < 2^63 ->
  a mod 2^64 = (d + 4*k) mod 2^64 -> v mod 2^32 = m Ⓓ[s ⊕ 4*k] ->
  wcpf m (setmem 64 LittleE 4 M a v) d s (k + 1).
Proof.
  intros m M d s k a v [C F] K A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply C, IK.
      intros [x [y [X [Y E]]]]. mlia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. intro H. apply B. lia.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

(* ---- backward copy: words k..n done ---- *)

Definition wcpb (m M:memory) (d s k n:N) :=
  (forall i, k <= i < n -> M Ⓓ[d ⊕ 4*i] = m Ⓓ[s ⊕ 4*i]) /\
  (forall b, ~ (4*k <= msub 64 b d < 4*n) -> M Ⓑ[b] = m Ⓑ[b]).

Lemma wcpb_empty: forall m d s n, wcpb m m d s n n.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma wcpb_moved: forall m M d s n, wcpb m M d s 0 n -> wmoved m M d s n.
Proof.
  intros m M d s n [C F]. split. intros i I. apply C. lia.
  intros b B. apply F. intro H. apply B. lia.
Qed.

(* source word k-1 is still intact while the destination is less than 4n
   bytes past the source *)
Lemma wcpb_src:
  forall m M d s k n, wcpb m M d s k n -> 0 < k -> k <= n -> msub 64 d s < 4*n -> 4*n < 2^63 ->
  M Ⓓ[s ⊕ 4*(k-1)] = m Ⓓ[s ⊕ 4*(k-1)].
Proof.
  intros m M d s k n [_ F] K KN DS NB. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply F. intro H. mlia.
Qed.

Lemma wcpb_store:
  forall m M d s k n a v, wcpb m M d s k n -> 0 < k -> k <= n -> 4*n < 2^63 ->
  a mod 2^64 = (d + 4*(k-1)) mod 2^64 -> v mod 2^32 = m Ⓓ[s ⊕ 4*(k-1)] ->
  wcpb m (setmem 64 LittleE 4 M a v) d s (k-1) n.
Proof.
  intros m M d s k n a v [C F] K KN NB A V. split.
  - intros i [I1 I2]. destruct (N.lt_ge_cases (k-1) i) as [IK|IK].
    + rewrite getmem_noverlap. apply C. lia.
      intros [x [y [X [Y E]]]]. mlia.
    + replace i with (k-1) by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. intro H. apply B. lia.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

(* disjoint areas put the destination at least 4n bytes past the source *)
Lemma noverlap_msub: forall d s n, ~ overlap 64 d (4*n) s (4*n) -> 0 < n -> 4*n <= msub 64 d s.
Proof.
  intros d s n NO N. apply N.nlt_ge. intro H. apply NO.
  exists 0, (msub 64 d s). split. lia. split. exact H. mlia.
Qed.
