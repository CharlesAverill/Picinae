Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import amd64_common.
Open Scope N.

(* Lemmas for amd64_memcpy_proof.v: the head/tail move patterns glibc's
   SSE2 memcpy uses for small sizes copy exactly n bytes.  Written by
   Claude Opus 5.5 (claude-opus-5-5) and checked by Rocq.  These proofs need
   a large stack (the Makefile sets ulimit -s unlimited) and take about 15
   minutes. *)

Definition copied (m m':memory) (d s n:N) :=
  (forall i, i < n -> m' Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b d < n) -> m' Ⓑ[b] = m Ⓑ[b]).

Ltac mod64 := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Ltac peel :=
  repeat match goal with |- context [getmem 64 LittleE 1 (setmem 64 LittleE ?L ?m ?a ?v) ?b] =>
    rewrite (byte_setmem_cases m a L v b) by (lia || discriminate || reflexivity);
    destruct (N.ltb_spec (msub 64 b a) L)
  end.

Ltac leaf :=
  first [ reflexivity
        | exfalso; mod64
        | rewrite byte_of_getmem by mod64; f_equal; mod64 ].

(* Head move then tail move of L bytes covers n bytes when L <= n <= 2L. *)
Lemma copy_ht:
  forall (m:memory) d s n L, 0 < L <= 16 -> L <= n <= 2*L ->
  copied m (setmem 64 LittleE L (setmem 64 LittleE L m d (getmem 64 LittleE L m s))
                   (msub 64 d L + n) (getmem 64 LittleE L m (msub 64 s L + n))) d s n.
Proof.
  intros m d s n L HL HN. split; [ intros i I | intros b NB ]; peel; leaf.
Qed.

(* Tail move then head move. *)
Lemma copy_th:
  forall (m:memory) d s n L, 0 < L <= 16 -> L <= n <= 2*L ->
  copied m (setmem 64 LittleE L (setmem 64 LittleE L m (msub 64 d L + n) (getmem 64 LittleE L m (msub 64 s L + n)))
                   d (getmem 64 LittleE L m s)) d s n.
Proof.
  intros m d s n L HL HN. split; [ intros i I | intros b NB ]; peel; leaf.
Qed.

(* n = 2..3: word tail, then byte head. *)
Lemma copy_w_b:
  forall (m:memory) d s n, 2 <= n <= 3 ->
  copied m (setmem 64 LittleE 1 (setmem 64 LittleE 2 m (msub 64 d 2 + n) (getmem 64 LittleE 2 m (msub 64 s 2 + n)))
                   d (getmem 64 LittleE 1 m s)) d s n.
Proof.
  intros m d s n HN. split; [ intros i I | intros b NB ]; peel; leaf.
Qed.

Lemma copy_b:
  forall (m:memory) d s, copied m (setmem 64 LittleE 1 m d (getmem 64 LittleE 1 m s)) d s 1.
Proof.
  intros m d s. split; [ intros i I | intros b NB ]; peel; leaf.
Qed.

Lemma copy_0: forall (m:memory) d s, copied m m d s 0.
Proof. intros. split. intros i I. lia. intros. reflexivity. Qed.

(* n = 33..64: two head moves and two tail moves of 16 bytes. *)
Lemma copy_4x16:
  forall (m:memory) d s n, 32 < n <= 64 ->
  copied m (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 m
              d (getmem 64 LittleE 16 m s))
              (16 + d) (getmem 64 LittleE 16 m (16 + s)))
              (msub 64 d 16 + n) (getmem 64 LittleE 16 m (msub 64 s 16 + n)))
              (msub 64 d 32 + n) (getmem 64 LittleE 16 m (msub 64 s 32 + n))) d s n.
Proof.
  intros m d s n HN. split; [ intros i I | intros b NB ]; peel; leaf.
Qed.
