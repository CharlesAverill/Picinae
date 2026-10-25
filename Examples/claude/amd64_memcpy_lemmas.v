Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import amd64_common.
Require Export amd64_memcpy_sets.
Open Scope N.

(* Lemmas for amd64_memcpy_proof.v: the head/tail move patterns glibc's
   SSE2 memcpy uses for small sizes copy exactly n bytes.  Each pattern is a
   chain of stores whose values are all loaded from the original memory m, so
   cpy_store from amd64_memcpy_sets.v handles one store at a time.  Written
   by Claude Opus 5.5 (claude-opus-5-5) and checked by Rocq. *)

Ltac mod64 := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* The store address d - L + n is offset n - L from d. *)
Lemma addr_tail:
  forall x L n, L <= n -> L <= 64 -> (msub 64 x L + n) mod 2^64 = (x + (n - L)) mod 2^64.
Proof.
  intros x L n LN L64. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small L) by (eapply N.le_lt_trans; [exact L64 | reflexivity]).
  assert (L < 2^64) by (eapply N.le_lt_trans; [exact L64 | reflexivity]).
  replace (x + (2^64 - L) + n) with (x + (n - L) + 1 * 2^64) by lia.
  apply N.mod_add. discriminate.
Qed.

Lemma addr_head: forall x k, (k + x) mod 2^64 = (x + k) mod 2^64.
Proof. intros. rewrite N.add_comm. reflexivity. Qed.

Lemma addr_0: forall x, x mod 2^64 = (x + 0) mod 2^64.
Proof. intros. rewrite N.add_0_r. reflexivity. Qed.

(* Build the store chain from the inside out, then check the offset sets. *)
Ltac chain :=
  eapply cpy_copied; cycle 1;
  [ repeat (eapply cpy_store;
              [ | | | | first [ apply addr_0 | apply addr_head | apply addr_tail; lia ]
                      | first [ apply addr_0 | apply addr_head | apply addr_tail; lia ] ]);
    try apply cpy_empty;
    try (intros ? ?; change (2^64) with 18446744073709551616; lia);
    change (2^64) with 18446744073709551616; lia
  | intro i; split; intro Hi; lia ].

(* Head move then tail move of L bytes covers n bytes when L <= n <= 2L. *)
Lemma copy_ht:
  forall (m:memory) d s n L, 0 < L <= 16 -> L <= n <= 2*L ->
  copied m (setmem 64 LittleE L (setmem 64 LittleE L m d (getmem 64 LittleE L m s))
                   (msub 64 d L + n) (getmem 64 LittleE L m (msub 64 s L + n))) d s n.
Proof. intros. chain. Qed.

(* Tail move then head move. *)
Lemma copy_th:
  forall (m:memory) d s n L, 0 < L <= 16 -> L <= n <= 2*L ->
  copied m (setmem 64 LittleE L (setmem 64 LittleE L m (msub 64 d L + n) (getmem 64 LittleE L m (msub 64 s L + n)))
                   d (getmem 64 LittleE L m s)) d s n.
Proof. intros. chain. Qed.

(* n = 2..3: word tail, then byte head. *)
Lemma copy_w_b:
  forall (m:memory) d s n, 2 <= n <= 3 ->
  copied m (setmem 64 LittleE 1 (setmem 64 LittleE 2 m (msub 64 d 2 + n) (getmem 64 LittleE 2 m (msub 64 s 2 + n)))
                   d (getmem 64 LittleE 1 m s)) d s n.
Proof. intros. chain. Qed.

Lemma copy_b:
  forall (m:memory) d s, copied m (setmem 64 LittleE 1 m d (getmem 64 LittleE 1 m s)) d s 1.
Proof. intros. chain. Qed.

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
Proof. intros. chain. Qed.

(* n = 65..128: four head moves and four tail moves of 16 bytes. *)
Lemma copy_8x16:
  forall (m:memory) d s n, 64 < n <= 128 ->
  copied m (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16
           (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 m
              d (getmem 64 LittleE 16 m s))
              (16 + d) (getmem 64 LittleE 16 m (16 + s)))
              (32 + d) (getmem 64 LittleE 16 m (32 + s)))
              (48 + d) (getmem 64 LittleE 16 m (48 + s)))
              (msub 64 d 16 + n) (getmem 64 LittleE 16 m (msub 64 s 16 + n)))
              (msub 64 d 32 + n) (getmem 64 LittleE 16 m (msub 64 s 32 + n)))
              (msub 64 d 48 + n) (getmem 64 LittleE 16 m (msub 64 s 48 + n)))
              (msub 64 d 64 + n) (getmem 64 LittleE 16 m (msub 64 s 64 + n))) d s n.
Proof. intros. chain. Qed.
