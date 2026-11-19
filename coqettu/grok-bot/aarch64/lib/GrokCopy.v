(* GrokCopy: byte-copy support for the memcpy family (store chains of loaded values).
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFill.
Import ARM8Notations.
Open Scope N.

Lemma iter_pred_sub: ∀ k len, N.iter k N.pred len = len - k.
Proof.
  induction k using N.peano_ind; intro len.
  - simpl. lia.
  - rewrite N.iter_succ, IHk. lia.
Qed.

(* byte k of a little-endian load of len bytes is the k-th byte in memory *)
Lemma byte_getmem: ∀ len m x k, k < len -> byte (getmem 64 LittleE len m x) k = m Ⓑ[k + x].
Proof.
  intros len m x k K. unfold byte.
  replace (8*k) with (k*8) by lia.
  rewrite getmem_shiftr8. change (2^8) with (2^(1*8)). rewrite getmem_mod.
  rewrite iter_pred_sub. replace (N.min (len - k) 1) with 1 by lia. reflexivity.
Qed.

(* single-byte read through a store of a loaded value *)
Lemma read_copy: ∀ len m0 m b x a w, b <= a -> a < b + len -> len <= 2^64 -> 8 * len <= w ->
  getmem 64 LittleE 1 (setmem 64 LittleE len m b (getmem 64 LittleE len m0 x mod 2^w)) a = m0 Ⓑ[(a - b) + x].
Proof.
  intros. rewrite read_in by assumption. rewrite byte_mod by lia. apply byte_getmem. lia.
Qed.

(* x - k + y computed in 64-bit arithmetic, without wraparound of the result *)
Lemma msub_add_mod: ∀ x k y, k <= x + y -> k < 2^64 -> x + y - k < 2^64 -> x < 2^64 ->
  (msub 64 x k + y) mod 2^64 = x + y - k.
Proof.
  intros x k y H1 H2 H3 H4. unfold msub. rewrite (N.mod_small k) by lia.
  rewrite N.add_mod_idemp_l by discriminate.
  replace (x + (2^64 - k) + y) with ((x + y - k) + 1 * 2^64) by lia.
  rewrite N.mod_add by discriminate. apply N.mod_small. lia.
Qed.

(* normalize load/store addresses of the form (x ⊖ k) + y *)
Ltac addr_norm :=
  repeat match goal with
  | |- context [getmem 64 ?e ?l ?m (msub 64 ?x ?k + ?y)] =>
      rewrite <- (getmem_mod_l 64 e l m (msub 64 x k + y)), (msub_add_mod x k y)
        by (change (2^64) with 18446744073709551616 in *; lia)
  | |- context [setmem 64 ?e ?l ?m (msub 64 ?x ?k + ?y) ?v] =>
      rewrite <- (setmem_mod_l 64 e l m (msub 64 x k + y) v), (msub_add_mod x k y)
        by (change (2^64) with 18446744073709551616 in *; lia)
  end.

(* rd1 with a single "outside" branch, so a chain of k stores costs O(k) *)
Ltac rdc :=
  match goal with |- context [getmem 64 LittleE 1 (setmem 64 LittleE ?len ?m ?b ?v) ?a] =>
    let H := fresh in
    assert (H: (b <= a /\ a < b + len) \/ (a < b \/ b + len <= a)) by lia;
    destruct H as [[? ?]|H];
    [ rewrite (read_in len m b v a) by (change (2^64) with 18446744073709551616 in *; lia)
    | rewrite (read_out len m b v a) by (change (2^64) with 18446744073709551616 in *; lia) ]
  end.

(* one byte of a copied region: walk the store chain, then match source bytes *)
Ltac copy_byte :=
  repeat rdc; rewrite ?byte_getmem by lia;
  first [ apply (f_equal (getmem 64 LittleE 1 _)); lia | exfalso; lia ].
