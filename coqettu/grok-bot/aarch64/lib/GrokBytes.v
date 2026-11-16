(* GrokBytes: byte-reversal (rev/rev16) networks checked by reflection, and the
   BigE/LittleE relationship for stores.  Written by Grok Bot (agent coqettu)
   and machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith Lia List Bool.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokBitRefl.
Import ListNotations.
Open Scope N.

(* every output bit j < W is (an OR of copies of) input bit f j *)
Definition bperm_check (e:bx) (W:N) (f:N->N) : bool :=
  forallb (fun n => let j := N.of_nat n in
             match bset e j with [] => false | l => forallb (fun k => k =? f j) l end)
          (seq 0 (N.to_nat W)).

Theorem bperm_check_ok: ∀ e W f y, bperm_check e W f = true ->
  ∀ j, j < W -> N.testbit (bden y e) j = N.testbit y (f j).
Proof.
  intros e W f y C j J. unfold bperm_check in C. rewrite forallb_forall in C.
  specialize (C (N.to_nat j)). rewrite in_seq, N2Nat.id in C.
  specialize (C ltac:(lia)). rewrite bset_ok.
  destruct (bset e j) as [|x l] eqn:E. discriminate.
  apply existsb_const. discriminate. exact C.
Qed.

Definition rbf (len j : N) : N := (N.pred len - j/8)*8 + j mod 8.

Theorem rev_bits_eq: ∀ y e len, bperm_check e (len*8) (rbf len) = true ->
  ∀ j, j < len*8 -> N.testbit (bden y e) j = N.testbit (revbytes y len) j.
Proof.
  intros y e len C j J. rewrite revbytes_spec, (proj2 (N.ltb_lt _ _) J).
  exact (bperm_check_ok e (len*8) (rbf len) y C j J).
Qed.

Lemma testbit_ge_bound: ∀ y W i, y < 2^W -> W <= i -> N.testbit y i = false.
Proof.
  intros y W i Y I. destruct (N.eq_dec y 0) as [->|NZ]. apply N.bits_0.
  apply N.bits_above_log2. apply N.log2_lt_pow2 in Y; lia.
Qed.

Lemma revbytes_high: ∀ y len i, y < 2^(len*8) -> len*8 <= i -> N.testbit (revbytes y len) i = false.
Proof.
  intros y len i Y I. rewrite revbytes_spec, (proj2 (N.ltb_ge _ _) I).
  apply (testbit_ge_bound y (len*8)); assumption.
Qed.

Theorem setmem_big_little: ∀ w len m a v, len <= 2^w ->
  setmem w BigE len m a v = setmem w LittleE len m a (revbytes v len).
Proof.
  intros. apply N.bits_inj. intro i. rewrite !setmem_spec by assumption. reflexivity.
Qed.

(* X = rev(y) on the low len*8 bits, where X is a bit network over y *)
Ltac rev_low y len :=
  match goal with |- N.testbit ?t ?i = _ =>
    let e := reify_bx y t in change t with (bden y e);
    apply (rev_bits_eq y e len); [vm_compute; reflexivity | assumption]
  end.
