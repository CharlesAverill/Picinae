(* GrokCtype2: lemmas for musl's (c|32)-based ctype tests (isalpha, isalnum,
   isxdigit).  Written by Grok Bot (agent coqettu), machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List Bool.
Require Import Picinae_armv8.
Import ListNotations.
Open Scope N.

Lemma finite128: ∀ (f g : N -> bool),
  forallb (fun n => Bool.eqb (f (N.of_nat n)) (g (N.of_nat n))) (seq 0 128) = true ->
  ∀ x, x < 128 -> f x = g x.
Proof.
  intros f g FA x X. rewrite forallb_forall in FA. specialize (FA (N.to_nat x)).
  rewrite in_seq, N2Nat.id in FA. apply Bool.eqb_prop, FA. lia.
Qed.

Lemma lor32_mod: ∀ c, (N.lor c 32) mod 2^32 = N.lor (c mod 2^32) 32.
Proof.
  intro c. apply N.bits_inj. intro i. rewrite N.lor_spec.
  destruct (N.lt_ge_cases i 32) as [L|G].
  - rewrite !N.mod_pow2_bits_low, N.lor_spec by assumption. reflexivity.
  - rewrite !N.mod_pow2_bits_high by assumption.
    replace (N.testbit 32 i) with false. reflexivity.
    symmetry. apply N.bits_above_log2. change (N.log2 32) with 5. lia.
Qed.

Lemma lor32_big: ∀ x, 128 <= x -> 128 <= N.lor x 32.
Proof.
  intros x X. destruct (N.lt_ge_cases (N.lor x 32) 128) as [L|G]; [exfalso|exact G].
  assert (LG: 7 <= N.log2 x). { change 7 with (N.log2 128). apply N.log2_le_mono. exact X. }
  assert (B: N.testbit (N.lor x 32) (N.log2 x) = true).
  { rewrite N.lor_spec, N.bit_log2 by lia. reflexivity. }
  rewrite N.bits_above_log2 in B. discriminate.
  destruct (N.eq_dec (N.lor x 32) 0) as [E|E]. rewrite E. simpl. lia.
  assert (N.log2 (N.lor x 32) < 7) by (apply N.log2_lt_pow2; [lia | exact L]). lia.
Qed.

Ltac or32_tac lo hi :=
  let c := fresh "c" in intro c; rewrite lor32_mod;
  pose proof (lor32_big (c mod 2^32)) as BIG;
  destruct (N.lt_ge_cases (c mod 2^32) 128) as [L|G];
  [ apply (finite128 (fun x => (lo <=? N.lor x 32) && (N.lor x 32 <=? hi))
                     (fun x => ((lo - 32 <=? x) && (x <=? hi - 32)) || ((lo <=? x) && (x <=? hi))));
    [vm_compute; reflexivity | exact L]
  | specialize (BIG G);
    repeat match goal with |- context [?a <=? ?b] => destruct (N.leb_spec a b) end;
    try reflexivity; lia ].

Lemma alpha_or32: ∀ c,
  ((97 <=? (N.lor c 32) mod 2^32) && ((N.lor c 32) mod 2^32 <=? 122)) =
  (((65 <=? c mod 2^32) && (c mod 2^32 <=? 90)) || ((97 <=? c mod 2^32) && (c mod 2^32 <=? 122))).
Proof. or32_tac 97 122. Qed.

Lemma xalpha_or32: ∀ c,
  ((97 <=? (N.lor c 32) mod 2^32) && ((N.lor c 32) mod 2^32 <=? 102)) =
  (((65 <=? c mod 2^32) && (c mod 2^32 <=? 70)) || ((97 <=? c mod 2^32) && (c mod 2^32 <=? 102))).
Proof. or32_tac 97 102. Qed.
