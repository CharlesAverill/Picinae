(* Character-class arithmetic for musl's <ctype.h> functions.

   musl classifies bytes arithmetically, e.g.
       isalpha(c) = ((unsigned)c|32)-'a' < 26
   so the proofs need facts such as  (c | 32) in ['a','z']  <->
   c in ['A','Z'] or c in ['a','z'].  Small ranges are checked by evaluation
   (range_check); values of 256 and above are excluded by lor_ge256.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Open Scope N.

Definition inr (lo hi x:N) : bool := (lo <=? x) && (x <=? hi).

Lemma inr_spec: forall lo hi x, inr lo hi x = true <-> lo <= x <= hi.
Proof. intros. unfold inr. rewrite Bool.andb_true_iff, N.leb_le, N.leb_le. reflexivity. Qed.

(* Check a boolean property on [lo, lo+len) by evaluation. *)
Lemma range_check:
  forall (f:N -> bool) lo len,
  forallb (fun i => f (lo + N.of_nat i)) (seq 0 len) = true ->
  forall y, lo <= y < lo + N.of_nat len -> f y = true.
Proof.
  intros f lo len C y Y. rewrite forallb_forall in C.
  specialize (C (N.to_nat (y - lo))). rewrite in_seq in C.
  replace (lo + N.of_nat (N.to_nat (y - lo))) with y in C by lia.
  apply C. lia.
Qed.

Lemma lor_ge256: forall x k, 256 <= x -> 256 <= x .| k.
Proof.
  intros x k X. destruct (N.lt_ge_cases (x .| k) 256) as [H|H]; [|exact H]. exfalso.
  assert (L: 8 <= N.log2 x) by (apply N.log2_le_pow2; [lia | exact X]).
  assert (T: N.testbit (x .| k) (N.log2 x) = true).
  { rewrite N.lor_spec, N.bit_log2 by lia. reflexivity. }
  destruct (N.eq_0_gt_0_cases (x .| k)) as [Z|P].
  - rewrite Z in T. discriminate.
  - rewrite N.bits_above_log2 in T. discriminate.
    apply N.lt_le_trans with 8; [|exact L]. apply N.log2_lt_pow2; [exact P | exact H].
Qed.

Lemma lor_mod32: forall x k, k < 2^32 -> (x .| k) mod 2^32 = (x mod 2^32) .| k.
Proof.
  intros x k K. apply N.bits_inj. intro i.
  destruct (N.lt_ge_cases i 32).
  - rewrite !N.mod_pow2_bits_low, !N.lor_spec, N.mod_pow2_bits_low by assumption. reflexivity.
  - rewrite N.mod_pow2_bits_high, N.lor_spec, N.mod_pow2_bits_high by assumption.
    symmetry. apply N.bits_above_log2.
    destruct k as [|k']. cbn. lia.
    apply N.lt_le_trans with 32; [|assumption]. apply N.log2_lt_pow2. lia. exact K.
Qed.

Lemma land_mod32: forall x k, k < 2^32 -> x .& k = (x mod 2^32) .& k.
Proof.
  intros x k K. apply N.bits_inj. intro i. rewrite !N.land_spec.
  destruct (N.lt_ge_cases i 32).
  - rewrite N.mod_pow2_bits_low by assumption. reflexivity.
  - replace (N.testbit k i) with false. rewrite !Bool.andb_false_r. reflexivity.
    symmetry. apply N.bits_above_log2.
    destruct k as [|k']. cbn. lia.
    apply N.lt_le_trans with 32; [|assumption]. apply N.log2_lt_pow2. lia. exact K.
Qed.

Lemma lor32_lt: forall y, y < 2^32 -> y .| 32 < 2^32.
Proof. intros. apply lor_bound; [assumption | reflexivity]. Qed.

(* (y | 32) lands in [97, hi] (hi <= 127) exactly for the two cases of a letter. *)
Lemma or32_range:
  forall y hi, hi = 122 \/ hi = 102 ->
  (97 <= y .| 32 <= hi <-> (65 <= y <= hi - 32 \/ 97 <= y <= hi)).
Proof.
  intros y hi HI.
  destruct (N.lt_ge_cases y 256) as [S|B].
  - assert (C: forall z, z < 256 ->
              Bool.eqb (inr 97 hi (z .| 32)) (inr 65 (hi - 32) z || inr 97 hi z) = true).
    { intros z Z. apply (range_check (fun z => Bool.eqb (inr 97 hi (z .| 32)) (inr 65 (hi - 32) z || inr 97 hi z)) 0 256).
      destruct HI as [->| ->]; vm_compute; reflexivity. lia. }
    specialize (C y S). apply Bool.eqb_prop in C.
    rewrite <- !inr_spec, <- Bool.orb_true_iff, C. reflexivity.
  - pose proof (lor_ge256 y 32 B). lia.
Qed.

Lemma or32_upper: forall y, 65 <= y <= 90 -> y .| 32 = y + 32.
Proof.
  intros y Y. apply N.eqb_eq.
  apply (range_check (fun y => y .| 32 =? y + 32) 65 26). vm_compute. reflexivity. lia.
Qed.

Lemma and95_lower: forall y, 97 <= y <= 122 -> y .& 95 = y - 32.
Proof.
  intros y Y. apply N.eqb_eq.
  apply (range_check (fun y => y .& 95 =? y - 32) 97 26). vm_compute. reflexivity. lia.
Qed.

(* Decide the comparison tests of a lifted classification and finish by lia. *)
Ltac ctype_cases :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch type of b with bool =>
      lazymatch b with
      | (_ <? _) => destruct b eqn:?
      | (_ =? _) => destruct b eqn:?
      | (_ <=? _) => destruct b eqn:?
      | _ && _ => destruct b eqn:?
      | _ || _ => destruct b eqn:?
      end end
  end;
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ && _) = true |- _ => apply Bool.andb_true_iff in H; destruct H
  | H: (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H
  | H: (_ || _) = true |- _ => apply Bool.orb_true_iff in H; destruct H
  | H: (_ || _) = false |- _ => apply Bool.orb_false_iff in H; destruct H
  end.

Lemma land_high32: forall x, x < 2^32 -> x .& 18446744069414584320 = 0.
Proof.
  intros x X. apply N.bits_inj_0. intro i. rewrite N.land_spec.
  destruct (N.lt_ge_cases i 32).
  - replace (N.testbit 18446744069414584320 i) with false. apply Bool.andb_false_r.
    symmetry. change 18446744069414584320 with (N.ldiff (N.ones 64) (N.ones 32)).
    rewrite N.ldiff_spec, (N.ones_spec_low 32 i) by assumption. apply Bool.andb_false_r.
  - replace (N.testbit x i) with false. reflexivity. symmetry.
    destruct x as [|x']. reflexivity. apply N.bits_above_log2.
    apply N.lt_le_trans with 32; [|assumption]. apply N.log2_lt_pow2. lia. exact X.
Qed.
