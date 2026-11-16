(* GrokBitRefl: reflective reasoning about bit-permutation networks
   (and-with-constant, or, shifts, mod 2^n) over one 64-bit variable.
   Used for rbit (ffs).  Written by Grok Bot (agent coqettu) and
   machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith Lia List Bool.
Import ListNotations.
Open Scope N.

Inductive bx := BLeaf | BAnd (e:bx) (c:N) | BOr (a b:bx) | BShr (e:bx) (n:N) | BShl (e:bx) (n:N) | BMod (e:bx) (n:N).

Fixpoint bden (y:N) (e:bx) : N :=
  match e with
  | BLeaf => y
  | BAnd e c => N.land (bden y e) c
  | BOr a b => N.lor (bden y a) (bden y b)
  | BShr e n => N.shiftr (bden y e) n
  | BShl e n => N.shiftl (bden y e) n
  | BMod e n => (bden y e) mod 2^n
  end.

(* indices k of y such that bit j of the result is the OR of the bits k of y *)
Fixpoint bset (e:bx) (j:N) : list N :=
  match e with
  | BLeaf => [j]
  | BAnd e c => if N.testbit c j then bset e j else []
  | BOr a b => bset a j ++ bset b j
  | BShr e n => bset e (j+n)
  | BShl e n => if j <? n then [] else bset e (j-n)
  | BMod e n => if j <? n then bset e j else []
  end.

Lemma bset_ok: ∀ y e j, N.testbit (bden y e) j = existsb (N.testbit y) (bset e j).
Proof.
  intros y e. induction e; intro j; simpl.
  - rewrite orb_false_r. reflexivity.
  - rewrite N.land_spec, IHe. destruct (N.testbit c j); simpl.
    apply andb_true_r. apply andb_false_r.
  - rewrite N.lor_spec, IHe1, IHe2, existsb_app. reflexivity.
  - rewrite N.shiftr_spec'. apply IHe.
  - destruct (j <? n) eqn:J.
    + apply N.ltb_lt in J. rewrite N.shiftl_spec_low by lia. reflexivity.
    + apply N.ltb_ge in J. rewrite N.shiftl_spec_high' by lia. apply IHe.
  - destruct (j <? n) eqn:J.
    + apply N.ltb_lt in J. rewrite N.mod_pow2_bits_low by lia. apply IHe.
    + apply N.ltb_ge in J. rewrite N.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* an upper bound on the bit width of the result *)
Fixpoint bbnd (e:bx) : N :=
  match e with
  | BLeaf => 64
  | BAnd e c => N.min (bbnd e) (N.size c)
  | BOr a b => N.max (bbnd a) (bbnd b)
  | BShr e n => bbnd e - n
  | BShl e n => bbnd e + n
  | BMod e n => N.min (bbnd e) n
  end.

Lemma testbit_size: ∀ c j, N.size c <= j -> N.testbit c j = false.
Proof.
  intros c j H. destruct (N.eq_dec c 0) as [->|NZ]. apply N.bits_0.
  apply N.bits_above_log2. rewrite N.size_log2 in H by exact NZ. lia.
Qed.

Lemma testbit_big64: ∀ y j, y < 2^64 -> 64 <= j -> N.testbit y j = false.
Proof.
  intros y j Y J. destruct (N.eq_dec y 0) as [->|NZ]. apply N.bits_0.
  apply N.bits_above_log2. apply N.log2_lt_pow2 in Y. lia. lia.
Qed.

Lemma bbnd_ok: ∀ y e j, y < 2^64 -> bbnd e <= j -> N.testbit (bden y e) j = false.
Proof.
  intros y e. induction e; intros j Y J; simpl in *.
  - apply testbit_big64; assumption.
  - rewrite N.land_spec. destruct (N.le_ge_cases (bbnd e) (N.size c)).
    + rewrite IHe by (assumption || lia). reflexivity.
    + rewrite (testbit_size c j) by lia. apply andb_false_r.
  - rewrite N.lor_spec, IHe1, IHe2 by (assumption || lia). reflexivity.
  - rewrite N.shiftr_spec'. apply IHe; [assumption | lia].
  - destruct (N.lt_ge_cases j n).
    + apply N.shiftl_spec_low; assumption.
    + rewrite N.shiftl_spec_high' by assumption. apply IHe; [assumption | lia].
  - destruct (N.lt_ge_cases j n).
    + rewrite N.mod_pow2_bits_low by assumption. apply IHe; [assumption | lia].
    + apply N.mod_pow2_bits_high; assumption.
Qed.

(* check that output bit j (j < 64) is exactly input bit 63 - j *)
Definition brev_check (e:bx) : bool :=
  forallb (fun n => let j := N.of_nat n in
             match bset e j with [] => false | l => forallb (fun k => k =? 63 - j) l end)
          (seq 0 64) && (bbnd e <=? 64).

Lemma existsb_const: ∀ (f:N->bool) l a, l <> [] -> forallb (fun k => k =? a) l = true -> existsb f l = f a.
Proof.
  intros f l a. induction l as [|x l IH]; intros NE H. contradiction.
  simpl in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply N.eqb_eq in H1. subst x.
  simpl. destruct l as [|z l]. simpl. apply orb_false_r.
  rewrite IH by (discriminate || assumption). destruct (f a); reflexivity.
Qed.

Theorem brev_check_ok: ∀ e y, y < 2^64 -> brev_check e = true ->
  ∀ j, N.testbit (bden y e) j = (j <? 64) && N.testbit y (63 - j).
Proof.
  intros e y Y C j. unfold brev_check in C. apply andb_true_iff in C. destruct C as [C B].
  apply N.leb_le in B. destruct (j <? 64) eqn:J.
  - apply N.ltb_lt in J. rewrite forallb_forall in C.
    specialize (C (N.to_nat j)). rewrite in_seq in C. rewrite N2Nat.id in C.
    specialize (C ltac:(lia)). rewrite bset_ok. simpl.
    destruct (bset e j) as [|x l] eqn:E. discriminate.
    apply existsb_const. discriminate. exact C.
  - apply N.ltb_ge in J. apply bbnd_ok; [assumption | lia].
Qed.

Ltac reify_bx y t :=
  lazymatch t with
  | y => constr:(BLeaf)
  | N.land ?a ?c => let r := reify_bx y a in constr:(BAnd r c)
  | N.lor ?a ?b => let ra := reify_bx y a in let rb := reify_bx y b in constr:(BOr ra rb)
  | N.shiftr ?a ?n => let r := reify_bx y a in constr:(BShr r n)
  | N.shiftl ?a ?n => let r := reify_bx y a in constr:(BShl r n)
  | N.modulo ?a (N.pow 2 ?n) => let r := reify_bx y a in constr:(BMod r n)
  end.
