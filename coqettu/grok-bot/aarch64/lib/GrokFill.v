(* GrokFill: byte-splat values and single-byte reads through overlapping stores,
   for memset-like code.  Written by Grok Bot (agent coqettu) and
   machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List Bool.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFrame.
Import ListNotations.
Open Scope N.

(* bit networks over two variables y (L1) and z (L2) *)
Inductive bz := ZL1 | ZL2 | ZAnd (e:bz) (c:N) | ZOr (a b:bz) | ZShr (e:bz) (n:N) | ZShl (e:bz) (n:N) | ZMod (e:bz) (n:N).

Fixpoint zden (y z:N) (e:bz) : N :=
  match e with
  | ZL1 => y
  | ZL2 => z
  | ZAnd e c => N.land (zden y z e) c
  | ZOr a b => N.lor (zden y z a) (zden y z b)
  | ZShr e n => N.shiftr (zden y z e) n
  | ZShl e n => N.shiftl (zden y z e) n
  | ZMod e n => (zden y z e) mod 2^n
  end.

(* (false,k) = bit k of y, (true,k) = bit k of z *)
Fixpoint zset (e:bz) (j:N) : list (bool * N) :=
  match e with
  | ZL1 => [(false, j)]
  | ZL2 => [(true, j)]
  | ZAnd e c => if N.testbit c j then zset e j else []
  | ZOr a b => zset a j ++ zset b j
  | ZShr e n => zset e (j+n)
  | ZShl e n => if j <? n then [] else zset e (j-n)
  | ZMod e n => if j <? n then zset e j else []
  end.

Definition zbit (y z:N) (p:bool*N) := if fst p then N.testbit z (snd p) else N.testbit y (snd p).

Lemma zset_ok: ∀ y z e j, N.testbit (zden y z e) j = existsb (zbit y z) (zset e j).
Proof.
  intros y z e. induction e; intro j; simpl.
  - rewrite orb_false_r. reflexivity.
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

(* every bit j < 8*nb of e is exactly bit (j mod 8) of y *)
Definition zsplat_check (e:bz) (nb:N) : bool :=
  forallb (fun n => let j := N.of_nat n in
             match zset e j with [] => false | l => forallb (fun p => negb (fst p) && (snd p =? j mod 8)) l end)
          (seq 0 (N.to_nat (8*nb))).

Lemma existsb_const2: ∀ y z l a, l <> [] -> forallb (fun p => negb (fst p) && (snd p =? a)) l = true ->
  existsb (zbit y z) l = N.testbit y a.
Proof.
  intros y z l a. induction l as [|[b k] l IH]; intros NE H. contradiction.
  simpl in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1.
  destruct H1 as [H0 H1]. apply N.eqb_eq in H1. subst k. destruct b; [discriminate|].
  change (existsb (zbit y z) ((false,a)::l)) with (N.testbit y a || existsb (zbit y z) l).
  destruct l as [|p l]. apply orb_false_r.
  rewrite IH by (discriminate || assumption). destruct (N.testbit y a); reflexivity.
Qed.

Definition splat_bytes (v c nb : N) := ∀ i, i < nb -> byte v i = c mod 2^8.

Theorem zsplat_check_ok: ∀ e nb y z, zsplat_check e nb = true -> splat_bytes (zden y z e) y nb.
Proof.
  intros e nb y z C i I. unfold byte. apply N.bits_inj. intro k.
  destruct (N.lt_ge_cases k 8) as [K|K].
  - rewrite !N.mod_pow2_bits_low by lia. rewrite N.shiftr_spec', zset_ok.
    unfold zsplat_check in C. rewrite forallb_forall in C.
    specialize (C (N.to_nat (k + 8*i))). rewrite in_seq, N2Nat.id in C. specialize (C ltac:(lia)).
    replace ((k + 8 * i) mod 8) with k in C.
    + destruct (zset e (k + 8*i)) eqn:E. discriminate. apply existsb_const2. discriminate. exact C.
    + symmetry. rewrite (N.mul_comm 8 i), N.Div0.mod_add. apply N.mod_small; lia.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Ltac reify_bz y z t :=
  lazymatch t with
  | y => constr:(ZL1)
  | z => constr:(ZL2)
  | N.land ?a ?c => let r := reify_bz y z a in constr:(ZAnd r c)
  | N.lor ?a ?b => let ra := reify_bz y z a in let rb := reify_bz y z b in constr:(ZOr ra rb)
  | N.shiftr ?a ?n => let r := reify_bz y z a in constr:(ZShr r n)
  | N.shiftl ?a ?n => let r := reify_bz y z a in constr:(ZShl r n)
  | N.modulo ?a (N.pow 2 ?n) => let r := reify_bz y z a in constr:(ZMod r n)
  end.

(* prove splat_bytes t y nb for a bit-network t over y and z *)
Ltac solve_splat y z :=
  match goal with |- splat_bytes ?t y ?nb =>
    let e := reify_bz y z t in change t with (zden y z e);
    apply zsplat_check_ok; vm_compute; reflexivity end.

(* single-byte reads through a store *)
Lemma read_in: ∀ len m b v a, b <= a -> a < b + len -> len <= 2^64 ->
  getmem 64 LittleE 1 (setmem 64 LittleE len m b v) a = byte v (a - b).
Proof.
  intros len m b v a H1 H2 H3. rewrite getmem_1.
  replace a with (b + (a - b)) at 1 by lia.
  rewrite setmem_byte by (assumption || lia). unfold byte. rewrite N.mul_comm. reflexivity.
Qed.

Lemma read_out: ∀ len m b v a, (a < b \/ b + len <= a) -> a < 2^64 -> b + len <= 2^64 ->
  getmem 64 LittleE 1 (setmem 64 LittleE len m b v) a = getmem 64 LittleE 1 m a.
Proof.
  intros len m b v a H A B. destruct (N.eq_dec len 0) as [->|NZ].
  - rewrite setmem_0. reflexivity.
  - destruct H as [H|H].
    + apply getmem_setmem_above; lia.
    + apply getmem_setmem_below; lia.
Qed.

Ltac rd1 :=
  match goal with |- context [getmem 64 LittleE 1 (setmem 64 LittleE ?len ?m ?b ?v) ?a] =>
    let H1 := fresh in let H2 := fresh in
    destruct (N.le_gt_cases b a) as [H1|H1];
    [ destruct (N.lt_ge_cases a (b + len)) as [H2|H2];
      [ rewrite (read_in len m b v a) by (change (2^64) with 18446744073709551616 in *; lia)
      | rewrite (read_out len m b v a) by (change (2^64) with 18446744073709551616 in *; lia) ]
    | rewrite (read_out len m b v a) by (change (2^64) with 18446744073709551616 in *; lia) ]
  end.

Lemma byte_mod: ∀ v m i, 8 * i + 8 <= m -> byte (v mod 2^m) i = byte v i.
Proof.
  intros v m i H. unfold byte. apply N.bits_inj. intro k.
  destruct (N.lt_ge_cases k 8) as [K|K].
  - rewrite !N.mod_pow2_bits_low by lia. rewrite !N.shiftr_spec'.
    rewrite N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma splat_mod: ∀ v c nb m k, splat_bytes v c nb -> k <= nb -> 8 * k <= m -> splat_bytes (v mod 2^m) c k.
Proof. intros v c nb m k S K M i I. rewrite byte_mod by lia. apply S. lia. Qed.
