(* Wide-string comparison: equal nonzero prefixes and signed ordering. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_compare i386_stack2 i386_stack i386_signed.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.

Definition wide_nonzero_prefix (m:memory) (p k:N) :=
  forall i, i<k -> getmem 32 LittleE 4 m (p+4*i)<>0.
Definition wide_string_prefix (m:memory) (p q k:N) :=
  wide_equal_prefix m p q k /\ wide_nonzero_prefix m p k.
Definition wide_character_order (a b:N) := if a=?b then 0 else wide_order a b.
Definition wide_string_result (m:memory) (p q result:N) :=
  exists k, wide_string_prefix m p q k /\
    (getmem 32 LittleE 4 m (p+4*k)=0 \/
     getmem 32 LittleE 4 m (p+4*k)<>getmem 32 LittleE 4 m (q+4*k)) /\
    result=wide_character_order (getmem 32 LittleE 4 m (p+4*k)) (getmem 32 LittleE 4 m (q+4*k)).
Definition wide_bounded_string_result (m:memory) (p q n result:N) :=
  (result=0 /\ wide_string_prefix m p q n) \/
  exists k, k<n /\ wide_string_prefix m p q k /\
    (getmem 32 LittleE 4 m (p+4*k)=0 \/
     getmem 32 LittleE 4 m (p+4*k)<>getmem 32 LittleE 4 m (q+4*k)) /\
    result=wide_character_order (getmem 32 LittleE 4 m (p+4*k)) (getmem 32 LittleE 4 m (q+4*k)).

Lemma wide_string_prefix_right : forall m p q k,
  wide_string_prefix m p q k -> wide_nonzero_prefix m q k.
Proof. intros m p q k [EQ NZ] i I. rewrite <- (EQ i I). exact (NZ i I). Qed.
Lemma wide_string_prefix_advance : forall m p q k,
  wide_string_prefix m p q k ->
  getmem 32 LittleE 4 m (p+4*k)=getmem 32 LittleE 4 m (q+4*k) ->
  getmem 32 LittleE 4 m (p+4*k)<>0 -> wide_string_prefix m p q (k+1).
Proof.
  intros m p q k [EQ NZ] SAME NONZERO. split.
  - apply wide_equal_prefix_advance; assumption.
  - intros i I. destruct (N.lt_ge_cases i k) as [LT|GE]; [exact (NZ i LT)|].
    replace i with k by (clear - I GE; lia). exact NONZERO.
Qed.

Definition wide_string_avoids_saves (s0:store) (p:N) :=
  forall k, wide_nonzero_prefix (s0 V_MEM32) p k ->
    ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (p+4*k) 4 /\
    ~overlap 32 (msub 32 (s0 R_ESP) 8) 4 (p+4*k) 4.
Lemma saved_wide_string_word : forall s0 p k,
  wide_string_avoids_saves s0 p -> wide_nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 4 (save_si_bx_memory s0) (p+4*k)=
  getmem 32 LittleE 4 (s0 V_MEM32) (p+4*k).
Proof.
  intros s0 p k NO PREFIX. destruct (NO k PREFIX) as [NO4 NO8].
  unfold save_si_bx_memory.
  rewrite !getmem_noverlap by (apply noverlap_symmetry; assumption). reflexivity.
Qed.

Lemma wide_character_order_equal : forall a, wide_character_order a a=0.
Proof. intros a. unfold wide_character_order. rewrite N.eqb_refl. reflexivity. Qed.

Lemma wide_character_order_sign : forall a b, a<2^32 -> b<2^32 ->
  (toZ 32%N (wide_character_order a b) ?= 0)%Z = (toZ 32%N a ?= toZ 32%N b)%Z.
Proof.
  intros a b A B. unfold wide_character_order, wide_order.
  destruct (a=?b) eqn:EQ; [apply N.eqb_eq in EQ; subst; change (Eq=(toZ 32%N b ?= toZ 32%N b)%Z); symmetry; apply Z.compare_refl|].
  destruct (Z.ltb (toZ 32%N a) (toZ 32%N b)) eqn:LT.
  - apply Z.ltb_lt in LT. change (Lt=(toZ 32%N a ?= toZ 32%N b)%Z).
    symmetry. apply Z.compare_lt_iff. exact LT.
  - apply Z.ltb_ge in LT. change (Gt=(toZ 32%N a ?= toZ 32%N b)%Z).
    symmetry. apply Z.compare_gt_iff. assert (NE:toZ 32%N a<>toZ 32%N b).
    { intro E. apply N.eqb_neq in EQ. apply EQ. exact (toZ_inj 32 a b A B E). }
    lia.
Qed.

Lemma wide_character_order_less : forall a b,
  slt 32 a b=true -> wide_character_order a b=4294967295.
Proof.
  intros a b LT. assert (NE:a<>b).
  { intro EQ. subst b. unfold slt in LT. rewrite Z.ltb_irrefl in LT. discriminate. }
  unfold wide_character_order, wide_order. rewrite (proj2 (N.eqb_neq _ _) NE).
  change ((if slt 32 a b then 4294967295 else 1)=4294967295).
  rewrite LT. reflexivity.
Qed.
Lemma wide_character_order_not_less : forall a b,
  slt 32 a b=false -> wide_character_order a b=(if a=?b then 0 else 1).
Proof.
  intros a b LT. unfold wide_character_order, wide_order. fold (slt 32 a b).
  rewrite LT. reflexivity.
Qed.
Lemma wide_character_order_greater : forall a b,
  slt 32 b a=true -> wide_character_order a b=1.
Proof.
  intros a b GT. assert (NE:a<>b).
  { intro EQ. subst b. unfold slt in GT. rewrite Z.ltb_irrefl in GT. discriminate. }
  assert (LT:slt 32 a b=false).
  { unfold slt in *. apply Z.ltb_lt in GT. apply Z.ltb_ge. lia. }
  rewrite (wide_character_order_not_less _ _ LT), (proj2 (N.eqb_neq _ _) NE). reflexivity.
Qed.
Lemma wide_character_order_reverse_not_less : forall a b,
  a<2^32 -> b<2^32 -> slt 32 b a=false ->
  wide_character_order a b=(if a=?b then 0 else 4294967295).
Proof.
  intros a b A B GT. destruct (a=?b) eqn:EQ.
  - apply N.eqb_eq in EQ. subst b. apply wide_character_order_equal.
  - apply wide_character_order_less. unfold slt in *. apply Z.ltb_ge in GT.
    apply Z.ltb_lt. assert (NE:toZ 32%N a<>toZ 32%N b).
    { intro E. apply N.eqb_neq in EQ. apply EQ. exact (toZ_inj 32 a b A B E). }
    lia.
Qed.

Lemma wide_string_prefix_transport : forall m1 m2 p q k,
  (forall i,i<k -> getmem 32 LittleE 4 m1 (p+4*i)=getmem 32 LittleE 4 m2 (p+4*i)) ->
  (forall i,i<k -> getmem 32 LittleE 4 m1 (q+4*i)=getmem 32 LittleE 4 m2 (q+4*i)) ->
  wide_string_prefix m1 p q k -> wide_string_prefix m2 p q k.
Proof.
  intros m1 m2 p q k P Q [EQ NZ]. split; intros i I.
  - rewrite <- (P i I), <- (Q i I). exact (EQ i I).
  - rewrite <- (P i I). exact (NZ i I).
Qed.
Lemma wide_bounded_string_transport : forall m1 m2 p q n result,
  (forall i,i<n -> getmem 32 LittleE 4 m1 (p+4*i)=getmem 32 LittleE 4 m2 (p+4*i)) ->
  (forall i,i<n -> getmem 32 LittleE 4 m1 (q+4*i)=getmem 32 LittleE 4 m2 (q+4*i)) ->
  wide_bounded_string_result m1 p q n result -> wide_bounded_string_result m2 p q n result.
Proof.
  intros m1 m2 p q n result P Q RESULT.
  assert (PREFIX:forall k,k<=n -> wide_string_prefix m1 p q k -> wide_string_prefix m2 p q k).
  { intros k K PRE. eapply wide_string_prefix_transport; [| |exact PRE];
      intros i I; [apply P|apply Q]; clear - K I; lia. }
  destruct RESULT as [[ZERO EQ]|(k & K & EQ & STOP & VALUE)].
  - left. split; [exact ZERO|apply PREFIX; [apply N.le_refl|exact EQ]].
  - right. exists k. split; [exact K|]. split.
    + apply PREFIX; [apply N.lt_le_incl; exact K|exact EQ].
    + rewrite <- (P k K), <- (Q k K). split; assumption.
Qed.

Lemma wide_word_offset_mod : forall m p offset,
  getmem 32 LittleE 4 m (p+offset mod 2^32)=getmem 32 LittleE 4 m (p+offset).
Proof.
  intros. rewrite <- getmem_mod_l at 1. rewrite mp2_add_r, getmem_mod_l. reflexivity.
Qed.
