(* ASCII-folded first-difference string comparison specifications. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_strings i386_compare i386_ascii tolower_proof.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.
Lemma casefold_byte_bound:forall c,c<256 ->tolower_spec c<256.
Proof.
  intros c C. unfold tolower_spec. destruct (ascii_upper c) eqn:UP;[|exact C].
  unfold ascii_upper in UP. apply Bool.andb_true_iff in UP. destruct UP as [LO HI].
  apply N.leb_le in LO,HI. lia.
Qed.
Lemma casefold_zero_iff:forall c,tolower_spec c=0 <->c=0.
Proof.
  intros c. unfold tolower_spec. destruct (ascii_upper c) eqn:UP;[|tauto].
  unfold ascii_upper in UP. apply Bool.andb_true_iff in UP. destruct UP as [LO HI].
  apply N.leb_le in LO,HI. lia.
Qed.
Definition case_equal_prefix (m:memory) (p q k:N):=
  nonzero_prefix m p k /\ nonzero_prefix m q k /\ forall i,i<k ->
    tolower_spec (getmem 32 LittleE 1 m (p+i))=tolower_spec (getmem 32 LittleE 1 m (q+i)).
Definition case_compare_result (m:memory) (p q result:N):=exists k,k<2^32 /\
  case_equal_prefix m p q k /\
  (getmem 32 LittleE 1 m (p+k)=0 \/getmem 32 LittleE 1 m (q+k)=0 \/
    tolower_spec (getmem 32 LittleE 1 m (p+k))<>tolower_spec (getmem 32 LittleE 1 m (q+k))) /\
  result=msub 32 (tolower_spec (getmem 32 LittleE 1 m (p+k)))
    (tolower_spec (getmem 32 LittleE 1 m (q+k))).
Lemma case_equal_prefix_step:forall m p q k,case_equal_prefix m p q k ->
  getmem 32 LittleE 1 m (p+k)<>0 ->getmem 32 LittleE 1 m (q+k)<>0 ->
  tolower_spec (getmem 32 LittleE 1 m (p+k))=tolower_spec (getmem 32 LittleE 1 m (q+k)) ->
  case_equal_prefix m p q (k+1).
Proof.
  intros m p q k (P & Q & EQ) NP NQ SAME. split.
  - apply prefix_advance1;[exact P|]. rewrite getmem_mod_l. exact NP.
  - split.
    + apply prefix_advance1;[exact Q|]. rewrite getmem_mod_l. exact NQ.
    + intros i I. destruct (N.lt_ge_cases i k);[apply EQ;assumption|]. replace i with k by lia. exact SAME.
Qed.
Lemma case_compare_stop:forall m p q k result,case_equal_prefix m p q k ->
  (getmem 32 LittleE 1 m (p+k)=0 \/getmem 32 LittleE 1 m (q+k)=0 \/
    tolower_spec (getmem 32 LittleE 1 m (p+k))<>tolower_spec (getmem 32 LittleE 1 m (q+k))) ->
  result=msub 32 (tolower_spec (getmem 32 LittleE 1 m (p+k)))
    (tolower_spec (getmem 32 LittleE 1 m (q+k))) ->case_compare_result m p q result.
Proof.
  intros m p q k result (P & Q & EQ) STOP VALUE. exists (k mod 2^32).
  split;[apply N.mod_lt;discriminate|]. split.
  - pose proof (N.Div0.mod_le k (2^32)) as SMALL. split;[intros i I;apply P;lia|].
    split;[intros i I;apply Q;lia|]. intros i I;apply EQ;lia.
  - rewrite !byte_offset_mod. split;assumption.
Qed.
Lemma case_compare_result_sign:forall m p q result,case_compare_result m p q result ->
  exists k,k<2^32 /\ case_equal_prefix m p q k /\
    (tolower_spec (getmem 32 LittleE 1 m (p+k)) ?= tolower_spec (getmem 32 LittleE 1 m (q+k)))=
      (toZ 32%N result ?=0)%Z.
Proof.
  intros m p q result (k & K & PREFIX & STOP & VALUE). exists k.
  split;[exact K|]. split;[exact PREFIX|]. rewrite VALUE,byte_difference_signed by (apply casefold_byte_bound;apply getmem_bound).
  rewrite <- Z.compare_sub,N2Z.inj_compare. reflexivity.
Qed.
