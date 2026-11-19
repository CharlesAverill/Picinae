(* Count-bounded ASCII-folded comparison and wrapping-pointer endpoints. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_casecmp i386_search_arith i386_compare tolower_proof.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.
Definition bounded_case_compare_result (m:memory) (p q n result:N):=
  (n=0 /\ result=0) \/ exists k,k<n /\ case_equal_prefix m p q k /\
    (k+1=n \/getmem 32 LittleE 1 m (p+k)=0 \/getmem 32 LittleE 1 m (q+k)=0 \/
      tolower_spec (getmem 32 LittleE 1 m (p+k))<>tolower_spec (getmem 32 LittleE 1 m (q+k))) /\
    result=msub 32 (tolower_spec (getmem 32 LittleE 1 m (p+k)))
      (tolower_spec (getmem 32 LittleE 1 m (q+k))).
Lemma bounded_case_zero:forall m p q,bounded_case_compare_result m p q 0 0.
Proof. intros. left. split;reflexivity. Qed.
Lemma bounded_case_zero_unique:forall m p q result,
  bounded_case_compare_result m p q 0 result ->result=0.
Proof. intros m p q result [[N V]|[k [K REST]]];[exact V|lia]. Qed.
Lemma bounded_case_last_pointer:forall p n k,n<2^32 ->0<n ->k<n ->
  ((p+k) mod 2^32=(p+(n-1)) mod 2^32 <->k+1=n).
Proof.
  intros p n k N POS K. split.
  - intro EQ. pose proof (search_pointer_injective32 p k (n-1) ltac:(lia) ltac:(lia) EQ). lia.
  - intro EQ. replace k with (n-1) by lia. reflexivity.
Qed.
Lemma bounded_case_step_room:forall p n k,n<2^32 ->0<n ->k<n ->
  (p+k) mod 2^32<>(p+(n-1)) mod 2^32 ->k+1<n.
Proof.
  intros p n k N POS K NE. assert (LAST:k+1<>n).
  { intro EQ. apply NE. apply (proj2 (bounded_case_last_pointer p n k N POS K));exact EQ. }
  lia.
Qed.
Lemma bounded_case_complete_prefix:forall m p q n k,k+1=n ->case_equal_prefix m p q k ->
  getmem 32 LittleE 1 m (p+k)<>0 ->getmem 32 LittleE 1 m (q+k)<>0 ->
  tolower_spec (getmem 32 LittleE 1 m (p+k))=tolower_spec (getmem 32 LittleE 1 m (q+k)) ->
  case_equal_prefix m p q n.
Proof. intros m p q n k N PREFIX P Q EQ. rewrite <- N. apply case_equal_prefix_step;assumption. Qed.
Lemma bounded_case_compare_sign:forall m p q n result,bounded_case_compare_result m p q n result ->
  (n=0 /\ result=0) \/ exists k,k<n /\ case_equal_prefix m p q k /\
    (tolower_spec (getmem 32 LittleE 1 m (p+k)) ?= tolower_spec (getmem 32 LittleE 1 m (q+k)))=
      (toZ 32%N result ?=0)%Z.
Proof.
  intros m p q n result [ZERO|(k & K & PREFIX & STOP & VALUE)];[left;exact ZERO|].
  right. exists k. split;[exact K|]. split;[exact PREFIX|].
  rewrite VALUE,byte_difference_signed by (apply casefold_byte_bound;apply getmem_bound).
  rewrite <- Z.compare_sub,N2Z.inj_compare. reflexivity.
Qed.
