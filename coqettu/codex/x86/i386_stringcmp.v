(* First-difference-or-NUL specifications for byte string comparison. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_strings i386_compare i386_stack2.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.

Definition string_equal_prefix (m : memory) (p q k : N) : Prop :=
  equal_prefix m p q k /\ nonzero_prefix m p k.
Definition string_compare_result (m : memory) (p q result : N) : Prop :=
  exists k, k < 2^32 /\ string_equal_prefix m p q k /\
    (getmem 32 LittleE 1 m (p+k)=0 \/
     getmem 32 LittleE 1 m (p+k)<>getmem 32 LittleE 1 m (q+k)) /\
    result=msub 32 (getmem 32 LittleE 1 m (p+k)) (getmem 32 LittleE 1 m (q+k)).

Lemma string_equal_prefix_right : forall m p q k,
  string_equal_prefix m p q k -> nonzero_prefix m q k.
Proof. intros m p q k [EQ NZ] i I. rewrite <- (EQ i I). exact (NZ i I). Qed.

Lemma string_equal_prefix_advance : forall m p q k,
  string_equal_prefix m p q k ->
  getmem 32 LittleE 1 m (p+k)=getmem 32 LittleE 1 m (q+k) ->
  getmem 32 LittleE 1 m (p+k)<>0 -> string_equal_prefix m p q (k+1).
Proof.
  intros m p q k [EQ NZ] SAME NONZERO. split.
  - apply equal_prefix_advance; assumption.
  - apply prefix_advance1; [exact NZ|]. rewrite getmem_mod_l. exact NONZERO.
Qed.

Lemma string_compare_stop : forall m p q k result,
  string_equal_prefix m p q k ->
  (getmem 32 LittleE 1 m (p+k)=0 \/
   getmem 32 LittleE 1 m (p+k)<>getmem 32 LittleE 1 m (q+k)) ->
  result=msub 32 (getmem 32 LittleE 1 m (p+k)) (getmem 32 LittleE 1 m (q+k)) ->
  string_compare_result m p q result.
Proof.
  intros m p q k result [EQ NZ] STOP VALUE. exists (k mod 2^32).
  split; [apply N.mod_lt; discriminate|]. split.
  - assert (SMALL : k mod 2^32 <= k) by apply N.Div0.mod_le.
    split; intros i I; [apply EQ|apply NZ]; clear - I SMALL; lia.
  - rewrite !byte_offset_mod. split; assumption.
Qed.

(* A normal input string does not pass through either callee-owned save slot.
   This condition needs no caller-supplied length or terminator witness. *)
Definition string_avoids_saves (s0 : store) (p : N) : Prop :=
  forall k, nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (p+k) 1 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 4 (p+k) 1.

Lemma saved_string_byte : forall s0 p k,
  string_avoids_saves s0 p -> nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (save_si_bx_memory s0) (p+k)=
    getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 p k NO PREFIX. destruct (NO k PREFIX) as [NO4 NO8].
  apply save_si_bx_byte; assumption.
Qed.

Lemma string_compare_result_sign : forall m p q result,
  string_compare_result m p q result ->
  exists k, k<2^32 /\ string_equal_prefix m p q k /\
    (getmem 32 LittleE 1 m (p+k)=0 \/
     getmem 32 LittleE 1 m (p+k)<>getmem 32 LittleE 1 m (q+k)) /\
    (getmem 32 LittleE 1 m (p+k) ?= getmem 32 LittleE 1 m (q+k)) =
      (toZ 32%N result ?= 0)%Z.
Proof.
  intros m p q result (k & K & PREFIX & STOP & VALUE).
  exists k. repeat split; try assumption; try exact (proj1 PREFIX); try exact (proj2 PREFIX).
  rewrite VALUE, byte_difference_signed by apply getmem_bound.
  rewrite <- Z.compare_sub, N2Z.inj_compare. reflexivity.
Qed.

Lemma string_compare_result_zero : forall m p q,
  string_compare_result m p q 0 ->
  exists k, first_nul m p k /\ first_nul m q k /\ equal_prefix m p q k.
Proof.
  intros m p q (k & K & [EQ NZ] & STOP & VALUE).
  symmetry in VALUE. apply msub_move_0_r in VALUE. psimpl in VALUE.
  assert (ZERO : getmem 32 LittleE 1 m (p+k)=0).
  { destruct STOP as [ZERO|DIFF]; [exact ZERO|contradiction]. }
  exists k. split; [repeat split; assumption|]. split.
  - split; [exact K|]. split.
    + exact (string_equal_prefix_right m p q k (conj EQ NZ)).
    + rewrite <- VALUE. exact ZERO.
  - exact EQ.
Qed.
