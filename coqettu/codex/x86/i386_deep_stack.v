(* Disjoint words in a descending stack frame, including nested calls. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia.
Open Scope N.

Lemma deep_stack_word_frame : forall m sp value depth off,
  4<=depth -> depth+off+4<=2^32 ->
  getmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 sp depth) value) (sp+off)=
  getmem 32 LittleE 4 m (sp+off).
Proof.
  intros m sp value depth off DEP BOUND. apply getmem_frame.
  - left. rewrite <- msub_add_distr.
    replace (depth+(sp+off)) with (sp+(depth+off)) by lia.
    rewrite msub_add_distr,msub_diag,msub_0_l.
    rewrite (N.mod_small (depth+off) (2^32)) by lia.
    rewrite N.mod_small by lia. lia.
  - left. rewrite msub_msub_distr,add_msub_l,mp2_add_l.
    rewrite N.mod_small by lia. lia.
Qed.
Lemma stack_depth_difference : forall sp d1 d2,
  msub 32 (msub 32 sp d1) (msub 32 sp d2)=msub 32 d2 d1.
Proof.
  intros. rewrite msub_msub_distr,msub_comm,msub_diag.
  rewrite <- add_msub_swap,N.add_0_l. reflexivity.
Qed.
Lemma small_separated_difference : forall x y,
  x<=64 -> y<=64 -> (x+4<=y \/ y+4<=x) -> 4<=msub 32 x y.
Proof.
  intros x y X Y SEP. destruct (N.le_ge_cases y x) as [LE|GE].
  - rewrite msub_sub by exact LE. rewrite N.mod_small by lia. lia.
  - unfold msub. rewrite (N.mod_small y (2^32)) by lia.
    rewrite N.mod_small by lia. lia.
Qed.
Lemma deep_saved_word_frame : forall m sp value saved read,
  saved<=64 -> read<=64 -> (saved+4<=read \/ read+4<=saved) ->
  getmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 sp saved) value) (msub 32 sp read)=
  getmem 32 LittleE 4 m (msub 32 sp read).
Proof.
  intros m sp value saved read S R SEP. apply getmem_frame;
    left; rewrite stack_depth_difference; apply small_separated_difference; try assumption; tauto.
Qed.

Lemma deep_stack_subregion : forall sp depth p n,
  4<=depth -> depth<=36 -> ~overlap 32 (msub 32 sp 36) 36 p n ->
  ~overlap 32 (msub 32 sp depth) 4 p n.
Proof.
  intros sp depth p n LO HI NO. eapply noverlap_shrink; [|exact NO].
  rewrite stack_depth_difference,msub_sub by lia. rewrite N.mod_small by lia. lia.
Qed.
Lemma deep_stack_byte : forall m sp depth value p n i,
  4<=depth -> depth<=36 -> ~overlap 32 (msub 32 sp 36) 36 p n -> i<n ->
  getmem 32 LittleE 1 (setmem 32 LittleE 4 m (msub 32 sp depth) value) (p+i)=
  getmem 32 LittleE 1 m (p+i).
Proof.
  intros m sp depth value p n i LO HI NO I.
  pose proof (deep_stack_subregion sp depth p n LO HI NO) as CELL.
  pose proof (getmem_frame_noverlap_index_l 32 LittleE LittleE m
    (msub 32 sp depth) 4 p n 0 i 4 1 value CELL) as FRAME.
  rewrite N.add_0_r in FRAME. apply FRAME; [reflexivity|clear - I; lia].
Qed.
