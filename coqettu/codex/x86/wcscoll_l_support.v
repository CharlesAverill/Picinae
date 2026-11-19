(* Linked code and shared unary stack interface for wcscoll_l. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_stringcmp i386_wstringcmp wcscmp_proof wcscoll_l_i386 pc_thunk_bx_i386 wcscmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcscoll_l_linked : program := updateall2 wcscoll_l_i386 (updateall2 pc_thunk_bx_i386 wcscmp_i386).
Lemma wcscoll_l_linked_caller : wcscoll_l_i386 ⊆2 wcscoll_l_linked.
Proof.
  intros s a insn H. unfold wcscoll_l_linked,updateall2,updateall,wcscoll_l_i386,pc_thunk_bx_i386,wcscmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wcscoll_l_linked_wcscmp : wcscmp_i386 ⊆2 wcscoll_l_linked.
Proof. intros s a insn H. unfold wcscoll_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wcscoll_l_linked_thunk : pc_thunk_bx_i386 ⊆2 wcscoll_l_linked.
Proof.
  intros s a insn H. unfold wcscoll_l_linked,updateall2,updateall,pc_thunk_bx_i386,wcscmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wcscoll_l_linked_welltyped : welltyped_prog x86typctx wcscoll_l_linked.
Proof.
  intros s a. unfold wcscoll_l_linked,updateall2,updateall.
  destruct (wcscmp_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (wcscmp_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wcscoll_l_i386.welltyped.
Qed.



Definition wcscoll_l_got:N:=0xb4f9c.
Definition wcscoll_l_arg2:=binary_arg2.
Definition wcscoll_l_m1:=unary_m1.
Definition wcscoll_l_m2 (s0:store):=unary_m2 s0 0x55577.
Definition wcscoll_l_m4 (s0:store):=binary_m4 s0 0x55577.
Definition wcscoll_l_m5 (s0:store):=binary_entry_memory s0 0x55577 0x5558d.
Definition wcscoll_l_memory (s0:store):=binary_memory s0 0x55577 0x5558d wcscoll_l_got.
Definition wcscoll_l_reference (s0:store):=binary_reference s0 0x55577 0x5558d wcscoll_l_got.
Definition wcscoll_l_frame:=unary_frame.
Definition wcscoll_l_pre (s0:store):=models x86typctx s0 /\
  binary_string_avoids s0 4 (cdecl_arg s0) /\ binary_string_avoids s0 4 (wcscoll_l_arg2 s0).
Definition wcscoll_l_result (s0:store) (value:N):=
  wide_string_result (s0 V_MEM32) (cdecl_arg s0) (wcscoll_l_arg2 s0) value.
Lemma wcscoll_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcscoll_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma wcscoll_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wcscoll_l_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof. intros. apply binary_saved_bx;assumption. Qed.
Lemma wcscoll_l_outer_stack:forall s0 off,off<=12 ->
  getmem 32 LittleE 4 (wcscoll_l_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply binary_outer_stack;assumption. Qed.
Lemma wcscoll_l_callee_pre:forall s0 sc,wcscoll_l_pre s0 ->models x86typctx sc ->
  wcscoll_l_frame s0 (wcscoll_l_m5 s0) 32 sc ->wcscmp_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL FRAME.
  destruct (binary_callee_args s0 0x55577 0x5558d sc FRAME) as [ARG1 ARG2].
  change (models x86typctx sc /\ wide_string_avoids_saves sc (cdecl_arg sc) /\
    wide_string_avoids_saves sc (binary_arg2 sc)).
  rewrite ARG1,ARG2. split;[exact MDL|]. split.
  - intros k PREFIX.
    pose proof (binary_entry_avoids_saves s0 0x55577 0x5558d sc 4 (cdecl_arg s0) FRAME P k PREFIX) as NO.
    exact NO.
  - intros k PREFIX.
    pose proof (binary_entry_avoids_saves s0 0x55577 0x5558d sc 4 (binary_arg2 s0) FRAME Q k PREFIX) as NO.
    exact NO.
Qed.
Lemma wcscoll_l_callee_result:forall s0 sc value,wcscoll_l_pre s0 ->
  wcscoll_l_frame s0 (wcscoll_l_m5 s0) 32 sc ->
  wide_string_result (sc V_MEM32) (cdecl_arg sc) (wcscmp_arg2 sc) value ->
  wcscoll_l_result s0 value.
Proof.
  intros s0 sc value (_ & P & Q) FRAME RESULT.
  destruct (binary_callee_args s0 0x55577 0x5558d sc FRAME) as [ARG1 ARG2].
  change (wide_string_result (sc V_MEM32) (cdecl_arg sc) (binary_arg2 sc) value) in RESULT.
  rewrite ARG1,ARG2,(proj1 FRAME) in RESULT.
  destruct RESULT as (k & PREFIX & STOP & VALUE).
  pose proof (binary_read_through_prefix s0 0x55577 0x5558d 4 _ k P (proj2 PREFIX)) as READP.
  pose proof (binary_read_through_prefix s0 0x55577 0x5558d 4 _ k Q
    (wide_string_prefix_right _ _ _ _ PREFIX)) as READQ.
  unfold wcscoll_l_result. exists k. split.
  - eapply wide_string_prefix_transport;[| |exact PREFIX];intros i I;
      [apply READP|apply READQ];clear - I;lia.
  - rewrite <- (READP k (N.le_refl k)), <- (READQ k (N.le_refl k)). split;assumption.
Qed.
