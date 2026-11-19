(* Linked code and shared unary stack interface for strcoll_l. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_stringcmp i386_wstringcmp strcmp_proof strcoll_l_i386 pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcoll_l_linked : program := updateall2 strcoll_l_i386 (updateall2 pc_thunk_bx_i386 strcmp_i386).
Lemma strcoll_l_linked_caller : strcoll_l_i386 ⊆2 strcoll_l_linked.
Proof.
  intros s a insn H. unfold strcoll_l_linked,updateall2,updateall,strcoll_l_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strcoll_l_linked_strcmp : strcmp_i386 ⊆2 strcoll_l_linked.
Proof. intros s a insn H. unfold strcoll_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strcoll_l_linked_thunk : pc_thunk_bx_i386 ⊆2 strcoll_l_linked.
Proof.
  intros s a insn H. unfold strcoll_l_linked,updateall2,updateall,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strcoll_l_linked_welltyped : welltyped_prog x86typctx strcoll_l_linked.
Proof.
  intros s a. unfold strcoll_l_linked,updateall2,updateall.
  destruct (strcmp_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (strcmp_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strcoll_l_i386.welltyped.
Qed.



Definition strcoll_l_got:N:=0xb4f9c.
Definition strcoll_l_arg2:=binary_arg2.
Definition strcoll_l_m1:=unary_m1.
Definition strcoll_l_m2 (s0:store):=unary_m2 s0 0x552e5.
Definition strcoll_l_m4 (s0:store):=binary_m4 s0 0x552e5.
Definition strcoll_l_m5 (s0:store):=binary_entry_memory s0 0x552e5 0x552fb.
Definition strcoll_l_memory (s0:store):=binary_memory s0 0x552e5 0x552fb strcoll_l_got.
Definition strcoll_l_reference (s0:store):=binary_reference s0 0x552e5 0x552fb strcoll_l_got.
Definition strcoll_l_frame:=unary_frame.
Definition strcoll_l_pre (s0:store):=models x86typctx s0 /\
  binary_string_avoids s0 1 (cdecl_arg s0) /\ binary_string_avoids s0 1 (strcoll_l_arg2 s0).
Definition strcoll_l_result (s0:store) (value:N):=
  string_compare_result (s0 V_MEM32) (cdecl_arg s0) (strcoll_l_arg2 s0) value.
Lemma strcoll_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strcoll_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma strcoll_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strcoll_l_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof. intros. apply binary_saved_bx;assumption. Qed.
Lemma strcoll_l_outer_stack:forall s0 off,off<=12 ->
  getmem 32 LittleE 4 (strcoll_l_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply binary_outer_stack;assumption. Qed.
Lemma strcoll_l_callee_pre:forall s0 sc,strcoll_l_pre s0 ->models x86typctx sc ->
  strcoll_l_frame s0 (strcoll_l_m5 s0) 32 sc ->strcmp_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL FRAME.
  destruct (binary_callee_args s0 0x552e5 0x552fb sc FRAME) as [ARG1 ARG2].
  change (models x86typctx sc /\ string_avoids_saves sc (cdecl_arg sc) /\
    string_avoids_saves sc (binary_arg2 sc)).
  rewrite ARG1,ARG2. split;[exact MDL|]. split.
  - intros k PREFIX.
    apply call_prefix_byte in PREFIX.
    pose proof (binary_entry_avoids_saves s0 0x552e5 0x552fb sc 1 (cdecl_arg s0) FRAME P k PREFIX) as NO.
    rewrite N.mul_1_l in NO. exact NO.
  - intros k PREFIX.
    apply call_prefix_byte in PREFIX.
    pose proof (binary_entry_avoids_saves s0 0x552e5 0x552fb sc 1 (binary_arg2 s0) FRAME Q k PREFIX) as NO.
    rewrite N.mul_1_l in NO. exact NO.
Qed.
Lemma strcoll_l_callee_result:forall s0 sc value,strcoll_l_pre s0 ->
  strcoll_l_frame s0 (strcoll_l_m5 s0) 32 sc ->
  string_compare_result (sc V_MEM32) (cdecl_arg sc) (strcmp_arg2 sc) value ->
  strcoll_l_result s0 value.
Proof.
  intros s0 sc value (_ & P & Q) FRAME RESULT.
  destruct (binary_callee_args s0 0x552e5 0x552fb sc FRAME) as [ARG1 ARG2].
  change (string_compare_result (sc V_MEM32) (cdecl_arg sc) (binary_arg2 sc) value) in RESULT.
  rewrite ARG1,ARG2,(proj1 FRAME) in RESULT.
  destruct RESULT as (k & K & PREFIX & STOP & VALUE).
  pose proof (proj2 PREFIX) as NZP.
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  pose proof (binary_byte_read s0 0x552e5 0x552fb _ k P NZP) as READP.
  pose proof (binary_byte_read s0 0x552e5 0x552fb _ k Q NZQ) as READQ.
  unfold strcoll_l_result. exists k. split;[exact K|]. split.
  - split.
    + intros i I. rewrite <- (READP i ltac:(clear - I;lia)), <- (READQ i ltac:(clear - I;lia)).
      exact (proj1 PREFIX i I).
    + exact (binary_byte_prefix_back s0 0x552e5 0x552fb _ k P NZP).
  - rewrite <- (READP k (N.le_refl k)), <- (READQ k (N.le_refl k)). split;assumption.
Qed.
