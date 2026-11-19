(* Linked code and stack snapshots for musl i386 iswblank. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack iswblank_i386 pc_thunk_bx_i386 isblank_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition iswblank_linked : program := updateall2 iswblank_i386 (updateall2 pc_thunk_bx_i386 isblank_i386).
Lemma iswblank_linked_caller : iswblank_i386 ⊆2 iswblank_linked.
Proof.
  intros s a insn H. unfold iswblank_linked,updateall2,updateall,iswblank_i386,pc_thunk_bx_i386,isblank_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma iswblank_linked_isblank : isblank_i386 ⊆2 iswblank_linked.
Proof. intros s a insn H. unfold iswblank_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma iswblank_linked_thunk : pc_thunk_bx_i386 ⊆2 iswblank_linked.
Proof.
  intros s a insn H. unfold iswblank_linked,updateall2,updateall,pc_thunk_bx_i386,isblank_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem iswblank_linked_welltyped : welltyped_prog x86typctx iswblank_linked.
Proof.
  intros s a. unfold iswblank_linked,updateall2,updateall.
  destruct (isblank_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (isblank_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply iswblank_i386.welltyped.
Qed.


Definition iswblank_got:N:=0xb4f9c.
Definition iswblank_m1 (s0:store):=save_ebx_memory s0.
Definition iswblank_m2 (s0:store):=setmem 32 LittleE 4 (iswblank_m1 s0) (msub 32 (s0 R_ESP) 8) 0x4f184.
Definition iswblank_m3 (s0:store):=setmem 32 LittleE 4 (iswblank_m2 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition iswblank_m4 (s0:store):=setmem 32 LittleE 4 (iswblank_m3 s0) (msub 32 (s0 R_ESP) 32) 0x4f196.
Definition iswblank_reference (s0:store):=s0[V_MEM32:=iswblank_m4 s0].
Definition iswblank_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Lemma iswblank_m2_stack:forall s0 off,off<=4 ->
  getmem 32 LittleE 4 (iswblank_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold iswblank_m2,iswblank_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma iswblank_outer_stack:forall s0 off,off<=4 ->
  getmem 32 LittleE 4 (iswblank_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold iswblank_m4,iswblank_m3,iswblank_m2,iswblank_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma iswblank_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (iswblank_m4 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold iswblank_m4,iswblank_m3,iswblank_m2,iswblank_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma iswblank_call_address:forall s0,
  getmem 32 LittleE 4 (iswblank_m4 s0) (msub 32 (s0 R_ESP) 32)=0x4f196.
Proof. intros s0. unfold iswblank_m4. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma iswblank_call_arg:forall s0 sc,iswblank_frame s0 (iswblank_m4 s0) 32 sc ->cdecl_arg sc=cdecl_arg s0.
Proof.
  intros s0 sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. rewrite MEM,SP. psimpl. unfold iswblank_m4,iswblank_m3.
  rewrite deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold cdecl_arg. apply getmem_bound.
Qed.
