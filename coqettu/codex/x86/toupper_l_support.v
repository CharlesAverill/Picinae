(* Linked code and shared unary stack interface for toupper_l. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_unary_call toupper_l_i386 pc_thunk_bx_i386 toupper_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition toupper_l_linked : program := updateall2 toupper_l_i386 (updateall2 pc_thunk_bx_i386 toupper_i386).
Lemma toupper_l_linked_caller : toupper_l_i386 ⊆2 toupper_l_linked.
Proof.
  intros s a insn H. unfold toupper_l_linked,updateall2,updateall,toupper_l_i386,pc_thunk_bx_i386,toupper_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma toupper_l_linked_toupper : toupper_i386 ⊆2 toupper_l_linked.
Proof. intros s a insn H. unfold toupper_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma toupper_l_linked_thunk : pc_thunk_bx_i386 ⊆2 toupper_l_linked.
Proof.
  intros s a insn H. unfold toupper_l_linked,updateall2,updateall,pc_thunk_bx_i386,toupper_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem toupper_l_linked_welltyped : welltyped_prog x86typctx toupper_l_linked.
Proof.
  intros s a. unfold toupper_l_linked,updateall2,updateall.
  destruct (toupper_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (toupper_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply toupper_l_i386.welltyped.
Qed.



Definition toupper_l_got:N:=0xb4f9c.
Definition toupper_l_m1:=unary_m1.
Definition toupper_l_m2 (s0:store):=unary_m2 s0 0x4f67a.
Definition toupper_l_m3 (s0:store):=unary_m3 s0 0x4f67a.
Definition toupper_l_m4 (s0:store):=unary_memory s0 0x4f67a 0x4f68c.
Definition toupper_l_frame:=unary_frame.
Definition toupper_l_reference (s0:store):=unary_reference s0 0x4f67a 0x4f68c.
Lemma toupper_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (toupper_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma toupper_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (toupper_l_m4 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof. intros. apply unary_saved_bx;assumption. Qed.
Lemma toupper_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (toupper_l_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_outer_stack;assumption. Qed.
