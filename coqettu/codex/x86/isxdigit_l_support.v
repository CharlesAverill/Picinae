(* Linked code and shared unary stack interface for isxdigit_l. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_unary_call isxdigit_l_i386 pc_thunk_bx_i386 isxdigit_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition isxdigit_l_linked : program := updateall2 isxdigit_l_i386 (updateall2 pc_thunk_bx_i386 isxdigit_i386).
Lemma isxdigit_l_linked_caller : isxdigit_l_i386 ⊆2 isxdigit_l_linked.
Proof.
  intros s a insn H. unfold isxdigit_l_linked,updateall2,updateall,isxdigit_l_i386,pc_thunk_bx_i386,isxdigit_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma isxdigit_l_linked_isxdigit : isxdigit_i386 ⊆2 isxdigit_l_linked.
Proof. intros s a insn H. unfold isxdigit_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma isxdigit_l_linked_thunk : pc_thunk_bx_i386 ⊆2 isxdigit_l_linked.
Proof.
  intros s a insn H. unfold isxdigit_l_linked,updateall2,updateall,pc_thunk_bx_i386,isxdigit_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem isxdigit_l_linked_welltyped : welltyped_prog x86typctx isxdigit_l_linked.
Proof.
  intros s a. unfold isxdigit_l_linked,updateall2,updateall.
  destruct (isxdigit_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (isxdigit_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply isxdigit_l_i386.welltyped.
Qed.



Definition isxdigit_l_got:N:=0xb4f9c.
Definition isxdigit_l_m1:=unary_m1.
Definition isxdigit_l_m2 (s0:store):=unary_m2 s0 0x4f616.
Definition isxdigit_l_m3 (s0:store):=unary_m3 s0 0x4f616.
Definition isxdigit_l_m4 (s0:store):=unary_memory s0 0x4f616 0x4f628.
Definition isxdigit_l_frame:=unary_frame.
Definition isxdigit_l_reference (s0:store):=unary_reference s0 0x4f616 0x4f628.
Lemma isxdigit_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (isxdigit_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma isxdigit_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (isxdigit_l_m4 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof. intros. apply unary_saved_bx;assumption. Qed.
Lemma isxdigit_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (isxdigit_l_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_outer_stack;assumption. Qed.
