(* Linked code and shared unary stack interface for islower_l. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_unary_call islower_l_i386 pc_thunk_bx_i386 islower_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition islower_l_linked : program := updateall2 islower_l_i386 (updateall2 pc_thunk_bx_i386 islower_i386).
Lemma islower_l_linked_caller : islower_l_i386 ⊆2 islower_l_linked.
Proof.
  intros s a insn H. unfold islower_l_linked,updateall2,updateall,islower_l_i386,pc_thunk_bx_i386,islower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma islower_l_linked_islower : islower_i386 ⊆2 islower_l_linked.
Proof. intros s a insn H. unfold islower_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma islower_l_linked_thunk : pc_thunk_bx_i386 ⊆2 islower_l_linked.
Proof.
  intros s a insn H. unfold islower_l_linked,updateall2,updateall,pc_thunk_bx_i386,islower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem islower_l_linked_welltyped : welltyped_prog x86typctx islower_l_linked.
Proof.
  intros s a. unfold islower_l_linked,updateall2,updateall.
  destruct (islower_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (islower_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply islower_l_i386.welltyped.
Qed.



Definition islower_l_got:N:=0xb4f9c.
Definition islower_l_m1:=unary_m1.
Definition islower_l_m2 (s0:store):=unary_m2 s0 0x4efb7.
Definition islower_l_m3 (s0:store):=unary_m3 s0 0x4efb7.
Definition islower_l_m4 (s0:store):=unary_memory s0 0x4efb7 0x4efc9.
Definition islower_l_frame:=unary_frame.
Definition islower_l_reference (s0:store):=unary_reference s0 0x4efb7 0x4efc9.
Lemma islower_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (islower_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma islower_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (islower_l_m4 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof. intros. apply unary_saved_bx;assumption. Qed.
Lemma islower_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (islower_l_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_outer_stack;assumption. Qed.
