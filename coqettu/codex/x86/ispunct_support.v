(* Linked code and shared unary stack interface for ispunct. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_unary_call ispunct_i386 pc_thunk_bx_i386 isalnum_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ispunct_linked : program := updateall2 ispunct_i386 (updateall2 pc_thunk_bx_i386 isalnum_i386).
Lemma ispunct_linked_caller : ispunct_i386 ⊆2 ispunct_linked.
Proof.
  intros s a insn H. unfold ispunct_linked,updateall2,updateall,ispunct_i386,pc_thunk_bx_i386,isalnum_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma ispunct_linked_isalnum : isalnum_i386 ⊆2 ispunct_linked.
Proof. intros s a insn H. unfold ispunct_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma ispunct_linked_thunk : pc_thunk_bx_i386 ⊆2 ispunct_linked.
Proof.
  intros s a insn H. unfold ispunct_linked,updateall2,updateall,pc_thunk_bx_i386,isalnum_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem ispunct_linked_welltyped : welltyped_prog x86typctx ispunct_linked.
Proof.
  intros s a. unfold ispunct_linked,updateall2,updateall.
  destruct (isalnum_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (isalnum_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply ispunct_i386.welltyped.
Qed.



Definition ispunct_got:N:=0xb4f9c.
Definition ispunct_m1:=unary_m1.
Definition ispunct_m2 (s0:store):=unary_m2 s0 0x4f004.
Definition ispunct_m3 (s0:store):=unary_m3 s0 0x4f004.
Definition ispunct_m4 (s0:store):=unary_memory s0 0x4f004 0x4f027.
Definition ispunct_frame:=unary_frame.
Definition ispunct_graph (c:N):bool:=(33<=?c)&&(c<=?126).
Definition ispunct_memory (s0:store):=
  if ispunct_graph (cdecl_arg s0) then ispunct_m4 s0 else ispunct_m2 s0.
Definition ispunct_reference (s0:store):=s0[V_MEM32:=ispunct_memory s0].
Lemma ispunct_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (ispunct_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma ispunct_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (ispunct_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold ispunct_memory. destruct (ispunct_graph (cdecl_arg s0)).
  - apply unary_saved_bx;exact BOUND.
  - unfold ispunct_m2,unary_m2,unary_m1.
    rewrite deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma ispunct_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (ispunct_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold ispunct_memory. destruct (ispunct_graph (cdecl_arg s0)).
  - apply unary_outer_stack;exact OFF.
  - apply unary_m2_stack;exact OFF.
Qed.
