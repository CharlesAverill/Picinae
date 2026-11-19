(* Linked code and exact stack snapshots for musl i386 bcmp. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_compare bcmp_i386 pc_thunk_bx_i386 memcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition bcmp_linked : program := updateall2 bcmp_i386 (updateall2 pc_thunk_bx_i386 memcmp_i386).
Lemma bcmp_linked_caller : bcmp_i386 ⊆2 bcmp_linked.
Proof.
  intros s a insn H. unfold bcmp_linked,updateall2,updateall,bcmp_i386,pc_thunk_bx_i386,memcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma bcmp_linked_memcmp : memcmp_i386 ⊆2 bcmp_linked.
Proof. intros s a insn H. unfold bcmp_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma bcmp_linked_thunk : pc_thunk_bx_i386 ⊆2 bcmp_linked.
Proof.
  intros s a insn H. unfold bcmp_linked,updateall2,updateall,pc_thunk_bx_i386,memcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem bcmp_linked_welltyped : welltyped_prog x86typctx bcmp_linked.
Proof.
  intros s a. unfold bcmp_linked,updateall2,updateall.
  destruct (memcmp_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (memcmp_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply bcmp_i386.welltyped.
Qed.

Definition bcmp_arg2 (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition bcmp_count (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition bcmp_got : N := 0xb4f9c.
Definition bcmp_m1 (s0:store) := save_ebx_memory s0.
Definition bcmp_m2 (s0:store) := setmem 32 LittleE 4 (bcmp_m1 s0) (msub 32 (s0 R_ESP) 8) 0x75d23.
Definition bcmp_m3 (s0:store) := setmem 32 LittleE 4 (bcmp_m2 s0) (msub 32 (s0 R_ESP) 20) (bcmp_count s0).
Definition bcmp_m4 (s0:store) := setmem 32 LittleE 4 (bcmp_m3 s0) (msub 32 (s0 R_ESP) 24) (bcmp_arg2 s0).
Definition bcmp_m5 (s0:store) := setmem 32 LittleE 4 (bcmp_m4 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition bcmp_m6 (s0:store) := setmem 32 LittleE 4 (bcmp_m5 s0) (msub 32 (s0 R_ESP) 32) 0x75d3d.
Definition bcmp_m7 (s0:store) := setmem 32 LittleE 4 (bcmp_m6 s0) (msub 32 (s0 R_ESP) 36) bcmp_got.
Definition bcmp_reference (s0:store) := s0[V_MEM32:=bcmp_m7 s0].
Definition bcmp_frame (s0:store) (m:memory) (depth:N) (s:store) :=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.

Lemma bcmp_m6_arg1 : forall s0,
  getmem 32 LittleE 4 (bcmp_m6 s0) (msub 32 (s0 R_ESP) 28)=cdecl_arg s0.
Proof.
  intros s0. unfold bcmp_m6,bcmp_m5.
  rewrite deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold cdecl_arg. apply getmem_bound.
Qed.
Lemma bcmp_m6_arg2 : forall s0,
  getmem 32 LittleE 4 (bcmp_m6 s0) (msub 32 (s0 R_ESP) 24)=bcmp_arg2 s0.
Proof.
  intros s0. unfold bcmp_m6,bcmp_m5,bcmp_m4.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold bcmp_arg2. apply getmem_bound.
Qed.
Lemma bcmp_m6_count : forall s0,
  getmem 32 LittleE 4 (bcmp_m6 s0) (msub 32 (s0 R_ESP) 20)=bcmp_count s0.
Proof.
  intros s0. unfold bcmp_m6,bcmp_m5,bcmp_m4,bcmp_m3.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold bcmp_count. apply getmem_bound.
Qed.
Lemma bcmp_m7_call_address : forall s0,
  getmem 32 LittleE 4 (bcmp_m7 s0) (msub 32 (s0 R_ESP) 32)=0x75d3d.
Proof.
  intros s0. unfold bcmp_m7,bcmp_m6.
  rewrite deep_saved_word_frame by lia. rewrite getmem_setmem by lia. reflexivity.
Qed.
Lemma bcmp_m7_saved_bx : forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (bcmp_m7 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold bcmp_m7,bcmp_m6,bcmp_m5,bcmp_m4,bcmp_m3,bcmp_m2,bcmp_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load. exact BOUND.
Qed.
Lemma bcmp_outer_stack : forall s0 off,off<=12 ->
  getmem 32 LittleE 4 (bcmp_m7 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold bcmp_m7,bcmp_m6,bcmp_m5,bcmp_m4,bcmp_m3,bcmp_m2,bcmp_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)). rewrite !deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma bcmp_m6_byte : forall s0 p n i,
  ~overlap 32 (msub 32 (s0 R_ESP) 36) 36 p n -> i<n ->
  getmem 32 LittleE 1 (bcmp_m6 s0) (p+i)=getmem 32 LittleE 1 (s0 V_MEM32) (p+i).
Proof.
  intros s0 p n i NO I. unfold bcmp_m6,bcmp_m5,bcmp_m4,bcmp_m3,bcmp_m2,bcmp_m1,save_ebx_memory.
  rewrite !deep_stack_byte with (n:=n) by (first [exact NO|exact I|lia]). reflexivity.
Qed.

Lemma bcmp_m2_stack : forall s0 off,off<=12 ->
  getmem 32 LittleE 4 (bcmp_m2 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold bcmp_m2,bcmp_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)). rewrite !deep_stack_word_frame by lia. reflexivity.
Qed.
