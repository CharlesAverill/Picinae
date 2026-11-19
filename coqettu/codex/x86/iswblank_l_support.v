(* Nested PIC-call stack for iswblank_l -> iswblank -> isblank. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_unary_call
  iswblank_l_i386 iswblank_support iswblank_i386 pc_thunk_bx_i386 isblank_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition iswblank_l_linked:program:=updateall2 iswblank_l_i386 iswblank_linked.
Lemma iswblank_l_linked_caller:iswblank_l_i386 ⊆2 iswblank_l_linked.
Proof.
  intros s a insn H. unfold iswblank_l_linked,iswblank_linked,updateall2,updateall,
    iswblank_l_i386,iswblank_i386,pc_thunk_bx_i386,isblank_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma iswblank_l_linked_iswblank:iswblank_linked ⊆2 iswblank_l_linked.
Proof. intros s a insn H. unfold iswblank_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem iswblank_l_linked_welltyped:welltyped_prog x86typctx iswblank_l_linked.
Proof.
  intros s a. unfold iswblank_l_linked,updateall2,updateall.
  destruct (iswblank_linked s a) as [[sz q]|] eqn:M.
  - pose proof (iswblank_linked_welltyped s a) as WT. rewrite M in WT. exact WT.
  - apply iswblank_l_i386.welltyped.
Qed.

Definition iswblank_l_got:N:=0xb4f9c.
Definition iswblank_l_m1:=unary_m1.
Definition iswblank_l_m2 (s0:store):=unary_m2 s0 0x4f1a1.
Definition iswblank_l_m3 (s0:store):=unary_m3 s0 0x4f1a1.
Definition iswblank_l_m4 (s0:store):=unary_memory s0 0x4f1a1 0x4f1b3.
Definition iswblank_l_m5 (s0:store):=
  setmem 32 LittleE 4 (iswblank_l_m4 s0) (msub 32 (s0 R_ESP) 36) iswblank_l_got.
Definition iswblank_l_m6 (s0:store):=
  setmem 32 LittleE 4 (iswblank_l_m5 s0) (msub 32 (s0 R_ESP) 40) 0x4f184.
Definition iswblank_l_m7 (s0:store):=
  setmem 32 LittleE 4 (iswblank_l_m6 s0) (msub 32 (s0 R_ESP) 60) (cdecl_arg s0).
Definition iswblank_l_memory (s0:store):=
  setmem 32 LittleE 4 (iswblank_l_m7 s0) (msub 32 (s0 R_ESP) 64) 0x4f196.
Definition iswblank_l_reference (s0:store):=s0[V_MEM32:=iswblank_l_memory s0].
Definition iswblank_l_frame:=unary_frame.
Lemma iswblank_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (iswblank_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma iswblank_l_callee_memory:forall s0 sc,
  iswblank_l_frame s0 (iswblank_l_m4 s0) 32 sc ->sc R_EBX=iswblank_l_got ->
  iswblank_m4 sc=iswblank_l_memory s0.
Proof.
  intros s0 sc FRAME BX. pose proof (unary_callee_arg s0 0x4f1a1 0x4f1b3 sc FRAME) as ARG.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold iswblank_m4,iswblank_m3,iswblank_m2,iswblank_m1,save_ebx_memory.
  rewrite ARG,MEM,SP,BX. psimpl.
  reflexivity.
Qed.
Lemma iswblank_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (iswblank_l_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold iswblank_l_memory,iswblank_l_m7,iswblank_l_m6,iswblank_l_m5.
  rewrite !deep_saved_word_frame by lia. apply unary_saved_bx;exact BOUND.
Qed.
Lemma iswblank_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (iswblank_l_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold iswblank_l_memory,iswblank_l_m7,iswblank_l_m6,iswblank_l_m5.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia.
  rewrite (N.add_comm (s0 R_ESP) off). apply unary_outer_stack;exact OFF.
Qed.
Lemma iswblank_l_call_return:forall s0 sc x se value,
  iswblank_l_frame s0 (iswblank_l_m4 s0) 32 sc ->sc R_EBX=iswblank_l_got ->
  cdecl_returned (iswblank_reference sc) (value (cdecl_arg sc)) x se ->
  x=Addr 0x4f1b3 /\ iswblank_l_frame s0 (iswblank_l_memory s0) 28 se /\
  se R_EBX=iswblank_l_got /\ se R_EAX=value (cdecl_arg s0).
Proof.
  intros s0 sc x se value FRAME BX RETURN.
  pose proof (unary_callee_arg s0 0x4f1a1 0x4f1b3 sc FRAME) as ARG.
  pose proof (iswblank_l_callee_memory s0 sc FRAME BX) as CALLEEMEM.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,iswblank_reference in RETURN. psimpl in RETURN.
  pose proof (iswblank_outer_stack sc 0 ltac:(lia)) as ADDRESS.
  rewrite N.add_0_l in ADDRESS.
  rewrite ADDRESS,ARG,CALLEEMEM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold iswblank_l_m4 in PC. rewrite unary_call_address in PC. split;[exact PC|]. split.
  - unfold iswblank_l_frame,unary_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE.
    psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
