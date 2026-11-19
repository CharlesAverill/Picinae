(* Nested PIC-call stack for ispunct_l -> ispunct -> isalnum. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_unary_call
  ispunct_l_i386 ispunct_support ispunct_i386 pc_thunk_bx_i386 isalnum_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ispunct_l_linked:program:=updateall2 ispunct_l_i386 ispunct_linked.
Lemma ispunct_l_linked_caller:ispunct_l_i386 ⊆2 ispunct_l_linked.
Proof.
  intros s a insn H. unfold ispunct_l_linked,ispunct_linked,updateall2,updateall,
    ispunct_l_i386,ispunct_i386,pc_thunk_bx_i386,isalnum_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma ispunct_l_linked_ispunct:ispunct_linked ⊆2 ispunct_l_linked.
Proof. intros s a insn H. unfold ispunct_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem ispunct_l_linked_welltyped:welltyped_prog x86typctx ispunct_l_linked.
Proof.
  intros s a. unfold ispunct_l_linked,updateall2,updateall.
  destruct (ispunct_linked s a) as [[sz q]|] eqn:M.
  - pose proof (ispunct_linked_welltyped s a) as WT. rewrite M in WT. exact WT.
  - apply ispunct_l_i386.welltyped.
Qed.

Definition ispunct_l_got:N:=0xb4f9c.
Definition ispunct_l_m1:=unary_m1.
Definition ispunct_l_m2 (s0:store):=unary_m2 s0 0x4f03a.
Definition ispunct_l_m3 (s0:store):=unary_m3 s0 0x4f03a.
Definition ispunct_l_m4 (s0:store):=unary_memory s0 0x4f03a 0x4f04c.
Definition ispunct_l_m5 (s0:store):=
  setmem 32 LittleE 4 (ispunct_l_m4 s0) (msub 32 (s0 R_ESP) 36) ispunct_l_got.
Definition ispunct_l_m6 (s0:store):=
  setmem 32 LittleE 4 (ispunct_l_m5 s0) (msub 32 (s0 R_ESP) 40) 0x4f004.
Definition ispunct_l_m7 (s0:store):=
  setmem 32 LittleE 4 (ispunct_l_m6 s0) (msub 32 (s0 R_ESP) 60) (cdecl_arg s0).
Definition ispunct_l_m8 (s0:store):=
  setmem 32 LittleE 4 (ispunct_l_m7 s0) (msub 32 (s0 R_ESP) 64) 0x4f027.
Definition ispunct_l_memory (s0:store):=
  if ispunct_graph (cdecl_arg s0) then ispunct_l_m8 s0 else ispunct_l_m6 s0.
Definition ispunct_l_reference (s0:store):=s0[V_MEM32:=ispunct_l_memory s0].
Definition ispunct_l_frame:=unary_frame.
Lemma ispunct_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (ispunct_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma ispunct_l_callee_memory:forall s0 sc,
  ispunct_l_frame s0 (ispunct_l_m4 s0) 32 sc ->sc R_EBX=ispunct_l_got ->
  ispunct_memory sc=ispunct_l_memory s0.
Proof.
  intros s0 sc FRAME BX. pose proof (unary_callee_arg s0 0x4f03a 0x4f04c sc FRAME) as ARG.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold ispunct_memory,ispunct_l_memory. rewrite ARG.
  destruct (ispunct_graph (cdecl_arg s0)).
  - unfold ispunct_m4,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
    rewrite ARG,MEM,SP,BX. psimpl. reflexivity.
  - unfold ispunct_m2,unary_m2,unary_m1,save_ebx_memory.
    rewrite MEM,SP,BX. psimpl. reflexivity.
Qed.
Lemma ispunct_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (ispunct_l_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold ispunct_l_memory. destruct (ispunct_graph (cdecl_arg s0));
    unfold ispunct_l_m8,ispunct_l_m7,ispunct_l_m6,ispunct_l_m5.
  all: rewrite !deep_saved_word_frame by lia;apply unary_saved_bx;exact BOUND.
Qed.
Lemma ispunct_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (ispunct_l_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold ispunct_l_memory. destruct (ispunct_graph (cdecl_arg s0));
    unfold ispunct_l_m8,ispunct_l_m7,ispunct_l_m6,ispunct_l_m5.
  all: rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia.
  all: rewrite (N.add_comm (s0 R_ESP) off);apply unary_outer_stack;exact OFF.
Qed.
Lemma ispunct_l_call_return:forall s0 sc x se value,
  ispunct_l_frame s0 (ispunct_l_m4 s0) 32 sc ->sc R_EBX=ispunct_l_got ->
  cdecl_returned (ispunct_reference sc) (value (cdecl_arg sc)) x se ->
  x=Addr 0x4f04c /\ ispunct_l_frame s0 (ispunct_l_memory s0) 28 se /\
  se R_EBX=ispunct_l_got /\ se R_EAX=value (cdecl_arg s0).
Proof.
  intros s0 sc x se value FRAME BX RETURN.
  pose proof (unary_callee_arg s0 0x4f03a 0x4f04c sc FRAME) as ARG.
  pose proof (ispunct_l_callee_memory s0 sc FRAME BX) as CALLEEMEM.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,ispunct_reference in RETURN. psimpl in RETURN.
  pose proof (ispunct_outer_stack sc 0 ltac:(lia)) as ADDRESS.
  rewrite N.add_0_l in ADDRESS.
  rewrite ADDRESS,ARG,CALLEEMEM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold ispunct_l_m4 in PC. rewrite unary_call_address in PC. split;[exact PC|]. split.
  - unfold ispunct_l_frame,unary_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE.
    psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
