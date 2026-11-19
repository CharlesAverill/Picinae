(* Exact nested stack and original-memory comparison transport for strcoll. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_tls_call
  i386_strings i386_stringcmp i386_wstringcmp strcoll_i386 strcoll_l_i386 strcoll_l_support strcoll_l_proof pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strcoll_linked:program:=updateall2 strcoll_i386 strcoll_l_linked.
Lemma strcoll_linked_caller:strcoll_i386 ⊆2 strcoll_linked.
Proof.
  intros s a insn H. unfold strcoll_linked,strcoll_l_linked,updateall2,updateall,
    strcoll_i386,strcoll_l_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strcoll_linked_callee:strcoll_l_linked ⊆2 strcoll_linked.
Proof. intros s a insn H. unfold strcoll_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem strcoll_linked_welltyped:welltyped_prog x86typctx strcoll_linked.
Proof.
  intros s a. unfold strcoll_linked,updateall2,updateall.
  destruct (strcoll_l_linked s a) as [[sz q]|] eqn:C.
  - pose proof (strcoll_l_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - apply strcoll_i386.welltyped.
Qed.
Definition strcoll_got:N:=0xb4f9c.
Definition strcoll_m1:=unary_m1.
Definition strcoll_m2 (s0:store):=unary_m2 s0 0x55306.
Definition strcoll_m5 (s0:store):=tls_m5 s0 0x55306.
Definition strcoll_m6 (s0:store):=tls_entry s0 0x55306 0x55325.
Definition strcoll_frame:=unary_frame.
Definition strcoll_child (s0:store):=s0[V_MEM32:=strcoll_m6 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=strcoll_got].
Definition strcoll_memory (s0:store):=strcoll_l_memory (strcoll_child s0).
Definition strcoll_reference (s0:store):=s0[V_MEM32:=strcoll_memory s0].
Definition strcoll_pre (s0:store):=models x86typctx s0 /\ tls_string_avoids s0 1 (cdecl_arg s0) /\
  tls_string_avoids s0 1 (binary_arg2 s0).
Definition strcoll_result:=strcoll_l_result.
Lemma strcoll_child_frame:forall s0,strcoll_frame s0 (strcoll_m6 s0) 32 (strcoll_child s0).
Proof. intros. unfold strcoll_frame,unary_frame,strcoll_child. psimpl. repeat split;reflexivity. Qed.
Lemma strcoll_m2_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (strcoll_m2 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros;apply unary_m2_stack;assumption. Qed.
Lemma strcoll_callee_pre:forall s0 sc,strcoll_pre s0 ->models x86typctx sc ->
  strcoll_frame s0 (strcoll_m6 s0) 32 sc ->strcoll_l_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL F. destruct (tls_callee_args s0 0x55306 0x55325 sc F) as [ARG1 ARG2].
  unfold strcoll_l_pre,strcoll_l_arg2. rewrite ARG1,ARG2. split;[exact MDL|].
  split;eapply tls_entry_avoids;[exact F|exact P|exact F|exact Q].
Qed.
Lemma strcoll_callee_memory:forall s0 sc,strcoll_frame s0 (strcoll_m6 s0) 32 sc ->sc R_EBX=strcoll_got ->
  strcoll_l_memory sc=strcoll_memory s0.
Proof.
  intros s0 sc F BX. destruct (tls_callee_args s0 0x55306 0x55325 sc F) as [ARG ARG2].
  destruct (tls_callee_args s0 0x55306 0x55325 (strcoll_child s0) (strcoll_child_frame s0)) as [CARG CARG2].
  unfold strcoll_memory,strcoll_l_memory. apply binary_memory_entry_ext;try congruence.
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold strcoll_child;psimpl;assumption.
Qed.
Lemma strcoll_result_back:forall s0 sc value,strcoll_pre s0 ->
  strcoll_frame s0 (strcoll_m6 s0) 32 sc ->
  strcoll_l_result sc value ->
  strcoll_result s0 value.
Proof.
  intros s0 sc value (_ & P & Q) FRAME RESULT.
  destruct (tls_callee_args s0 0x55306 0x55325 sc FRAME) as [ARG1 ARG2].
  unfold strcoll_l_result,strcoll_l_arg2 in RESULT.
  change (string_compare_result (sc V_MEM32) (cdecl_arg sc) (binary_arg2 sc) value) in RESULT.
  rewrite ARG1,ARG2,(proj1 FRAME) in RESULT.
  destruct RESULT as (k & K & PREFIX & STOP & VALUE).
  pose proof (proj2 PREFIX) as NZP.
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  apply (proj2 (call_prefix_byte _ _ _)) in NZP.
  apply (proj2 (call_prefix_byte _ _ _)) in NZQ.
  pose proof (tls_read_through_prefix s0 0x55306 0x55325 1 _ k P NZP) as READP. setoid_rewrite N.mul_1_l in READP.
  pose proof (tls_read_through_prefix s0 0x55306 0x55325 1 _ k Q NZQ) as READQ. setoid_rewrite N.mul_1_l in READQ.
  unfold strcoll_result,strcoll_l_result,strcoll_l_arg2. exists k. split;[exact K|]. split.
  - split.
    + intros i I. rewrite <- (READP i ltac:(clear - I;lia)), <- (READQ i ltac:(clear - I;lia)).
      exact (proj1 PREFIX i I).
    + apply (proj1 (call_prefix_byte _ _ _)). exact (tls_prefix_back s0 0x55306 0x55325 1 _ k P NZP).
  - rewrite <- (READP k (N.le_refl k)), <- (READQ k (N.le_refl k)). split;assumption.
Qed.

Lemma strcoll_after_stack:forall sc off,off<=64 ->getmem 32 LittleE 4 (strcoll_l_memory sc) (off+sc R_ESP)=
  getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof. intros;apply binary_memory_above;assumption. Qed.
Lemma strcoll_saved_bx:forall s0,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (strcoll_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold strcoll_memory. pose proof (strcoll_after_stack (strcoll_child s0) 28 ltac:(lia)) as READ.
  unfold strcoll_child in READ. psimpl in READ. unfold strcoll_child. rewrite READ. apply tls_saved_bx;exact BOUND.
Qed.
Lemma strcoll_outer_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (strcoll_memory s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strcoll_memory. pose proof (strcoll_after_stack (strcoll_child s0) (32+off) ltac:(lia)) as READ.
  unfold strcoll_child in READ. psimpl in READ. unfold strcoll_child. rewrite READ. apply tls_outer_stack;lia.
Qed.
Lemma strcoll_call_return:forall s0 sc value x se,strcoll_frame s0 (strcoll_m6 s0) 32 sc ->sc R_EBX=strcoll_got ->
  cdecl_returned (strcoll_l_reference sc) value x se ->
  x=Addr 0x55325 /\ strcoll_frame s0 (strcoll_memory s0) 28 se /\ se R_EBX=strcoll_got /\ se R_EAX=value.
Proof.
  intros s0 sc value x se F BX RETURN. pose proof (strcoll_callee_memory s0 sc F BX) as MM.
  pose proof (strcoll_l_outer_stack sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strcoll_l_reference,binary_reference in RETURN. psimpl in RETURN.
  change (getmem 32 LittleE 4 (strcoll_l_memory sc) (sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (sc R_ESP)) in RA.
  fold (strcoll_l_memory sc) in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold strcoll_m6 in PC. rewrite tls_call_address in PC. split;[exact PC|]. split.
  - unfold strcoll_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
