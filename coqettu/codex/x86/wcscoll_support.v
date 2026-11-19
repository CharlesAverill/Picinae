(* Exact nested stack and original-memory comparison transport for wcscoll. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_tls_call
  i386_strings i386_stringcmp i386_wstringcmp wcscoll_i386 wcscoll_l_i386 wcscoll_l_support wcscoll_l_proof pc_thunk_bx_i386 wcscmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition wcscoll_linked:program:=updateall2 wcscoll_i386 wcscoll_l_linked.
Lemma wcscoll_linked_caller:wcscoll_i386 ⊆2 wcscoll_linked.
Proof.
  intros s a insn H. unfold wcscoll_linked,wcscoll_l_linked,updateall2,updateall,
    wcscoll_i386,wcscoll_l_i386,pc_thunk_bx_i386,wcscmp_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma wcscoll_linked_callee:wcscoll_l_linked ⊆2 wcscoll_linked.
Proof. intros s a insn H. unfold wcscoll_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem wcscoll_linked_welltyped:welltyped_prog x86typctx wcscoll_linked.
Proof.
  intros s a. unfold wcscoll_linked,updateall2,updateall.
  destruct (wcscoll_l_linked s a) as [[sz q]|] eqn:C.
  - pose proof (wcscoll_l_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - apply wcscoll_i386.welltyped.
Qed.
Definition wcscoll_got:N:=0xb4f9c.
Definition wcscoll_m1:=unary_m1.
Definition wcscoll_m2 (s0:store):=unary_m2 s0 0x55598.
Definition wcscoll_m5 (s0:store):=tls_m5 s0 0x55598.
Definition wcscoll_m6 (s0:store):=tls_entry s0 0x55598 0x555b7.
Definition wcscoll_frame:=unary_frame.
Definition wcscoll_child (s0:store):=s0[V_MEM32:=wcscoll_m6 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=wcscoll_got].
Definition wcscoll_memory (s0:store):=wcscoll_l_memory (wcscoll_child s0).
Definition wcscoll_reference (s0:store):=s0[V_MEM32:=wcscoll_memory s0].
Definition wcscoll_pre (s0:store):=models x86typctx s0 /\ tls_string_avoids s0 4 (cdecl_arg s0) /\
  tls_string_avoids s0 4 (binary_arg2 s0).
Definition wcscoll_result:=wcscoll_l_result.
Lemma wcscoll_child_frame:forall s0,wcscoll_frame s0 (wcscoll_m6 s0) 32 (wcscoll_child s0).
Proof. intros. unfold wcscoll_frame,unary_frame,wcscoll_child. psimpl. repeat split;reflexivity. Qed.
Lemma wcscoll_m2_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (wcscoll_m2 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros;apply unary_m2_stack;assumption. Qed.
Lemma wcscoll_callee_pre:forall s0 sc,wcscoll_pre s0 ->models x86typctx sc ->
  wcscoll_frame s0 (wcscoll_m6 s0) 32 sc ->wcscoll_l_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL F. destruct (tls_callee_args s0 0x55598 0x555b7 sc F) as [ARG1 ARG2].
  unfold wcscoll_l_pre,wcscoll_l_arg2. rewrite ARG1,ARG2. split;[exact MDL|].
  split;eapply tls_entry_avoids;[exact F|exact P|exact F|exact Q].
Qed.
Lemma wcscoll_callee_memory:forall s0 sc,wcscoll_frame s0 (wcscoll_m6 s0) 32 sc ->sc R_EBX=wcscoll_got ->
  wcscoll_l_memory sc=wcscoll_memory s0.
Proof.
  intros s0 sc F BX. destruct (tls_callee_args s0 0x55598 0x555b7 sc F) as [ARG ARG2].
  destruct (tls_callee_args s0 0x55598 0x555b7 (wcscoll_child s0) (wcscoll_child_frame s0)) as [CARG CARG2].
  unfold wcscoll_memory,wcscoll_l_memory. apply binary_memory_entry_ext;try congruence.
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold wcscoll_child;psimpl;assumption.
Qed.
Lemma wcscoll_result_back:forall s0 sc value,wcscoll_pre s0 ->
  wcscoll_frame s0 (wcscoll_m6 s0) 32 sc ->
  wcscoll_l_result sc value ->
  wcscoll_result s0 value.
Proof.
  intros s0 sc value (_ & P & Q) FRAME RESULT.
  destruct (tls_callee_args s0 0x55598 0x555b7 sc FRAME) as [ARG1 ARG2].
  unfold wcscoll_l_result,wcscoll_l_arg2 in RESULT.
  change (wide_string_result (sc V_MEM32) (cdecl_arg sc) (binary_arg2 sc) value) in RESULT.
  rewrite ARG1,ARG2,(proj1 FRAME) in RESULT.
  destruct RESULT as (k & PREFIX & STOP & VALUE).
  pose proof (tls_read_through_prefix s0 0x55598 0x555b7 4 _ k P (proj2 PREFIX)) as READP.
  pose proof (tls_read_through_prefix s0 0x55598 0x555b7 4 _ k Q
    (wide_string_prefix_right _ _ _ _ PREFIX)) as READQ.
  unfold wcscoll_result,wcscoll_l_result,wcscoll_l_arg2. exists k. split.
  - eapply wide_string_prefix_transport;[| |exact PREFIX];intros i I;
      [apply READP|apply READQ];clear - I;lia.
  - rewrite <- (READP k (N.le_refl k)), <- (READQ k (N.le_refl k)). split;assumption.
Qed.

Lemma wcscoll_after_stack:forall sc off,off<=64 ->getmem 32 LittleE 4 (wcscoll_l_memory sc) (off+sc R_ESP)=
  getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof. intros;apply binary_memory_above;assumption. Qed.
Lemma wcscoll_saved_bx:forall s0,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (wcscoll_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold wcscoll_memory. pose proof (wcscoll_after_stack (wcscoll_child s0) 28 ltac:(lia)) as READ.
  unfold wcscoll_child in READ. psimpl in READ. unfold wcscoll_child. rewrite READ. apply tls_saved_bx;exact BOUND.
Qed.
Lemma wcscoll_outer_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (wcscoll_memory s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcscoll_memory. pose proof (wcscoll_after_stack (wcscoll_child s0) (32+off) ltac:(lia)) as READ.
  unfold wcscoll_child in READ. psimpl in READ. unfold wcscoll_child. rewrite READ. apply tls_outer_stack;lia.
Qed.
Lemma wcscoll_call_return:forall s0 sc value x se,wcscoll_frame s0 (wcscoll_m6 s0) 32 sc ->sc R_EBX=wcscoll_got ->
  cdecl_returned (wcscoll_l_reference sc) value x se ->
  x=Addr 0x555b7 /\ wcscoll_frame s0 (wcscoll_memory s0) 28 se /\ se R_EBX=wcscoll_got /\ se R_EAX=value.
Proof.
  intros s0 sc value x se F BX RETURN. pose proof (wcscoll_callee_memory s0 sc F BX) as MM.
  pose proof (wcscoll_l_outer_stack sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,wcscoll_l_reference,binary_reference in RETURN. psimpl in RETURN.
  change (getmem 32 LittleE 4 (wcscoll_l_memory sc) (sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (sc R_ESP)) in RA.
  fold (wcscoll_l_memory sc) in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wcscoll_m6 in PC. rewrite tls_call_address in PC. split;[exact PC|]. split.
  - unfold wcscoll_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
