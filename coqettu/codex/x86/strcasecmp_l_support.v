(* Nested PIC-call stack for strcasecmp_l -> strcasecmp -> tolower. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_strings i386_casecmp i386_call_pair
  strcasecmp_l_i386 strcasecmp_support strcasecmp_proof strcasecmp_i386 pc_thunk_bx_i386 tolower_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcasecmp_l_linked:program:=updateall2 strcasecmp_l_i386 strcasecmp_linked.
Lemma strcasecmp_l_linked_caller:strcasecmp_l_i386 ⊆2 strcasecmp_l_linked.
Proof.
  intros s a insn H. unfold strcasecmp_l_linked,strcasecmp_linked,updateall2,updateall,
    strcasecmp_l_i386,strcasecmp_i386,pc_thunk_bx_i386,tolower_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strcasecmp_l_linked_strcasecmp:strcasecmp_linked ⊆2 strcasecmp_l_linked.
Proof. intros s a insn H. unfold strcasecmp_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem strcasecmp_l_linked_welltyped:welltyped_prog x86typctx strcasecmp_l_linked.
Proof.
  intros s a. unfold strcasecmp_l_linked,updateall2,updateall.
  destruct (strcasecmp_linked s a) as [[sz q]|] eqn:M.
  - pose proof (strcasecmp_linked_welltyped s a) as WT. rewrite M in WT. exact WT.
  - apply strcasecmp_l_i386.welltyped.
Qed.

Definition strcasecmp_l_got:N:=0xb4f9c.
Definition strcasecmp_l_m1:=unary_m1.
Definition strcasecmp_l_m2 (s0:store):=unary_m2 s0 0x75fc0.
Definition strcasecmp_l_m4 (s0:store):=binary_m4 s0 0x75fc0.
Definition strcasecmp_l_m5 (s0:store):=binary_entry_memory s0 0x75fc0 0x75fd6.
Definition strcasecmp_l_frame:=unary_frame.
Definition strcasecmp_l_child (s0:store):=
  s0[V_MEM32:=strcasecmp_l_m5 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=strcasecmp_l_got].
Definition strcasecmp_l_memory (s0:store) (k:N):=
  strcasecmp_memory (strcasecmp_l_child s0) (Some (strcasecmp_q s0 k,0x75fac)).
Definition strcasecmp_l_reference (s0:store) (k:N):=s0[V_MEM32:=strcasecmp_l_memory s0 k].
Definition strcasecmp_l_avoids (s0:store) (p:N):=forall k,nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 80) 80 (p+k) 1.
Definition strcasecmp_l_pre (s0:store):=models x86typctx s0 /\
  strcasecmp_l_avoids s0 (cdecl_arg s0) /\ strcasecmp_l_avoids s0 (binary_arg2 s0).
Lemma strcasecmp_l_child_frame:forall s0,strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 (strcasecmp_l_child s0).
Proof. intros. unfold strcasecmp_l_frame,unary_frame,strcasecmp_l_child. psimpl. repeat split;reflexivity. Qed.
Lemma strcasecmp_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strcasecmp_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma strcasecmp_l_entry_read:forall s0 p k,strcasecmp_l_avoids s0 p ->nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (strcasecmp_l_m5 s0) (p+k)=getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 p k AVOID PREFIX. pose proof (AVOID k PREFIX) as NO.
  unfold strcasecmp_l_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  replace (p+k) with ((p+k)+0) by lia.
  rewrite !descending_stack_read with (total:=80) (n:=1) by (try exact NO;lia). reflexivity.
Qed.
Lemma strcasecmp_l_prefix_back:forall s0 p k,strcasecmp_l_avoids s0 p ->
  nonzero_prefix (strcasecmp_l_m5 s0) p k ->nonzero_prefix (s0 V_MEM32) p k.
Proof.
  intros s0 p k AVOID PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (p+i))
    (fun i=>getmem 32 LittleE 1 (strcasecmp_l_m5 s0) (p+i)) _ k PREFIX).
  intros j P. apply strcasecmp_l_entry_read;assumption.
Qed.
Lemma strcasecmp_l_transport:forall s0 sc k,strcasecmp_l_pre s0 ->
  strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 sc ->strcasecmp_prefix sc k ->
  strcasecmp_prefix s0 k /\ strcasecmp_p sc k=strcasecmp_p s0 k /\ strcasecmp_q sc k=strcasecmp_q s0 k.
Proof.
  intros s0 sc k (_ & P & Q) F PREFIX.
  destruct (binary_callee_args s0 0x75fc0 0x75fd6 sc F) as [ARG1 ARG2].
  unfold strcasecmp_prefix,case_equal_prefix in PREFIX. rewrite ARG1,ARG2,(proj1 F) in PREFIX.
  destruct PREFIX as (NP & NQ & EQ).
  pose proof (strcasecmp_l_prefix_back s0 _ k P NP) as OP.
  pose proof (strcasecmp_l_prefix_back s0 _ k Q NQ) as OQ.
  assert (READP:forall i,i<=k ->getmem 32 LittleE 1 (strcasecmp_l_m5 s0) (cdecl_arg s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)).
  { intros i I. apply strcasecmp_l_entry_read;[exact P|]. intros j J. apply OP. clear - I J;lia. }
  assert (READQ:forall i,i<=k ->getmem 32 LittleE 1 (strcasecmp_l_m5 s0) (binary_arg2 s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+i)).
  { intros i I. apply strcasecmp_l_entry_read;[exact Q|]. intros j J. apply OQ. clear - I J;lia. }
  split.
  - unfold strcasecmp_prefix,case_equal_prefix. split;[exact OP|]. split;[exact OQ|]. intros i I.
    rewrite <- (READP i ltac:(lia)),<- (READQ i ltac:(lia)). exact (EQ i I).
  - unfold strcasecmp_p,strcasecmp_q. rewrite ARG1,ARG2,(proj1 F). split;[apply READP|apply READQ];lia.
Qed.
Lemma strcasecmp_l_callee_pre:forall s0 sc,strcasecmp_l_pre s0 ->models x86typctx sc ->
  strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 sc ->strcasecmp_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL F.
  destruct (binary_callee_args s0 0x75fc0 0x75fd6 sc F) as [ARG1 ARG2].
  split;[exact MDL|]. rewrite ARG1,ARG2.
  assert (AVOID:forall p,strcasecmp_l_avoids s0 p ->strcasecmp_avoids sc p).
  { intros p A k PREFIX. rewrite (proj1 F) in PREFIX.
    pose proof (strcasecmp_l_prefix_back s0 p k A PREFIX) as ORIGINAL.
    pose proof (A k ORIGINAL) as NO. rewrite (proj1 (proj2 F)). psimpl.
    eapply descending_stack_subregion;[| |exact NO];lia. }
  split;apply AVOID;assumption.
Qed.
Lemma strcasecmp_memory_entry_ext:forall s1 s2,
  s1 V_MEM32=s2 V_MEM32 ->s1 R_ESP=s2 R_ESP ->s1 R_EBX=s2 R_EBX ->s1 R_ESI=s2 R_ESI ->
  s1 R_EDI=s2 R_EDI ->s1 R_EBP=s2 R_EBP ->forall last,strcasecmp_memory s1 last=strcasecmp_memory s2 last.
Proof.
  intros s1 s2 MEM SP BX SI DI BP [[arg ra]|];unfold strcasecmp_memory,case_call_pair,strcasecmp_base,save4_registers;
    rewrite MEM,SP,BX,SI,DI,BP;reflexivity.
Qed.
Lemma strcasecmp_l_callee_memory:forall s0 sc k,
  strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 sc ->sc R_EBX=strcasecmp_l_got ->
  strcasecmp_q sc k=strcasecmp_q s0 k ->
  strcasecmp_memory sc (Some (strcasecmp_q sc k,0x75fac))=strcasecmp_l_memory s0 k.
Proof.
  intros s0 sc k F BX Q. unfold strcasecmp_l_memory. rewrite Q. apply strcasecmp_memory_entry_ext.
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold strcasecmp_l_child;psimpl;assumption.
Qed.
Lemma strcasecmp_l_after_stack:forall sc last off,off<=64 ->
  getmem 32 LittleE 4 (strcasecmp_memory sc last) (off+sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc [[arg ra]|] off OFF;unfold strcasecmp_memory,case_call_pair,strcasecmp_base,save4_registers;
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strcasecmp_l_saved_bx:forall s0 k,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strcasecmp_l_memory s0 k) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 k BOUND. unfold strcasecmp_l_memory.
  pose proof (strcasecmp_l_after_stack (strcasecmp_l_child s0) (Some (strcasecmp_q s0 k,0x75fac)) 28 ltac:(lia)) as READ.
  unfold strcasecmp_l_child in READ. psimpl in READ. unfold strcasecmp_l_child. rewrite READ.
  unfold strcasecmp_l_m5,binary_entry_memory,binary_m4,binary_m3.
  rewrite !deep_saved_word_frame by lia. unfold unary_m2. rewrite deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma strcasecmp_l_outer_stack:forall s0 k off,off<=8 ->
  getmem 32 LittleE 4 (strcasecmp_l_memory s0 k) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 k off OFF. unfold strcasecmp_l_memory.
  pose proof (strcasecmp_l_after_stack (strcasecmp_l_child s0) (Some (strcasecmp_q s0 k,0x75fac)) (32+off) ltac:(lia)) as READ.
  unfold strcasecmp_l_child in READ. psimpl in READ. unfold strcasecmp_l_child. rewrite READ.
  unfold strcasecmp_l_m5,binary_entry_memory,binary_m4,binary_m3.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia.
  rewrite (N.add_comm (s0 R_ESP) off). apply unary_m2_stack;exact OFF.
Qed.
Lemma strcasecmp_l_call_return:forall s0 sc k value x se,
  strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 sc ->sc R_EBX=strcasecmp_l_got ->
  strcasecmp_q sc k=strcasecmp_q s0 k ->
  cdecl_returned (strcasecmp_reference sc k) value x se ->
  x=Addr 0x75fd6 /\ strcasecmp_l_frame s0 (strcasecmp_l_memory s0 k) 28 se /\
  se R_EBX=strcasecmp_l_got /\ se R_EAX=value.
Proof.
  intros s0 sc k value x se F BX Q RETURN.
  pose proof (strcasecmp_l_callee_memory s0 sc k F BX Q) as MM.
  pose proof (strcasecmp_outer_stack sc (Some (strcasecmp_q sc k,0x75fac)) 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strcasecmp_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold strcasecmp_l_m5 in PC. rewrite binary_call_address in PC. split;[exact PC|]. split.
  - unfold strcasecmp_l_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
