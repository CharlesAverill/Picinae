(* Three-argument wrapper around a bounded comparison with two PIC thunks. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call
  i386_ternary_call i386_strings i386_casecmp i386_casecmp_bounded
  strncasecmp_support strncasecmp_i386 strncasecmp_l_i386 pc_thunk_bx_i386 pc_thunk_ax_i386 tolower_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strncasecmp_l_linked:program:=updateall2 strncasecmp_l_i386 (updateall2 pc_thunk_bx_i386 strncasecmp_linked).
Lemma strncasecmp_l_linked_caller:strncasecmp_l_i386 ⊆2 strncasecmp_l_linked.
Proof.
  intros s a insn H. unfold strncasecmp_l_linked,strncasecmp_linked,updateall2,updateall,
    strncasecmp_l_i386,strncasecmp_i386,pc_thunk_bx_i386,pc_thunk_ax_i386,tolower_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strncasecmp_l_linked_callee:strncasecmp_linked ⊆2 strncasecmp_l_linked.
Proof. intros s a insn H. unfold strncasecmp_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem strncasecmp_l_linked_welltyped:welltyped_prog x86typctx strncasecmp_l_linked.
Proof.
  intros s a. unfold strncasecmp_l_linked,updateall2,updateall.
  destruct (strncasecmp_linked s a) as [[sz q]|] eqn:C.
  - pose proof (strncasecmp_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:B.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite B in WT. exact WT.
    + apply strncasecmp_l_i386.welltyped.
Qed.
Definition strncasecmp_l_got:N:=0xb4f9c.
Definition strncasecmp_l_m1:=unary_m1.
Definition strncasecmp_l_m2 (s0:store):=unary_m2 s0 0x76266.
Definition strncasecmp_l_m5 (s0:store):=ternary_m5 s0 0x76266.
Definition strncasecmp_l_m6 (s0:store):=ternary_entry_memory s0 0x76266 0x76280.
Definition strncasecmp_l_frame:=unary_frame.
Definition strncasecmp_l_child (s0:store):=
  s0[V_MEM32:=strncasecmp_l_m6 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=strncasecmp_l_got].
Definition strncasecmp_l_memory (s0:store) (called:bool) (stop:option N):=
  strncasecmp_memory (strncasecmp_l_child s0) called
    (match stop with None=>None|Some k=>Some (strncasecmp_q s0 k,0x7624f) end).
Definition strncasecmp_l_reference (s0:store) (called:bool) (stop:option N):=s0[V_MEM32:=strncasecmp_l_memory s0 called stop].
Definition strncasecmp_l_avoids (s0:store) (p:N):=forall k,k<strncasecmp_count s0 ->nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 96) 96 (p+k) 1.
Definition strncasecmp_l_pre (s0:store):=models x86typctx s0 /\
  strncasecmp_l_avoids s0 (cdecl_arg s0) /\ strncasecmp_l_avoids s0 (binary_arg2 s0).
Lemma strncasecmp_l_child_frame:forall s0,strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 (strncasecmp_l_child s0).
Proof. intros. unfold strncasecmp_l_frame,unary_frame,strncasecmp_l_child. psimpl. repeat split;reflexivity. Qed.
Lemma strncasecmp_l_m2_stack:forall s0 off,off<=16 ->
  getmem 32 LittleE 4 (strncasecmp_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strncasecmp_l_m2,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma strncasecmp_l_count:forall s0 sc,strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->
  strncasecmp_count sc=strncasecmp_count s0.
Proof.
  intros s0 sc F. exact (proj2 (proj2 (ternary_callee_args s0 0x76266 0x76280 sc F))).
Qed.
Lemma strncasecmp_l_entry_read:forall s0 p k,strncasecmp_l_avoids s0 p ->k<strncasecmp_count s0 ->
  nonzero_prefix (s0 V_MEM32) p k ->getmem 32 LittleE 1 (strncasecmp_l_m6 s0) (p+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 p k A K PREFIX. pose proof (A k K PREFIX) as NO.
  unfold strncasecmp_l_m6,ternary_entry_memory,ternary_m5,ternary_m4,ternary_m3,unary_m2,unary_m1,save_ebx_memory.
  replace (p+k) with ((p+k)+0) by lia.
  rewrite !descending_stack_read with (total:=96) (n:=1) by (try exact NO;lia). reflexivity.
Qed.
Lemma strncasecmp_l_prefix_back:forall s0 p k,strncasecmp_l_avoids s0 p ->k<=strncasecmp_count s0 ->
  nonzero_prefix (strncasecmp_l_m6 s0) p k ->nonzero_prefix (s0 V_MEM32) p k.
Proof.
  intros s0 p k A K PREFIX. refine (conditional_prefix_transfer_bounded
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (p+i))
    (fun i=>getmem 32 LittleE 1 (strncasecmp_l_m6 s0) (p+i)) (strncasecmp_count s0) _ k K PREFIX).
  intros j J P. apply strncasecmp_l_entry_read;assumption.
Qed.
Lemma strncasecmp_l_transport:forall s0 sc k,strncasecmp_l_pre s0 ->
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->k<strncasecmp_count sc ->strncasecmp_prefix sc k ->
  strncasecmp_prefix s0 k /\ strncasecmp_p sc k=strncasecmp_p s0 k /\ strncasecmp_q sc k=strncasecmp_q s0 k.
Proof.
  intros s0 sc k (_ & P & Q) F K PREFIX.
  destruct (ternary_callee_args s0 0x76266 0x76280 sc F) as (ARG1 & ARG2 & COUNT).
  change (strncasecmp_count sc=strncasecmp_count s0) in COUNT. rewrite COUNT in K.
  unfold strncasecmp_prefix,case_equal_prefix in PREFIX. rewrite ARG1,ARG2,(proj1 F) in PREFIX.
  destruct PREFIX as (NP & NQ & EQ).
  pose proof (strncasecmp_l_prefix_back s0 _ k P ltac:(lia) NP) as OP.
  pose proof (strncasecmp_l_prefix_back s0 _ k Q ltac:(lia) NQ) as OQ.
  assert (READP:forall i,i<=k ->getmem 32 LittleE 1 (strncasecmp_l_m6 s0) (cdecl_arg s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)).
  { intros i I. apply strncasecmp_l_entry_read;[exact P|lia|]. intros j J. apply OP;lia. }
  assert (READQ:forall i,i<=k ->getmem 32 LittleE 1 (strncasecmp_l_m6 s0) (binary_arg2 s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+i)).
  { intros i I. apply strncasecmp_l_entry_read;[exact Q|lia|]. intros j J. apply OQ;lia. }
  split.
  - unfold strncasecmp_prefix,case_equal_prefix. split;[exact OP|]. split;[exact OQ|]. intros i I.
    rewrite <- (READP i ltac:(lia)),<- (READQ i ltac:(lia)). exact (EQ i I).
  - unfold strncasecmp_p,strncasecmp_q. rewrite ARG1,ARG2,(proj1 F). split;[apply READP|apply READQ];lia.
Qed.
Lemma strncasecmp_l_callee_pre:forall s0 sc,strncasecmp_l_pre s0 ->models x86typctx sc ->
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->strncasecmp_pre sc.
Proof.
  intros s0 sc (_ & P & Q) MDL F.
  destruct (ternary_callee_args s0 0x76266 0x76280 sc F) as (ARG1 & ARG2 & COUNT).
  change (strncasecmp_count sc=strncasecmp_count s0) in COUNT.
  split;[exact MDL|]. rewrite ARG1,ARG2.
  assert (AVOID:forall p,strncasecmp_l_avoids s0 p ->strncasecmp_avoids sc p).
  { intros p A k K PREFIX. rewrite COUNT in K. rewrite (proj1 F) in PREFIX.
    pose proof (strncasecmp_l_prefix_back s0 p k A ltac:(lia) PREFIX) as ORIGINAL.
    pose proof (A k K ORIGINAL) as NO. rewrite (proj1 (proj2 F)). psimpl.
    eapply descending_stack_subregion;[| |exact NO];lia. }
  split;apply AVOID;assumption.
Qed.
Lemma strncasecmp_memory_entry_ext:forall s1 s2,
  s1 V_MEM32=s2 V_MEM32 ->s1 R_ESP=s2 R_ESP ->s1 R_EBX=s2 R_EBX ->s1 R_ESI=s2 R_ESI ->
  s1 R_EDI=s2 R_EDI ->s1 R_EBP=s2 R_EBP ->strncasecmp_count s1=strncasecmp_count s2 ->
  forall called last,strncasecmp_memory s1 called last=strncasecmp_memory s2 called last.
Proof.
  intros s1 s2 MEM SP BX SI DI BP COUNT called [[arg ra]|];
    unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base,save4_registers;rewrite ?COUNT,MEM,SP,BX,SI,DI,BP;reflexivity.
Qed.
Lemma strncasecmp_l_memory_ext:forall s0 sc called last,
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->sc R_EBX=strncasecmp_l_got ->
  strncasecmp_memory sc called last=strncasecmp_memory (strncasecmp_l_child s0) called last.
Proof.
  intros s0 sc called last F BX.
  pose proof (strncasecmp_l_count s0 sc F) as COUNT.
  pose proof (strncasecmp_l_count s0 (strncasecmp_l_child s0) (strncasecmp_l_child_frame s0)) as CCOUNT.
  apply strncasecmp_memory_entry_ext;try (rewrite COUNT,CCOUNT;reflexivity).
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold strncasecmp_l_child;psimpl;assumption.
Qed.
Lemma strncasecmp_l_outcome:forall s0 sc called stop value,strncasecmp_l_pre s0 ->
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->sc R_EBX=strncasecmp_l_got ->
  strncasecmp_outcome sc called stop value ->strncasecmp_outcome s0 called stop value /\
  strncasecmp_endmem sc called stop=strncasecmp_l_memory s0 called stop.
Proof.
  intros s0 sc called [k|] value PRE F BX OUT.
  - destruct OUT as (K & PREFIX & STOP & VALUE).
    destruct (strncasecmp_l_transport s0 sc k PRE F K PREFIX) as (OP & P & Q).
    pose proof (strncasecmp_l_count s0 sc F) as COUNT. split.
    + unfold strncasecmp_outcome. rewrite COUNT in K. split;[exact K|]. split;[exact OP|]. split.
      * unfold strncasecmp_stop in *. rewrite COUNT,P,Q in STOP. exact STOP.
      * unfold strncasecmp_diff in *. rewrite P,Q in VALUE. exact VALUE.
    + unfold strncasecmp_endmem,strncasecmp_l_memory. rewrite Q. apply strncasecmp_l_memory_ext;assumption.
  - destruct OUT as (ZERO & CALLED & VALUE). split.
    + unfold strncasecmp_outcome. rewrite (strncasecmp_l_count s0 sc F) in ZERO. exact (conj ZERO (conj CALLED VALUE)).
    + unfold strncasecmp_endmem,strncasecmp_l_memory. apply strncasecmp_l_memory_ext;assumption.
Qed.
Lemma strncasecmp_l_after_stack:forall sc called last off,off<=64 ->
  getmem 32 LittleE 4 (strncasecmp_memory sc called last) (off+sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc called [[arg ra]|] off OFF;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base,save4_registers;rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strncasecmp_l_saved_bx:forall s0 called stop,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strncasecmp_l_memory s0 called stop) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 called stop BOUND. unfold strncasecmp_l_memory.
  pose proof (strncasecmp_l_after_stack (strncasecmp_l_child s0) called
    (match stop with None=>None|Some k=>Some (strncasecmp_q s0 k,0x7624f) end) 28 ltac:(lia)) as READ.
  unfold strncasecmp_l_child in READ. psimpl in READ. unfold strncasecmp_l_child. rewrite READ.
  apply ternary_saved_bx;exact BOUND.
Qed.
Lemma strncasecmp_l_outer_stack:forall s0 called stop off,off<=16 ->
  getmem 32 LittleE 4 (strncasecmp_l_memory s0 called stop) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 called stop off OFF. unfold strncasecmp_l_memory.
  pose proof (strncasecmp_l_after_stack (strncasecmp_l_child s0) called
    (match stop with None=>None|Some k=>Some (strncasecmp_q s0 k,0x7624f) end) (32+off) ltac:(lia)) as READ.
  unfold strncasecmp_l_child in READ. psimpl in READ. unfold strncasecmp_l_child.
  rewrite READ. apply ternary_outer_stack;exact OFF.
Qed.
Lemma strncasecmp_l_call_return:forall s0 sc called stop value x se,
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->sc R_EBX=strncasecmp_l_got ->
  strncasecmp_endmem sc called stop=strncasecmp_l_memory s0 called stop ->
  cdecl_returned (strncasecmp_reference sc called stop) value x se ->
  x=Addr 0x76280 /\ strncasecmp_l_frame s0 (strncasecmp_l_memory s0 called stop) 28 se /\
  se R_EBX=strncasecmp_l_got /\ se R_EAX=value.
Proof.
  intros s0 sc called stop value x se F BX MM RETURN.
  pose proof (strncasecmp_outer_stack sc called
    (match stop with None=>None|Some k=>Some (strncasecmp_q sc k,0x7624f) end) 0 ltac:(lia)) as RA.
  rewrite N.add_0_l in RA. change (getmem 32 LittleE 4 (strncasecmp_endmem sc called stop) (sc R_ESP)=
    getmem 32 LittleE 4 (sc V_MEM32) (sc R_ESP)) in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strncasecmp_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold strncasecmp_l_m6 in PC. rewrite ternary_call_address in PC. split;[exact PC|]. split.
  - unfold strncasecmp_l_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
