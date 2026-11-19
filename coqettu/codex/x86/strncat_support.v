(* Exact three-register/PIC/strlen stack and bounded append support. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call i386_binary_call i386_ternary_call
  i386_strings i386_memory i386_byte_copy i386_search_arith strncat_i386 strlen_i386 pc_thunk_bx_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strncat_linked : program := updateall2 strncat_i386 (updateall2 pc_thunk_bx_i386 strlen_i386).
Lemma strncat_linked_caller : strncat_i386 ⊆2 strncat_linked.
Proof.
  intros s a insn H. unfold strncat_linked,updateall2,updateall,strncat_i386,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strncat_linked_strlen:strlen_i386 ⊆2 strncat_linked.
Proof.
  intros s a insn H. unfold strncat_linked,updateall2,updateall,strlen_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strncat_linked_thunk : pc_thunk_bx_i386 ⊆2 strncat_linked.
Proof.
  intros s a insn H. unfold strncat_linked,updateall2,updateall,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strncat_linked_welltyped:welltyped_prog x86typctx strncat_linked.
Proof.
  intros s a. unfold strncat_linked,updateall2,updateall.
  destruct (strlen_i386 s a) as [[sz q]|] eqn:L.
  - pose proof (strlen_i386.welltyped s a) as WT. rewrite L in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strncat_i386.welltyped.
Qed.
Definition strncat_p:=cdecl_arg.
Definition strncat_q:=binary_arg2.
Definition strncat_count:=ternary_arg3.
Definition strncat_got:N:=0xb4f9c.
Definition strncat_m1 (s0:store):=setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) (s0 R_EDI).
Definition strncat_m2 (s0:store):=setmem 32 LittleE 4 (strncat_m1 s0) (msub 32 (s0 R_ESP) 8) (s0 R_ESI).
Definition strncat_m3 (s0:store):=setmem 32 LittleE 4 (strncat_m2 s0) (msub 32 (s0 R_ESP) 12) (s0 R_EBX).
Definition strncat_m4 (s0:store):=setmem 32 LittleE 4 (strncat_m3 s0) (msub 32 (s0 R_ESP) 16) 0x3f56c.
Definition strncat_m5 (s0:store):=setmem 32 LittleE 4 (strncat_m4 s0) (msub 32 (s0 R_ESP) 28) (strncat_p s0).
Definition strncat_m6 (s0:store):=setmem 32 LittleE 4 (strncat_m5 s0) (msub 32 (s0 R_ESP) 32) 0x3f57f.
Definition strncat_memory (s0:store) (d k:N):=copy_bytes (s0 V_MEM32) (strncat_q s0) (strncat_p s0+d) k (strncat_m6 s0).
Definition strncat_endmem (s0:store) (d k:N):=copy_terminated (s0 V_MEM32) (strncat_q s0) (strncat_p s0+d) k (strncat_m6 s0).
Definition strncat_reference (s0:store) (d k:N):=s0[V_MEM32:=strncat_endmem s0 d k].
Definition strncat_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\ s R_EBP=s0 R_EBP /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strncat_pre (s0:store):=models x86typctx s0 /\
  (forall d,nonzero_prefix (s0 V_MEM32) (strncat_p s0) d ->
    ~overlap 32 (msub 32 (s0 R_ESP) 32) 32 (strncat_p s0+d) 4) /\
  forall d k,first_nul (s0 V_MEM32) (strncat_p s0) d ->k<=strncat_count s0 ->
    nonzero_prefix (s0 V_MEM32) (strncat_q s0) k ->
    ~overlap 32 (msub 32 (s0 R_ESP) 32) 48 (strncat_p s0) (d+k+1) /\
    (k<strncat_count s0 ->~overlap 32 (strncat_p s0+d) k (strncat_q s0+k) 1) /\
    (k<strncat_count s0 ->~overlap 32 (msub 32 (s0 R_ESP) 32) 32 (strncat_q s0+k) 1).
Definition strncat_outcome (s0:store) (d k:N):=
  first_nul (s0 V_MEM32) (strncat_p s0) d /\ k<=strncat_count s0 /\
  nonzero_prefix (s0 V_MEM32) (strncat_q s0) k /\
  (k=strncat_count s0 \/ getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k)=0).
Definition strncat_contents (s0:store) (d k:N) (m:memory):=
  (forall i,i<d ->getmem 32 LittleE 1 m (strncat_p s0+i)=getmem 32 LittleE 1 (s0 V_MEM32) (strncat_p s0+i)) /\
  (forall i,i<k ->getmem 32 LittleE 1 m (strncat_p s0+d+i)=getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+i)) /\
  getmem 32 LittleE 1 m (strncat_p s0+d+k)=0.
Lemma strncat_count_bound:forall s0,strncat_count s0<2^32.
Proof. intros. unfold strncat_count,ternary_arg3;apply getmem_bound. Qed.
Lemma strncat_stack_word:forall s0 off,off<=12 ->getmem 32 LittleE 4 (strncat_m6 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strncat_m6,strncat_m5,strncat_m4,strncat_m3,strncat_m2,strncat_m1.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strncat_m4_word:forall s0 off,off<=12 ->getmem 32 LittleE 4 (strncat_m4 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strncat_m4,strncat_m3,strncat_m2,strncat_m1.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strncat_stack_byte:forall s0 a,~overlap 32 (msub 32 (s0 R_ESP) 32) 32 a 1 ->
  getmem 32 LittleE 1 (strncat_m6 s0) a=getmem 32 LittleE 1 (s0 V_MEM32) a.
Proof.
  intros s0 a NO. unfold strncat_m6,strncat_m5,strncat_m4,strncat_m3,strncat_m2,strncat_m1.
  replace a with (a+0) by lia. rewrite !descending_stack_read with (total:=32) (n:=1) by (try exact NO;lia). reflexivity.
Qed.
Lemma strncat_dest_byte:forall s0 d,strncat_pre s0 ->nonzero_prefix (s0 V_MEM32) (strncat_p s0) d ->
  getmem 32 LittleE 1 (strncat_m6 s0) (strncat_p s0+d)=getmem 32 LittleE 1 (s0 V_MEM32) (strncat_p s0+d).
Proof.
  intros s0 d (_ & READ & SAFE) PREFIX. apply strncat_stack_byte.
  pose proof (noverlap_index_r 32 _ _ _ _ 0 1 (READ d PREFIX) ltac:(lia)) as NO.
  rewrite N.add_0_r in NO. exact NO.
Qed.
Lemma strncat_dest_prefix_back:forall s0 d,strncat_pre s0 ->nonzero_prefix (strncat_m6 s0) (strncat_p s0) d ->
  nonzero_prefix (s0 V_MEM32) (strncat_p s0) d.
Proof.
  intros s0 d PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (strncat_p s0+i))
    (fun i=>getmem 32 LittleE 1 (strncat_m6 s0) (strncat_p s0+i)) _ d PREFIX).
  intros j P. apply strncat_dest_byte;assumption.
Qed.
Lemma strncat_first_back:forall s0 d,strncat_pre s0 ->first_nul (strncat_m6 s0) (strncat_p s0) d ->
  first_nul (s0 V_MEM32) (strncat_p s0) d.
Proof.
  intros s0 d PRE [B [P ZERO]]. pose proof (strncat_dest_prefix_back s0 d PRE P) as ORIGINAL.
  split;[exact B|]. split;[exact ORIGINAL|]. rewrite <- strncat_dest_byte;assumption.
Qed.
Lemma strncat_callee_arg:forall s0 sc,strncat_frame s0 (strncat_m6 s0) 32 sc ->cdecl_arg sc=strncat_p s0.
Proof.
  intros s0 sc (MEM & SP & BP & RD & WR). unfold cdecl_arg at 1. rewrite MEM,SP. psimpl.
  unfold strncat_m6,strncat_m5. rewrite deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold strncat_p,cdecl_arg;apply getmem_bound.
Qed.
Lemma strncat_call_return:forall s0 sc value x se,strncat_frame s0 (strncat_m6 s0) 32 sc ->
  sc R_EBX=strncat_got ->sc R_ESI=strncat_p s0 ->sc R_EDI=strncat_q s0 ->cdecl_returned sc value x se ->
  x=Addr 0x3f57f /\ strncat_frame s0 (strncat_m6 s0) 28 se /\
    se R_EBX=strncat_got /\ se R_ESI=strncat_p s0 /\ se R_EDI=strncat_q s0 /\ se R_EAX=value.
Proof.
  intros s0 sc value x se (MEM & SP & BP & RD & WR) BX SI DI RETURN.
  unfold cdecl_returned in RETURN. rewrite MEM,SP,BP,RD,WR,BX,SI,DI in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold strncat_m6 in PC. rewrite getmem_setmem in PC by lia. split;[exact PC|]. split.
  - unfold strncat_frame. rewrite MEMORY,ESP,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX (conj ESI (conj EDI AX))).
Qed.
Lemma strncat_copy_bound:forall s0 d k,strncat_pre s0 ->first_nul (s0 V_MEM32) (strncat_p s0) d ->
  k<=strncat_count s0 ->nonzero_prefix (s0 V_MEM32) (strncat_q s0) k ->d+k+1<2^32.
Proof.
  intros s0 d k (_ & READ & SAFE) FIRST K PREFIX. destruct (SAFE d k FIRST K PREFIX) as [NO _].
  destruct (noverlap_sep 32 (msub 32 (s0 R_ESP) 32) 48 (strncat_p s0) (d+k+1) NO) as [LE|ZERO];[|discriminate].
  pose proof (msub_lt 32 (msub 32 (s0 R_ESP) 32) (strncat_p s0)). lia.
Qed.
Lemma strncat_source_byte:forall s0 d k,strncat_pre s0 ->first_nul (s0 V_MEM32) (strncat_p s0) d ->
  k<strncat_count s0 ->nonzero_prefix (s0 V_MEM32) (strncat_q s0) k ->
  getmem 32 LittleE 1 (strncat_memory s0 d k) (strncat_q s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k).
Proof.
  intros s0 d k (_ & READ & SAFE) FIRST K PREFIX. destruct (SAFE d k FIRST ltac:(lia) PREFIX) as (FRAME & COPY & STACK).
  unfold strncat_memory. rewrite (copy_bytes_frame _ _ _ _ _ _ _ (COPY K)).
  apply strncat_stack_byte;exact (STACK K).
Qed.
Lemma strncat_memory_step:forall s0 d k,setmem 32 LittleE 1 (strncat_memory s0 d k) (strncat_p s0+d+k)
  (getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k))=strncat_memory s0 d (k+1).
Proof. intros. unfold strncat_memory. rewrite copy_bytes_succ. reflexivity. Qed.
Lemma strncat_endmem_stack:forall s0 d k depth,strncat_pre s0 ->strncat_outcome s0 d k ->depth<=32 ->
  getmem 32 LittleE 4 (strncat_endmem s0 d k) (msub 32 (s0 R_ESP) depth)=
  getmem 32 LittleE 4 (strncat_m6 s0) (msub 32 (s0 R_ESP) depth).
Proof.
  intros s0 d k depth (_ & READ & SAFE) (FIRST & K & PREFIX & STOP) DEP.
  destruct (SAFE d k FIRST K PREFIX) as [NO _]. unfold strncat_endmem.
  apply copy_terminated_frame. apply noverlap_symmetry.
  assert (SLOT:~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (strncat_p s0) (d+k+1)).
  { eapply noverlap_shrink;[|exact NO]. rewrite stack_depth_difference,msub_sub by lia.
    rewrite N.mod_small by lia. lia. }
  replace (strncat_p s0+d) with (strncat_p s0+d) by reflexivity.
  eapply noverlap_index_r;[exact SLOT|lia].
Qed.
Lemma strncat_contents_endmem:forall s0 d k,strncat_pre s0 ->strncat_outcome s0 d k ->strncat_contents s0 d k (strncat_endmem s0 d k).
Proof.
  intros s0 d k PRE OUT. destruct OUT as (FIRST & K & PREFIX & STOP).
  pose proof (strncat_copy_bound s0 d k PRE FIRST K PREFIX) as BOUND.
  unfold strncat_contents,strncat_endmem. split.
  - intros i I. rewrite copy_terminated_frame.
    + apply strncat_dest_byte;[exact PRE|]. intros j J. apply (proj1 (proj2 FIRST));lia.
    + intros (u & v & U & V & EQ).
      replace (strncat_p s0+d+u) with (strncat_p s0+(d+u)) in EQ by lia.
      replace (strncat_p s0+i+v) with (strncat_p s0+(i+v)) in EQ by lia.
      apply (f_equal (fun a=>msub 32 a (strncat_p s0))) in EQ. cbn beta in EQ.
      rewrite !msub_mod_l,!add_msub_l in EQ by reflexivity. rewrite !N.mod_small in EQ by lia. lia.
  - split;[intros;apply copy_terminated_prefix;lia|apply copy_terminated_zero].
Qed.
Lemma strncat_m3_word:forall s0 off,off<=12 ->getmem 32 LittleE 4 (strncat_m3 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strncat_m3,strncat_m2,strncat_m1.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strncat_load_bx:forall s0,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (strncat_m6 s0) (msub 32 (s0 R_ESP) 12)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold strncat_m6,strncat_m5,strncat_m4,strncat_m3.
  repeat (rewrite deep_saved_word_frame by lia). rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma strncat_load_si:forall s0,s0 R_ESI<2^32 ->getmem 32 LittleE 4 (strncat_m6 s0) (msub 32 (s0 R_ESP) 8)=s0 R_ESI.
Proof.
  intros s0 BOUND. unfold strncat_m6,strncat_m5,strncat_m4,strncat_m3,strncat_m2.
  repeat (rewrite deep_saved_word_frame by lia). rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma strncat_load_di:forall s0,s0 R_EDI<2^32 ->getmem 32 LittleE 4 (strncat_m6 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EDI.
Proof.
  intros s0 BOUND. unfold strncat_m6,strncat_m5,strncat_m4,strncat_m3,strncat_m2,strncat_m1.
  repeat (rewrite deep_saved_word_frame by lia). rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma strncat_return_address:forall s0 d k,strncat_pre s0 ->strncat_outcome s0 d k ->
  getmem 32 LittleE 4 (strncat_endmem s0 d k) (s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP).
Proof.
  intros s0 d k PRE OUT. pose proof (strncat_endmem_stack s0 d k 0 PRE OUT ltac:(lia)) as RA.
  rewrite msub_0_r,!getmem_mod_l in RA.
  pose proof (strncat_stack_word s0 0 ltac:(lia)) as WORD. rewrite N.add_0_l in WORD. rewrite WORD in RA. exact RA.
Qed.
