(* Original-memory last-match transport through rindex -> strrchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_strings
  rindex_i386 strrchr_support strrchr_proof strrchr_i386 i386_reverse memrchr_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition rindex_linked:program:=updateall2 rindex_i386 strrchr_linked.
Lemma rindex_linked_caller:rindex_i386 ⊆2 rindex_linked.
Proof.
  intros s a insn H. unfold rindex_linked,strrchr_linked,updateall2,updateall,
    rindex_i386,strrchr_i386,memrchr_i386,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma rindex_linked_callee:strrchr_linked ⊆2 rindex_linked.
Proof. intros s a insn H. unfold rindex_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem rindex_linked_welltyped:welltyped_prog x86typctx rindex_linked.
Proof.
  intros s a. unfold rindex_linked,updateall2,updateall.
  destruct (strrchr_linked s a) as [[sz q]|] eqn:C.
  - pose proof (strrchr_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - apply rindex_i386.welltyped.
Qed.
Definition rindex_got:N:=0xb4f9c.
Definition rindex_m1:=unary_m1.
Definition rindex_m2 (s0:store):=unary_m2 s0 0x75f25.
Definition rindex_m4 (s0:store):=binary_m4 s0 0x75f25.
Definition rindex_m5 (s0:store):=binary_entry_memory s0 0x75f25 0x75f3b.
Definition rindex_frame:=unary_frame.
Definition rindex_child (s0:store):=s0[V_MEM32:=rindex_m5 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=rindex_got].
Definition rindex_memory (s0:store) (n:N):=strrchr_memory (rindex_child s0) n.
Definition rindex_reference (s0:store) (n:N):=s0[V_MEM32:=rindex_memory s0 n].
Definition rindex_pre (s0:store):=models x86typctx s0 /\ 0<cdecl_arg s0 /\
  forall k,nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->cdecl_arg s0+k+1<=2^32 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 72) 72 (cdecl_arg s0) (k+1).
Lemma rindex_child_frame:forall s0,rindex_frame s0 (rindex_m5 s0) 32 (rindex_child s0).
Proof. intros. unfold rindex_frame,unary_frame,rindex_child. psimpl. repeat split;reflexivity. Qed.
Lemma rindex_m2_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (rindex_m2 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros;apply unary_m2_stack;assumption. Qed.
Lemma rindex_callee_args:forall s0 sc,rindex_frame s0 (rindex_m5 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ strrchr_char sc=strrchr_char s0.
Proof.
  intros s0 sc F. destruct (binary_callee_args s0 0x75f25 0x75f3b sc F) as [P C]. split;[exact P|].
  apply (f_equal (fun x=>x mod 2^(1*8))) in C. unfold binary_arg2 in C. rewrite !getmem_mod in C. exact C.
Qed.
Lemma rindex_entry_byte:forall s0 k,rindex_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (rindex_m5 s0) (cdecl_arg s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 k (_ & BASE & SAFE) P. destruct (SAFE k P) as [BOUND NO].
  unfold rindex_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=72) (n:=k+1) by (try exact NO;lia). reflexivity.
Qed.
Lemma rindex_prefix_back:forall s0 k,rindex_pre s0 ->nonzero_prefix (rindex_m5 s0) (cdecl_arg s0) k ->
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.
Proof.
  intros s0 k PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
    (fun i=>getmem 32 LittleE 1 (rindex_m5 s0) (cdecl_arg s0+i)) _ k PREFIX).
  intros j P. apply rindex_entry_byte;assumption.
Qed.
Lemma rindex_first_back:forall s0 sc n,rindex_pre s0 ->rindex_frame s0 (rindex_m5 s0) 32 sc ->
  first_nul (sc V_MEM32) (cdecl_arg sc) n ->first_nul (s0 V_MEM32) (cdecl_arg s0) n.
Proof.
  intros s0 sc n PRE F [NBOUND [PREFIX ZERO]]. pose proof (rindex_callee_args s0 sc F) as [ARG CHAR].
  rewrite ARG,(proj1 F) in PREFIX,ZERO. pose proof (rindex_prefix_back s0 n PRE PREFIX) as ORIGINAL.
  split;[exact NBOUND|]. split;[exact ORIGINAL|]. rewrite <- rindex_entry_byte;assumption.
Qed.
Lemma rindex_callee_pre:forall s0 sc,rindex_pre s0 ->models x86typctx sc ->
  rindex_frame s0 (rindex_m5 s0) 32 sc ->strrchr_pre sc.
Proof.
  intros s0 sc PRE MDL F. pose proof (rindex_callee_args s0 sc F) as [ARG CHAR].
  destruct PRE as (MDL0 & BASE & SAFE). split;[exact MDL|]. rewrite ARG. split;[exact BASE|].
  intros k PREFIX. rewrite (proj1 F) in PREFIX.
  pose proof (rindex_prefix_back s0 k (conj MDL0 (conj BASE SAFE)) PREFIX) as ORIGINAL.
  destruct (SAFE k ORIGINAL) as [BOUND NO]. split;[exact BOUND|]. rewrite (proj1 (proj2 F)). psimpl.
  eapply descending_stack_subregion;[| |replace (1+k) with (k+1) by lia;exact NO];lia.
Qed.
Lemma rindex_callee_memory:forall s0 sc n,rindex_frame s0 (rindex_m5 s0) 32 sc ->sc R_EBX=rindex_got ->
  strrchr_memory sc n=rindex_memory s0 n.
Proof.
  intros s0 sc n F BX. pose proof (rindex_callee_args s0 sc F) as [ARG CHAR].
  pose proof (binary_callee_args s0 0x75f25 0x75f3b sc F) as [_ ARG2].
  pose proof (binary_callee_args s0 0x75f25 0x75f3b (rindex_child s0) (rindex_child_frame s0)) as [CARG CARG2].
  unfold rindex_memory,strrchr_memory,strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5,strrchr_m4,
    unary_memory,unary_m3,strrchr_m2,unary_m2,unary_m1,save_ebx_memory.
  rewrite ARG,ARG2,CARG,CARG2;destruct F as (MEM & SP & SI & DI & BP & RD & WR);
    unfold rindex_child;psimpl;rewrite MEM,SP,BX,SI;psimpl;reflexivity.
Qed.
Lemma rindex_search_back:forall s0 sc n value,rindex_pre s0 ->rindex_frame s0 (rindex_m5 s0) 32 sc ->
  first_nul (s0 V_MEM32) (cdecl_arg s0) n ->strrchr_search sc n value ->strrchr_search s0 n value.
Proof.
  intros s0 sc n value PRE F [_ [PREFIX ZERO]] RESULT. pose proof (rindex_callee_args s0 sc F) as [ARG CHAR].
  assert (READ:forall i,i<=n ->getmem 32 LittleE 1 (rindex_m5 s0) (cdecl_arg s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)).
  { intros i I. apply rindex_entry_byte;[exact PRE|]. intros j J. apply PREFIX;lia. }
  unfold strrchr_search,reverse_search_result,nonmatching_suffix in *. rewrite ARG,CHAR,(proj1 F) in RESULT.
  destruct RESULT as [[VALUE NO]|[k (K & NO & BYTE & VALUE)]].
  - left. split;[exact VALUE|]. intros i I J. rewrite <- READ by lia. apply NO;assumption.
  - right. exists k. split;[exact K|]. split.
    + intros i I J. rewrite <- READ by lia. apply NO;assumption.
    + rewrite READ in BYTE by lia. exact (conj BYTE VALUE).
Qed.
Lemma rindex_after_stack:forall sc n off,off<=64 ->getmem 32 LittleE 4 (strrchr_memory sc n) (off+sc R_ESP)=
  getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc n off OFF. unfold strrchr_memory,strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5,strrchr_m4,
    unary_memory,unary_m3,strrchr_m2,unary_m2,unary_m1,save_ebx_memory;
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma rindex_saved_bx:forall s0 n,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (rindex_memory s0 n) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 n BOUND. unfold rindex_memory. pose proof (rindex_after_stack (rindex_child s0) n 28 ltac:(lia)) as READ.
  unfold rindex_child in READ. psimpl in READ. unfold rindex_child. rewrite READ.
  unfold rindex_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma rindex_outer_stack:forall s0 n off,off<=8 ->getmem 32 LittleE 4 (rindex_memory s0 n) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 n off OFF. unfold rindex_memory. pose proof (rindex_after_stack (rindex_child s0) n (32+off) ltac:(lia)) as READ.
  unfold rindex_child in READ. psimpl in READ. unfold rindex_child. rewrite READ.
  unfold rindex_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma rindex_call_return:forall s0 sc n value x se,rindex_pre s0 ->rindex_frame s0 (rindex_m5 s0) 32 sc ->sc R_EBX=rindex_got ->
  cdecl_returned (strrchr_reference sc n) value x se ->
  x=Addr 0x75f3b /\ rindex_frame s0 (rindex_memory s0 n) 28 se /\ se R_EBX=rindex_got /\ se R_EAX=value.
Proof.
  intros s0 sc n value x se PRE F BX RETURN. pose proof (rindex_callee_memory s0 sc n F BX) as MM.
  pose proof (strrchr_outer_stack sc n 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strrchr_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold rindex_m5 in PC. rewrite binary_call_address in PC. split;[exact PC|]. split.
  - unfold rindex_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
