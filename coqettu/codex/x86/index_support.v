(* Original-memory search transport through index -> strchr -> strchrnul. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_strings
  index_i386 strchr_support strchr_proof strchr_i386 strchrnul_support strchrnul_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition index_linked:program:=updateall2 index_i386 strchr_linked.
Lemma index_linked_caller:index_i386 ⊆2 index_linked.
Proof.
  intros s a insn H. unfold index_linked,strchr_linked,strchrnul_linked,updateall2,updateall,
    index_i386,strchr_i386,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma index_linked_callee:strchr_linked ⊆2 index_linked.
Proof. intros s a insn H. unfold index_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem index_linked_welltyped:welltyped_prog x86typctx index_linked.
Proof.
  intros s a. unfold index_linked,updateall2,updateall.
  destruct (strchr_linked s a) as [[sz q]|] eqn:C.
  - pose proof (strchr_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - apply index_i386.welltyped.
Qed.
Definition index_got:N:=0xb4f9c.
Definition index_m1:=unary_m1.
Definition index_m2 (s0:store):=unary_m2 s0 0x75edb.
Definition index_m4 (s0:store):=binary_m4 s0 0x75edb.
Definition index_m5 (s0:store):=binary_entry_memory s0 0x75edb 0x75ef1.
Definition index_frame:=unary_frame.
Definition index_child (s0:store):=s0[V_MEM32:=index_m5 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=index_got].
Definition index_memory (s0:store):=strchr_memory (index_child s0).
Definition index_reference (s0:store):=s0[V_MEM32:=index_memory s0].
Definition index_pre (s0:store):=models x86typctx s0 /\ forall k,nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 112) 112 (cdecl_arg s0+k) 4.
Lemma index_child_frame:forall s0,index_frame s0 (index_m5 s0) 32 (index_child s0).
Proof. intros. unfold index_frame,unary_frame,index_child. psimpl. repeat split;reflexivity. Qed.
Lemma index_m2_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (index_m2 s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros;apply unary_m2_stack;assumption. Qed.
Lemma index_callee_args:forall s0 sc,index_frame s0 (index_m5 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ strchrnul_char sc=strchrnul_char s0.
Proof.
  intros s0 sc F. destruct (binary_callee_args s0 0x75edb 0x75ef1 sc F) as [P C]. split;[exact P|].
  apply (f_equal (fun x=>x mod 2^(1*8))) in C. unfold binary_arg2 in C. rewrite !getmem_mod in C. exact C.
Qed.
Lemma index_entry_word:forall s0 k,index_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 4 (index_m5 s0) (cdecl_arg s0+k)=getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 k [_ A] P. pose proof (A k P) as NO.
  unfold index_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  replace (cdecl_arg s0+k) with ((cdecl_arg s0+k)+0) by lia.
  rewrite !descending_stack_read with (total:=112) (n:=4) by (try exact NO;lia). reflexivity.
Qed.
Lemma index_entry_byte:forall s0 k,index_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (index_m5 s0) (cdecl_arg s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros. pose proof (index_entry_word s0 k H H0) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma index_prefix_back:forall s0 k,index_pre s0 ->nonzero_prefix (index_m5 s0) (cdecl_arg s0) k ->
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.
Proof.
  intros s0 k PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
    (fun i=>getmem 32 LittleE 1 (index_m5 s0) (cdecl_arg s0+i)) _ k PREFIX).
  intros j P. apply index_entry_byte;assumption.
Qed.
Lemma index_callee_pre:forall s0 sc,index_pre s0 ->models x86typctx sc ->
  index_frame s0 (index_m5 s0) 32 sc ->strchr_pre sc.
Proof.
  intros s0 sc PRE MDL F. pose proof (index_callee_args s0 sc F) as [ARG CHAR].
  split;[exact MDL|]. intros k PREFIX. rewrite ARG,(proj1 F) in PREFIX.
  pose proof (index_prefix_back s0 k PRE PREFIX) as ORIGINAL.
  pose proof (proj2 PRE k ORIGINAL) as NO. rewrite ARG,(proj1 (proj2 F)). psimpl.
  eapply descending_stack_subregion;[| |exact NO];lia.
Qed.
Lemma strchr_memory_entry_ext:forall s1 s2,s1 V_MEM32=s2 V_MEM32 ->s1 R_ESP=s2 R_ESP ->
  s1 R_EBX=s2 R_EBX ->s1 R_ESI=s2 R_ESI ->s1 R_EDI=s2 R_EDI ->s1 R_EBP=s2 R_EBP ->
  cdecl_arg s1=cdecl_arg s2 ->binary_arg2 s1=binary_arg2 s2 ->strchrnul_char s1=strchrnul_char s2 ->
  strchr_memory s1=strchr_memory s2.
Proof.
  intros s1 s2 MEM SP BX SI DI BP ARG ARG2 CHAR. unfold strchr_memory. rewrite CHAR.
  destruct (strchrnul_char s2=?0);
    unfold strchr_m10,strchr_m9,strchr_m8,strchr_m7,strchr_m6,strchr_m5,strchr_m4,strchr_m3,strchr_m2,strchr_m1;
    rewrite ?ARG,?ARG2,MEM,SP,BX,SI,DI,BP;reflexivity.
Qed.
Lemma index_callee_memory:forall s0 sc,index_frame s0 (index_m5 s0) 32 sc ->sc R_EBX=index_got ->
  strchr_memory sc=index_memory s0.
Proof.
  intros s0 sc F BX. pose proof (index_callee_args s0 sc F) as [ARG CHAR].
  pose proof (index_callee_args s0 (index_child s0) (index_child_frame s0)) as [CARG CCHAR].
  pose proof (binary_callee_args s0 0x75edb 0x75ef1 sc F) as [_ ARG2].
  pose proof (binary_callee_args s0 0x75edb 0x75ef1 (index_child s0) (index_child_frame s0)) as [_ CARG2].
  unfold index_memory. apply strchr_memory_entry_ext;try congruence.
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold index_child;psimpl;assumption.
Qed.
Lemma index_result_back:forall s0 sc value,index_pre s0 ->index_frame s0 (index_m5 s0) 32 sc ->
  strchr_result sc value ->strchr_result s0 value.
Proof.
  intros s0 sc value PRE F RESULT. pose proof (index_callee_args s0 sc F) as [ARG CHAR].
  unfold strchr_result,strchrnul_prefix in *. rewrite ARG,CHAR,(proj1 F) in RESULT.
  destruct RESULT as [k [[PREFIX MATCH] STOP]]. pose proof (index_prefix_back s0 k PRE PREFIX) as ORIGINAL.
  exists k. split.
  - split;[exact ORIGINAL|]. intros i I. rewrite <- index_entry_byte;[exact (MATCH i I)|exact PRE|].
    intros j J. apply ORIGINAL;lia.
  - rewrite (index_entry_byte s0 k PRE ORIGINAL) in STOP. exact STOP.
Qed.
Lemma index_after_stack:forall sc off,off<=64 ->getmem 32 LittleE 4 (strchr_memory sc) (off+sc R_ESP)=
  getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc off OFF. unfold strchr_memory. destruct (strchrnul_char sc=?0);
    unfold strchr_m10,strchr_m9,strchr_m8,strchr_m7,strchr_m6,strchr_m5,strchr_m4,strchr_m3,strchr_m2,strchr_m1;
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma index_saved_bx:forall s0,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (index_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold index_memory. pose proof (index_after_stack (index_child s0) 28 ltac:(lia)) as READ.
  unfold index_child in READ. psimpl in READ. unfold index_child. rewrite READ.
  unfold index_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma index_outer_stack:forall s0 off,off<=8 ->getmem 32 LittleE 4 (index_memory s0) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold index_memory. pose proof (index_after_stack (index_child s0) (32+off) ltac:(lia)) as READ.
  unfold index_child in READ. psimpl in READ. unfold index_child. rewrite READ.
  unfold index_m5,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma index_call_return:forall s0 sc value x se,index_pre s0 ->index_frame s0 (index_m5 s0) 32 sc ->sc R_EBX=index_got ->
  cdecl_returned (strchr_reference sc) value x se ->
  x=Addr 0x75ef1 /\ index_frame s0 (index_memory s0) 28 se /\ se R_EBX=index_got /\ se R_EAX=value.
Proof.
  intros s0 sc value x se PRE F BX RETURN. pose proof (index_callee_memory s0 sc F BX) as MM.
  pose proof (strchr_outer_stack sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strchr_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold index_m5 in PC. rewrite binary_call_address in PC. split;[exact PC|]. split.
  - unfold index_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
