(* Linked code and shared unary stack interface for strrchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call
  i386_binary_call i386_strings i386_stack2 i386_reverse memrchr_i386 memrchr_proof strlen_proof strrchr_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strrchr_linked : program := updateall2 strrchr_i386 (updateall2 pc_thunk_bx_i386 (updateall2 strlen_i386 memrchr_i386)).
Lemma strrchr_linked_caller : strrchr_i386 ⊆2 strrchr_linked.
Proof.
  intros s a insn H. unfold strrchr_linked,updateall2,updateall,strrchr_i386,pc_thunk_bx_i386,strlen_i386,memrchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strrchr_linked_memrchr:memrchr_i386 ⊆2 strrchr_linked.
Proof. intros s a insn H. unfold strrchr_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strrchr_linked_strlen:strlen_i386 ⊆2 strrchr_linked.
Proof.
  intros s a insn H. unfold strrchr_linked,updateall2,updateall,strlen_i386,memrchr_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strrchr_linked_thunk : pc_thunk_bx_i386 ⊆2 strrchr_linked.
Proof.
  intros s a insn H. unfold strrchr_linked,updateall2,updateall,pc_thunk_bx_i386,strlen_i386,memrchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strrchr_linked_welltyped:welltyped_prog x86typctx strrchr_linked.
Proof.
  intros s a. unfold strrchr_linked,updateall2,updateall.
  destruct (memrchr_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (memrchr_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (strlen_i386 s a) as [[sz q]|] eqn:L.
    + pose proof (strlen_i386.welltyped s a) as WT. rewrite L in WT. exact WT.
    + destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
      * pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
      * apply strrchr_i386.welltyped.
Qed.

Definition strrchr_got:N:=0xb4f9c.
Definition strrchr_char (s0:store):=getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP).
Definition strrchr_m1:=unary_m1.
Definition strrchr_m2 (s0:store):=unary_m2 s0 0x763bc.
Definition strrchr_m3 (s0:store):=unary_m3 s0 0x763bc.
Definition strrchr_m4 (s0:store):=unary_memory s0 0x763bc 0x763ce.
Definition strrchr_m5 (s0:store) (n:N):=
  setmem 32 LittleE 4 (strrchr_m4 s0) (msub 32 (s0 R_ESP) 20) (n+1).
Definition strrchr_m6 (s0:store) (n:N):=
  setmem 32 LittleE 4 (strrchr_m5 s0 n) (msub 32 (s0 R_ESP) 24) (binary_arg2 s0).
Definition strrchr_m7 (s0:store) (n:N):=
  setmem 32 LittleE 4 (strrchr_m6 s0 n) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition strrchr_m8 (s0:store) (n:N):=
  setmem 32 LittleE 4 (strrchr_m7 s0 n) (msub 32 (s0 R_ESP) 32) 0x763e2.
Definition strrchr_memory (s0:store) (n:N):=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (strrchr_m8 s0 n) (msub 32 (s0 R_ESP) 36) (s0 R_ESI))
    (msub 32 (s0 R_ESP) 40) strrchr_got.
Definition strrchr_reference (s0:store) (n:N):=s0[V_MEM32:=strrchr_memory s0 n].
Definition strrchr_frame:=unary_frame.
Definition strrchr_pre (s0:store):=models x86typctx s0 /\ 0<cdecl_arg s0 /\
  forall k,nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
    cdecl_arg s0+k+1<=2^32 /\
    ~overlap 32 (msub 32 (s0 R_ESP) 40) 40 (cdecl_arg s0) (k+1).
Definition strrchr_search (s0:store) (n result:N):=
  reverse_search_result (s0 V_MEM32) (cdecl_arg s0) (strrchr_char s0) (n+1) result.
Definition strrchr_result (s0:store) (result:N):=exists n,
  first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ strrchr_search s0 n result.
Lemma strrchr_bound:forall s0 n,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->n+1<2^32.
Proof.
  intros s0 n (_ & BASE & SAFE) (NBOUND & PREFIX & ZERO).
  destruct (SAFE n PREFIX) as [BOUND NO].
  set (p:=cdecl_arg s0) in *;clearbody p;clear - BASE BOUND;lia.
Qed.
Lemma strrchr_region:forall s0 n,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  ~overlap 32 (msub 32 (s0 R_ESP) 40) 40 (cdecl_arg s0) (n+1).
Proof. intros s0 n (_ & BASE & SAFE) (NBOUND & PREFIX & ZERO). exact (proj2 (SAFE n PREFIX)). Qed.
Lemma strrchr_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strrchr_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma strrchr_m4_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strrchr_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_outer_stack;assumption. Qed.
Lemma strrchr_m5_stack:forall s0 n off,off<=8 ->
  getmem 32 LittleE 4 (strrchr_m5 s0 n) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros. unfold strrchr_m5. rewrite (N.add_comm off (s0 R_ESP)),deep_stack_word_frame by lia.
  rewrite (N.add_comm (s0 R_ESP) off). apply unary_outer_stack;assumption.
Qed.
Lemma strrchr_m6_stack:forall s0 n off,off<=8 ->
  getmem 32 LittleE 4 (strrchr_m6 s0 n) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros. unfold strrchr_m6. rewrite (N.add_comm off (s0 R_ESP)),deep_stack_word_frame by lia.
  rewrite (N.add_comm (s0 R_ESP) off). apply strrchr_m5_stack;assumption.
Qed.
Lemma strrchr_outer_stack:forall s0 n off,off<=8 ->
  getmem 32 LittleE 4 (strrchr_memory s0 n) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 n off OFF. unfold strrchr_memory,strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5,
    strrchr_m4,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma strrchr_saved_bx:forall s0 n,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strrchr_memory s0 n) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 n BOUND. unfold strrchr_memory,strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5,
    strrchr_m4,unary_memory,unary_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma strrchr_m4_byte:forall s0 k,strrchr_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (strrchr_m4 s0) (cdecl_arg s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 k (_ & BASE & SAFE) PREFIX. destruct (SAFE k PREFIX) as [BOUND NO].
  unfold strrchr_m4,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=40) (n:=k+1) by (first[exact NO|lia]). reflexivity.
Qed.
Lemma strrchr_first_transport:forall s0 n,strrchr_pre s0 ->first_nul (strrchr_m4 s0) (cdecl_arg s0) n ->
  first_nul (s0 V_MEM32) (cdecl_arg s0) n.
Proof.
  intros s0 n PRE (BOUND & PREFIX & ZERO).
  assert (ORIGINAL:nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) n).
  { refine (conditional_prefix_transfer
      (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
      (fun i=>getmem 32 LittleE 1 (strrchr_m4 s0) (cdecl_arg s0+i)) _ n PREFIX).
    intros j P. exact (strrchr_m4_byte s0 j PRE P). }
  rewrite (strrchr_m4_byte s0 n PRE ORIGINAL) in ZERO. repeat split;assumption.
Qed.
Lemma strrchr_m8_byte:forall s0 n i,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->i<n+1 ->
  getmem 32 LittleE 1 (strrchr_m8 s0 n) (cdecl_arg s0+i)=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i).
Proof.
  intros s0 n i PRE FIRST I. pose proof (strrchr_region s0 n PRE FIRST) as NO.
  unfold strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5,strrchr_m4,
    unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=40) (n:=n+1) by (first[exact NO|clear - I;lia]). reflexivity.
Qed.
Lemma strrchr_m8_arg:forall s0 n,
  getmem 32 LittleE 4 (strrchr_m8 s0 n) (msub 32 (s0 R_ESP) 28)=cdecl_arg s0.
Proof.
  intros. unfold strrchr_m8,strrchr_m7. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small. unfold cdecl_arg;apply getmem_bound.
Qed.
Lemma strrchr_m8_char:forall s0 n,
  getmem 32 LittleE 1 (strrchr_m8 s0 n) (msub 32 (s0 R_ESP) 24)=strrchr_char s0.
Proof.
  intros. assert (WORD:getmem 32 LittleE 4 (strrchr_m8 s0 n) (msub 32 (s0 R_ESP) 24)=binary_arg2 s0).
  { unfold strrchr_m8,strrchr_m7,strrchr_m6. rewrite !deep_saved_word_frame by lia.
    rewrite getmem_setmem by lia. apply N.mod_small. unfold binary_arg2;apply getmem_bound. }
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. unfold binary_arg2 in WORD.
  rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma strrchr_m8_count:forall s0 n,n+1<2^32 ->
  getmem 32 LittleE 4 (strrchr_m8 s0 n) (msub 32 (s0 R_ESP) 20)=n+1.
Proof.
  intros. unfold strrchr_m8,strrchr_m7,strrchr_m6,strrchr_m5. rewrite !deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small;assumption.
Qed.
Lemma strrchr_callee_args:forall s0 n sc,n+1<2^32 ->strrchr_frame s0 (strrchr_m8 s0 n) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ memrchr_char sc=strrchr_char s0 /\ memrchr_count sc=n+1.
Proof.
  intros s0 n sc BOUND (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold memrchr_char,memrchr_count. rewrite MEM,SP. psimpl.
  rewrite strrchr_m8_arg,strrchr_m8_char,strrchr_m8_count by exact BOUND.
  repeat split;try reflexivity. clear - n;lia.
Qed.
Lemma strrchr_callee_pre:forall s0 n sc,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  models x86typctx sc ->strrchr_frame s0 (strrchr_m8 s0 n) 32 sc ->memrchr_pre sc.
Proof.
  intros s0 n sc PRE FIRST MDL FRAME. pose proof (strrchr_bound s0 n PRE FIRST) as BOUND.
  pose proof (strrchr_region s0 n PRE FIRST) as NO.
  destruct (strrchr_callee_args s0 n sc BOUND FRAME) as (P & C & N).
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold memrchr_pre. rewrite P,N,SP. psimpl. rewrite (N.add_comm 1 n).
  split;[exact MDL|]. split;
    eapply descending_stack_subregion;[| |exact NO| | |exact NO];lia.
Qed.
Lemma strrchr_callee_memory:forall s0 n sc,strrchr_frame s0 (strrchr_m8 s0 n) 32 sc ->
  sc R_EBX=strrchr_got ->save_si_bx_memory sc=strrchr_memory s0 n.
Proof.
  intros s0 n sc (MEM & SP & SI & DI & BP & RD & WR) BX.
  unfold save_si_bx_memory,strrchr_memory. rewrite MEM,SP,SI,BX. psimpl. reflexivity.
Qed.
Lemma strrchr_call_address:forall s0 n,
  getmem 32 LittleE 4 (strrchr_memory s0 n) (msub 32 (s0 R_ESP) 32)=0x763e2.
Proof.
  intros. unfold strrchr_memory,strrchr_m8. rewrite !deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. reflexivity.
Qed.
Lemma strrchr_search_transport:forall s0 n result,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  reverse_search_result (strrchr_m8 s0 n) (cdecl_arg s0) (strrchr_char s0) (n+1) result ->strrchr_search s0 n result.
Proof.
  intros s0 n result PRE FIRST RESULT.
  assert (SUFFIX:forall k,nonmatching_suffix (strrchr_m8 s0 n) (cdecl_arg s0) (strrchr_char s0) k (n+1) ->
    nonmatching_suffix (s0 V_MEM32) (cdecl_arg s0) (strrchr_char s0) k (n+1)).
  { intros k SUF i LO HI. rewrite <- (strrchr_m8_byte s0 n i PRE FIRST HI). exact (SUF i LO HI). }
  destruct RESULT as [[ZERO NONE]|(k & K & NONE & MATCH & VALUE)].
  - left. split;[exact ZERO|apply SUFFIX;exact NONE].
  - right. exists k. split;[exact K|]. split;[apply SUFFIX;exact NONE|].
    rewrite <- (strrchr_m8_byte s0 n k PRE FIRST K). split;assumption.
Qed.
Lemma strrchr_call_return:forall s0 n sc sr x se,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  strrchr_frame s0 (strrchr_m8 s0 n) 32 sc ->sc R_EBX=strrchr_got ->memrchr_result sc (sr R_EAX) ->
  cdecl_returned (save_si_bx_reference sc) (sr R_EAX) x se ->
  x=Addr 0x763e2 /\ strrchr_frame s0 (strrchr_memory s0 n) 28 se /\
  se R_EBX=strrchr_got /\ strrchr_search s0 n (se R_EAX).
Proof.
  intros s0 n sc sr x se PRE FIRST FRAME BX RESULT RETURN.
  destruct (strrchr_callee_args s0 n sc (strrchr_bound s0 n PRE FIRST) FRAME) as (P & C & N).
  pose proof (strrchr_callee_memory s0 n sc FRAME BX) as SAVED.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,save_si_bx_reference in RETURN. psimpl in RETURN.
  rewrite SAVED,SP,SI,DI,BX,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite strrchr_call_address in PC. split;[exact PC|]. split.
  - unfold strrchr_frame,unary_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - split;[exact EBX|]. rewrite AX. unfold memrchr_result in RESULT. rewrite P,C,N,MEM in RESULT.
    apply strrchr_search_transport;assumption.
Qed.
