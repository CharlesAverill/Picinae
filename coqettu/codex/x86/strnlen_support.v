(* Linked code and stack snapshots for strnlen composed with memchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_strings i386_byte_search
  strnlen_i386 pc_thunk_bx_i386 memchr_i386 memchr_support.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strnlen_linked : program := updateall2 strnlen_i386 (updateall2 pc_thunk_bx_i386 memchr_i386).
Lemma strnlen_linked_caller : strnlen_i386 ⊆2 strnlen_linked.
Proof.
  intros s a insn H. unfold strnlen_linked,updateall2,updateall,strnlen_i386,pc_thunk_bx_i386,memchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strnlen_linked_memchr : memchr_i386 ⊆2 strnlen_linked.
Proof. intros s a insn H. unfold strnlen_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strnlen_linked_thunk : pc_thunk_bx_i386 ⊆2 strnlen_linked.
Proof.
  intros s a insn H. unfold strnlen_linked,updateall2,updateall,pc_thunk_bx_i386,memchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strnlen_linked_welltyped : welltyped_prog x86typctx strnlen_linked.
Proof.
  intros s a. unfold strnlen_linked,updateall2,updateall.
  destruct (memchr_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (memchr_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strnlen_i386.welltyped.
Qed.

Definition strnlen_count (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition strnlen_got:N:=0xb4f9c.
Definition strnlen_m1 (s0:store):=save_ebx_memory s0.
Definition strnlen_m2 (s0:store):=setmem 32 LittleE 4 (strnlen_m1 s0) (msub 32 (s0 R_ESP) 8) 0x76355.
Definition strnlen_m3 (s0:store):=setmem 32 LittleE 4 (strnlen_m2 s0) (msub 32 (s0 R_ESP) 20) (strnlen_count s0).
Definition strnlen_m4 (s0:store):=setmem 32 LittleE 4 (strnlen_m3 s0) (msub 32 (s0 R_ESP) 24) 0.
Definition strnlen_m5 (s0:store):=setmem 32 LittleE 4 (strnlen_m4 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition strnlen_m6 (s0:store):=setmem 32 LittleE 4 (strnlen_m5 s0) (msub 32 (s0 R_ESP) 32) 0x7636d.
Definition strnlen_m7 (s0:store):=setmem 32 LittleE 4 (strnlen_m6 s0) (msub 32 (s0 R_ESP) 36) (s0 R_EBP).
Definition strnlen_m8 (s0:store):=setmem 32 LittleE 4 (strnlen_m7 s0) (msub 32 (s0 R_ESP) 40) (s0 R_EDI).
Definition strnlen_m9 (s0:store):=setmem 32 LittleE 4 (strnlen_m8 s0) (msub 32 (s0 R_ESP) 44) (s0 R_ESI).
Definition strnlen_m10 (s0:store):=setmem 32 LittleE 4 (strnlen_m9 s0) (msub 32 (s0 R_ESP) 48) strnlen_got.
Definition strnlen_endpoint (s0:store):=(cdecl_arg s0+strnlen_count s0) mod 2^32.
Definition strnlen_memory (s0:store) (used:bool):=if used then
  setmem 32 LittleE 4 (strnlen_m10 s0) (msub 32 (s0 R_ESP) 52) (strnlen_endpoint s0)
  else strnlen_m10 s0.
Definition strnlen_reference (s0:store) (used:bool):=s0[V_MEM32:=strnlen_memory s0 used].
Definition strnlen_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strnlen_pre (s0:store):=models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 52) 52 (cdecl_arg s0) (strnlen_count s0) /\
  ~overlap 32 0 1 (cdecl_arg s0) (strnlen_count s0).
Definition strnlen_result (s0:store) (result:N):=
  (result=strnlen_count s0 /\ nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) (strnlen_count s0)) \/
  (exists k,k<strnlen_count s0 /\ first_nul (s0 V_MEM32) (cdecl_arg s0) k /\ result=k).
Lemma strnlen_count_bound:forall s0,strnlen_count s0<2^32.
Proof. intros s0. unfold strnlen_count. apply getmem_bound. Qed.
Lemma strnlen_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strnlen_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strnlen_m2,strnlen_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma strnlen_outer_stack:forall s0 used off,off<=8 ->
  getmem 32 LittleE 4 (strnlen_memory s0 used) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 [|] off OFF;unfold strnlen_memory,strnlen_m10,strnlen_m9,strnlen_m8,strnlen_m7,
    strnlen_m6,strnlen_m5,strnlen_m4,strnlen_m3,strnlen_m2,strnlen_m1,save_ebx_memory;
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strnlen_saved_bx:forall s0 used,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strnlen_memory s0 used) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 [|] BOUND;unfold strnlen_memory,strnlen_m10,strnlen_m9,strnlen_m8,strnlen_m7,
    strnlen_m6,strnlen_m5,strnlen_m4,strnlen_m3,strnlen_m2,strnlen_m1;
  rewrite !deep_saved_word_frame by lia;apply saved_ebx_load;exact BOUND.
Qed.
Lemma strnlen_call_address:forall s0 used,
  getmem 32 LittleE 4 (strnlen_memory s0 used) (msub 32 (s0 R_ESP) 32)=0x7636d.
Proof.
  intros s0 [|];unfold strnlen_memory,strnlen_m10,strnlen_m9,strnlen_m8,strnlen_m7,strnlen_m6;
  rewrite !deep_saved_word_frame by lia;rewrite getmem_setmem by lia;reflexivity.
Qed.
Lemma strnlen_m6_arg:forall s0,
  getmem 32 LittleE 4 (strnlen_m6 s0) (msub 32 (s0 R_ESP) 28)=cdecl_arg s0.
Proof.
  intros s0. unfold strnlen_m6,strnlen_m5. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small. unfold cdecl_arg. apply getmem_bound.
Qed.
Lemma strnlen_m6_char:forall s0,
  getmem 32 LittleE 1 (strnlen_m6 s0) (msub 32 (s0 R_ESP) 24)=0.
Proof.
  intros s0. assert (WORD:getmem 32 LittleE 4 (strnlen_m6 s0) (msub 32 (s0 R_ESP) 24)=0).
  { unfold strnlen_m6,strnlen_m5,strnlen_m4. rewrite !deep_saved_word_frame by lia.
    rewrite getmem_setmem by lia. reflexivity. }
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite getmem_mod in WORD. exact WORD.
Qed.
Lemma strnlen_m6_count:forall s0,
  getmem 32 LittleE 4 (strnlen_m6 s0) (msub 32 (s0 R_ESP) 20)=strnlen_count s0.
Proof.
  intros s0. unfold strnlen_m6,strnlen_m5,strnlen_m4,strnlen_m3.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. apply strnlen_count_bound.
Qed.
Lemma strnlen_callee_args:forall s0 sc,strnlen_frame s0 (strnlen_m6 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ memchr_char sc=0 /\ memchr_count sc=strnlen_count s0.
Proof.
  intros s0 sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold memchr_char,memchr_count. rewrite MEM,SP. psimpl.
  rewrite strnlen_m6_arg,strnlen_m6_char,strnlen_m6_count. repeat split;reflexivity.
Qed.
Lemma strnlen_callee_memory:forall s0 sc used,
  strnlen_frame s0 (strnlen_m6 s0) 32 sc ->sc R_EBX=strnlen_got ->
  memchr_memory sc used=strnlen_memory s0 used.
Proof.
  intros s0 sc used FRAME BX.
  destruct (strnlen_callee_args s0 sc FRAME) as (P & C & N).
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  destruct used;unfold memchr_memory,memchr_local,save4_memory,save4_registers,memchr_endpoint,
    strnlen_memory,strnlen_m10,strnlen_m9,strnlen_m8,strnlen_m7,strnlen_endpoint;
  rewrite ?P,?N,MEM,SP,BX,SI,DI,BP;psimpl;reflexivity.
Qed.
Lemma strnlen_m6_byte:forall s0 i,strnlen_pre s0 ->i<strnlen_count s0 ->
  getmem 32 LittleE 1 (strnlen_m6 s0) (cdecl_arg s0+i)=
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i).
Proof.
  intros s0 i (_ & NO & NULL) I.
  unfold strnlen_m6,strnlen_m5,strnlen_m4,strnlen_m3,strnlen_m2,strnlen_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=52) (n:=strnlen_count s0)
    by (first[exact NO|clear - I;lia]). reflexivity.
Qed.
Lemma strnlen_nonnull_index:forall s0 i,strnlen_pre s0 ->i<strnlen_count s0 ->
  (cdecl_arg s0+i) mod 2^32<>0.
Proof.
  intros s0 i (_ & NO & NULL) I ZERO. apply NULL. exists 0,i.
  split;[reflexivity|]. split;[exact I|]. change (0=(cdecl_arg s0+i) mod 2^32). symmetry;exact ZERO.
Qed.

Lemma strnlen_callee_pre:forall s0 sc,strnlen_pre s0 ->models x86typctx sc ->
  strnlen_frame s0 (strnlen_m6 s0) 32 sc ->memchr_pre sc.
Proof.
  intros s0 sc (_ & NO & NULL) MDL FRAME.
  destruct (strnlen_callee_args s0 sc FRAME) as (P & C & N).
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold memchr_pre. rewrite P,N,SP. psimpl. split;[exact MDL|].
  apply descending_stack_subregion with (total:=52);try lia;exact NO.
Qed.
Lemma strnlen_search_transport:forall s0 result,strnlen_pre s0 ->
  forward_search_result (strnlen_m6 s0) (cdecl_arg s0) 0 (strnlen_count s0) result ->
  forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) result.
Proof.
  intros s0 result PRE RESULT.
  assert (PREFIX:forall k,k<=strnlen_count s0 ->
    nonmatching_prefix (strnlen_m6 s0) (cdecl_arg s0) 0 k ->
    nonmatching_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k).
  { intros k K EQ i I. assert (IN:i<strnlen_count s0) by
      (set (n:=strnlen_count s0) in *;clearbody n;clear - K I;lia).
    rewrite <- (strnlen_m6_byte s0 i PRE IN). exact (EQ i I). }
  destruct RESULT as [(k & K & EQ & ZERO & VALUE)|[VALUE EQ]].
  - left. exists k. split;[exact K|]. split.
    + apply PREFIX;[apply N.lt_le_incl;exact K|exact EQ].
    + rewrite <- (strnlen_m6_byte s0 k PRE K). exact (conj ZERO VALUE).
  - right. split;[exact VALUE|]. apply PREFIX;[apply N.le_refl|exact EQ].
Qed.
Lemma strnlen_null_result:forall s0,strnlen_pre s0 ->
  forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) 0 ->
  strnlen_result s0 (strnlen_count s0).
Proof.
  intros s0 PRE [(k & K & EQ & ZERO & VALUE)|[_ EQ]].
  - exfalso. apply (strnlen_nonnull_index s0 k PRE K). symmetry;exact VALUE.
  - left. split;[reflexivity|exact EQ].
Qed.
Lemma strnlen_found_result:forall s0 ptr,ptr<>0 ->
  forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) ptr ->
  strnlen_result s0 (msub 32 ptr (cdecl_arg s0)).
Proof.
  intros s0 ptr NONZERO [(k & K & PREFIX & ZERO & VALUE)|[VALUE EQ]];[|contradiction].
  pose proof (strnlen_count_bound s0) as COUNT.
  assert (BOUND:k<2^32) by (set (n:=strnlen_count s0) in *;clearbody n;clear - K COUNT;lia).
  right. exists k. split;[exact K|]. split.
  - exact (conj BOUND (conj PREFIX ZERO)).
  - rewrite VALUE. psimpl. reflexivity.
Qed.

Lemma strnlen_call_return:forall s0 sc sr used x se,
  strnlen_pre s0 ->strnlen_frame s0 (strnlen_m6 s0) 32 sc ->sc R_EBX=strnlen_got ->
  memchr_result sc (sr R_EAX) ->
  cdecl_returned (memchr_reference sc used) (sr R_EAX) x se ->
  x=Addr 0x7636d /\ strnlen_frame s0 (strnlen_memory s0 used) 28 se /\
  se R_EBX=strnlen_got /\
  forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) (se R_EAX).
Proof.
  intros s0 sc sr used x se PRE FRAME BX RESULT RETURN.
  destruct (strnlen_callee_args s0 sc FRAME) as (P & C & N).
  pose proof (strnlen_callee_memory s0 sc used FRAME BX) as SAVED.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,memchr_reference in RETURN. psimpl in RETURN.
  rewrite SAVED,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite strnlen_call_address in PC. split;[exact PC|]. split.
  - unfold strnlen_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - split;[exact EBX|]. rewrite AX.
    unfold memchr_result in RESULT. rewrite P,C,N,MEM in RESULT.
    apply strnlen_search_transport;assumption.
Qed.
