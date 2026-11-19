(* Linked code and exact caller stack snapshots for musl i386 wcsnlen. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_strings i386_wstrlen
  wcsnlen_i386 pc_thunk_bx_i386 wmemchr_i386 wmemchr_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcsnlen_linked : program := updateall2 wcsnlen_i386 (updateall2 pc_thunk_bx_i386 wmemchr_i386).
Lemma wcsnlen_linked_caller : wcsnlen_i386 ⊆2 wcsnlen_linked.
Proof.
  intros s a insn H. unfold wcsnlen_linked,updateall2,updateall,wcsnlen_i386,pc_thunk_bx_i386,wmemchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wcsnlen_linked_wmemchr : wmemchr_i386 ⊆2 wcsnlen_linked.
Proof. intros s a insn H. unfold wcsnlen_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wcsnlen_linked_thunk : pc_thunk_bx_i386 ⊆2 wcsnlen_linked.
Proof.
  intros s a insn H. unfold wcsnlen_linked,updateall2,updateall,pc_thunk_bx_i386,wmemchr_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wcsnlen_linked_welltyped : welltyped_prog x86typctx wcsnlen_linked.
Proof.
  intros s a. unfold wcsnlen_linked,updateall2,updateall.
  destruct (wmemchr_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (wmemchr_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wcsnlen_i386.welltyped.
Qed.

Definition wcsnlen_count (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wcsnlen_got:N:=0xb4f9c.
Definition wcsnlen_m1 (s0:store):=save_ebx_memory s0.
Definition wcsnlen_m2 (s0:store):=setmem 32 LittleE 4 (wcsnlen_m1 s0) (msub 32 (s0 R_ESP) 8) 0x768a6.
Definition wcsnlen_m3 (s0:store):=setmem 32 LittleE 4 (wcsnlen_m2 s0) (msub 32 (s0 R_ESP) 20) (wcsnlen_count s0).
Definition wcsnlen_m4 (s0:store):=setmem 32 LittleE 4 (wcsnlen_m3 s0) (msub 32 (s0 R_ESP) 24) 0.
Definition wcsnlen_m5 (s0:store):=setmem 32 LittleE 4 (wcsnlen_m4 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition wcsnlen_m6 (s0:store):=setmem 32 LittleE 4 (wcsnlen_m5 s0) (msub 32 (s0 R_ESP) 32) 0x768be.
Definition wcsnlen_reference (s0:store):=s0[V_MEM32:=wcsnlen_m6 s0].
Definition wcsnlen_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition wcsnlen_pre (s0:store):=models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 32) 32 (cdecl_arg s0) (4*wcsnlen_count s0) /\
  ~overlap 32 0 1 (cdecl_arg s0) (4*wcsnlen_count s0).
Definition wcsnlen_search (s0:store) (result:N):=
  (exists k,k<wcsnlen_count s0 /\ wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k /\
    getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)=0 /\
    result=(cdecl_arg s0+4*k) mod 2^32) \/
  (result=0 /\ wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 (wcsnlen_count s0)).
Definition wcsnlen_result (s0:store) (result:N):=
  (result=wcsnlen_count s0 /\ wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 (wcsnlen_count s0)) \/
  (exists k,k<wcsnlen_count s0 /\ wide_first_nul (s0 V_MEM32) (cdecl_arg s0) k /\ result=wide_length32 k).
Lemma wcsnlen_count_bound:forall s0,wcsnlen_count s0<2^32.
Proof. intros s0. unfold wcsnlen_count. apply getmem_bound. Qed.
Lemma wcsnlen_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcsnlen_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcsnlen_m2,wcsnlen_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma wcsnlen_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcsnlen_m6,wcsnlen_m5,wcsnlen_m4,wcsnlen_m3,wcsnlen_m2,wcsnlen_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma wcsnlen_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold wcsnlen_m6,wcsnlen_m5,wcsnlen_m4,wcsnlen_m3,wcsnlen_m2,wcsnlen_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma wcsnlen_call_address:forall s0,
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (msub 32 (s0 R_ESP) 32)=0x768be.
Proof. intros s0. unfold wcsnlen_m6. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma wcsnlen_m6_arg:forall s0,
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (msub 32 (s0 R_ESP) 28)=cdecl_arg s0.
Proof.
  intros s0. unfold wcsnlen_m6,wcsnlen_m5. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small. unfold cdecl_arg. apply getmem_bound.
Qed.
Lemma wcsnlen_m6_char:forall s0,
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (msub 32 (s0 R_ESP) 24)=0.
Proof.
  intros s0. unfold wcsnlen_m6,wcsnlen_m5,wcsnlen_m4.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia. reflexivity.
Qed.
Lemma wcsnlen_m6_count:forall s0,
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (msub 32 (s0 R_ESP) 20)=wcsnlen_count s0.
Proof.
  intros s0. unfold wcsnlen_m6,wcsnlen_m5,wcsnlen_m4,wcsnlen_m3.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. apply wcsnlen_count_bound.
Qed.
Lemma wcsnlen_callee_args:forall s0 sc,wcsnlen_frame s0 (wcsnlen_m6 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ wmemchr_char sc=0 /\ wmemchr_count sc=wcsnlen_count s0.
Proof.
  intros s0 sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold wmemchr_char,wmemchr_count. rewrite MEM,SP. psimpl.
  rewrite wcsnlen_m6_arg,wcsnlen_m6_char,wcsnlen_m6_count. repeat split;reflexivity.
Qed.
Lemma wcsnlen_m6_wide:forall s0 i,wcsnlen_pre s0 ->i<wcsnlen_count s0 ->
  getmem 32 LittleE 4 (wcsnlen_m6 s0) (cdecl_arg s0+4*i)=
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*i).
Proof.
  intros s0 i (_ & NO & NULL) I.
  assert (FIT:4*i+4<=4*wcsnlen_count s0) by
    (set (n:=wcsnlen_count s0) in *;clearbody n;clear - I;lia).
  unfold wcsnlen_m6,wcsnlen_m5,wcsnlen_m4,wcsnlen_m3,wcsnlen_m2,wcsnlen_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=32) (n:=4*wcsnlen_count s0)
    by (first[exact NO|exact FIT|lia]). reflexivity.
Qed.
Lemma wcsnlen_nonnull_index:forall s0 i,wcsnlen_pre s0 ->i<wcsnlen_count s0 ->
  (cdecl_arg s0+4*i) mod 2^32<>0.
Proof.
  intros s0 i (_ & NO & NULL) I ZERO. apply NULL. exists 0,(4*i).
  split;[reflexivity|]. split.
  - set (n:=wcsnlen_count s0) in *;clearbody n;clear - I;lia.
  - change (0=(cdecl_arg s0+4*i) mod 2^32). symmetry;exact ZERO.
Qed.
Lemma wcsnlen_search_transport:forall s0 sc result,wcsnlen_pre s0 ->
  wcsnlen_frame s0 (wcsnlen_m6 s0) 32 sc ->wmemchr_result sc result ->wcsnlen_search s0 result.
Proof.
  intros s0 sc result PRE FRAME RESULT.
  destruct (wcsnlen_callee_args s0 sc FRAME) as (P & C & N).
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold wmemchr_result in RESULT. rewrite P,C,N,MEM in RESULT.
  assert (PREFIX:forall k,k<=wcsnlen_count s0 ->
    wide_prefix (wcsnlen_m6 s0) (cdecl_arg s0) 0 k ->
    wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k).
  { intros k K EQ i I. assert (IN:i<wcsnlen_count s0) by
      (set (n:=wcsnlen_count s0) in *;clearbody n;clear - K I;lia).
    rewrite <- (wcsnlen_m6_wide s0 i PRE IN). exact (EQ i I). }
  destruct RESULT as [(k & K & EQ & ZERO & VALUE)|[VALUE EQ]].
  - left. exists k. split;[exact K|]. split.
    + apply PREFIX;[apply N.lt_le_incl;exact K|exact EQ].
    + rewrite <- (wcsnlen_m6_wide s0 k PRE K). exact (conj ZERO VALUE).
  - right. split;[exact VALUE|]. apply PREFIX;[apply N.le_refl|exact EQ].
Qed.
Lemma wcsnlen_null_result:forall s0,wcsnlen_pre s0 ->wcsnlen_search s0 0 ->
  wcsnlen_result s0 (wcsnlen_count s0).
Proof.
  intros s0 PRE [(k & K & EQ & ZERO & VALUE)|[_ EQ]].
  - exfalso. apply (wcsnlen_nonnull_index s0 k PRE K). symmetry;exact VALUE.
  - left. split;[reflexivity|exact EQ].
Qed.
Lemma wcsnlen_found_result:forall s0 ptr,ptr<>0 ->wcsnlen_search s0 ptr ->
  wcsnlen_result s0 (ashiftr 32 (msub 32 ptr (cdecl_arg s0)) 2).
Proof.
  intros s0 ptr NONZERO [(k & K & PREFIX & ZERO & VALUE)|[VALUE EQ]];[|contradiction].
  right. exists (k mod 2^30). split.
  - pose proof (mp2_mod_le k 30). set (n:=wcsnlen_count s0) in *;clearbody n;clear - K H;lia.
  - split.
    + apply wide_prefix_stop;[exact PREFIX|]. rewrite getmem_mod_l. exact ZERO.
    + rewrite VALUE. rewrite msub_mod_l by reflexivity. rewrite add_msub_l. change (wide_length32 k=wide_length32 (k mod 2^30)).
      symmetry. apply wide_length32_reduce.
Qed.
Lemma wcsnlen_call_return:forall s0 sc sr x se,
  wcsnlen_pre s0 ->wcsnlen_frame s0 (wcsnlen_m6 s0) 32 sc ->sc R_EBX=wcsnlen_got ->
  wmemchr_result sc (sr R_EAX) ->cdecl_returned sc (sr R_EAX) x se ->
  x=Addr 0x768be /\ wcsnlen_frame s0 (wcsnlen_m6 s0) 28 se /\
  se R_EBX=wcsnlen_got /\ wcsnlen_search s0 (se R_EAX).
Proof.
  intros s0 sc sr x se PRE FRAME BX RESULT RETURN.
  pose proof (wcsnlen_search_transport s0 sc _ PRE FRAME RESULT) as SEARCH.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned in RETURN. rewrite MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite wcsnlen_call_address in PC. split;[exact PC|]. split.
  - unfold wcsnlen_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - split;[exact EBX|]. rewrite AX. exact SEARCH.
Qed.
