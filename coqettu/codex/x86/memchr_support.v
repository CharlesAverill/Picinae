(* Contracts and memory snapshots for the optimized musl i386 memchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack4 i386_byte_search i386_search_arith.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition memchr_char (s0:store):=getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP).
Definition memchr_count (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition memchr_endpoint (s0:store):=(cdecl_arg s0+memchr_count s0) mod 2^32.
Definition memchr_local (s0:store) (used:bool):=if used then Some (memchr_endpoint s0) else None.
Definition memchr_memory (s0:store) (used:bool):=save4_memory s0 (memchr_local s0 used).
Definition memchr_reference (s0:store) (used:bool):=s0[V_MEM32:=memchr_memory s0 used].
Definition memchr_frame (s0:store) (used:bool) (s:store):=
  s V_MEM32=memchr_memory s0 used /\ s R_ESP=msub 32 (s0 R_ESP) 20 /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition memchr_pre (s0:store):=models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 20) 20 (cdecl_arg s0) (memchr_count s0).
Definition memchr_result (s0:store) result:=forward_search_result (s0 V_MEM32)
  (cdecl_arg s0) (memchr_char s0) (memchr_count s0) result.
Definition memchr_prefix (s0:store) k:=nonmatching_prefix (s0 V_MEM32) (cdecl_arg s0) (memchr_char s0) k.
Definition memchr_align (s0 s:store):=memchr_frame s0 false s /\ s R_EBX=memchr_char s0 /\
  exists k,k<=memchr_count s0 /\ s R_EAX=memchr_count s0-k /\
    s R_EDX=(cdecl_arg s0+k) mod 2^32 /\ memchr_prefix s0 k.
Definition memchr_setup (s0 s:store):=memchr_frame s0 false s /\ s R_EBX=memchr_char s0 /\
  exists k,k<memchr_count s0 /\ s R_EAX=memchr_count s0-k /\
    s R_EDX=(cdecl_arg s0+k) mod 2^32 /\ memchr_prefix s0 k.
Definition memchr_words (s0 s:store):=memchr_frame s0 true s /\ s R_EBX=memchr_char s0 /\
  s R_EBP=repeated_byte32 (memchr_char s0) /\ exists k e,
    k<=e /\ e<=memchr_count s0 /\ (e-k) mod 4=0 /\
    s R_EDX=(cdecl_arg s0+k) mod 2^32 /\
    s R_ECX=(cdecl_arg s0+e) mod 2^32 /\ memchr_prefix s0 k.
Definition memchr_tail (s0 s:store):=exists used,memchr_frame s0 used s /\ s R_EBX=memchr_char s0 /\
  exists k,k<=memchr_count s0 /\ s R_EAX=memchr_count s0-k /\
    s R_ECX=(cdecl_arg s0+k) mod 2^32 /\ memchr_prefix s0 k.
Definition memchr_prepop (s0 s:store):=exists used,
  memchr_frame s0 used s /\ memchr_result s0 (s R_ECX).
Definition memchr_post (s0 s:store):=exists used,
  cdecl_leaf_frame (memchr_reference s0 used) s /\ memchr_result s0 (s R_EAX).
Lemma memchr_char_bound:forall s0,memchr_char s0<256.
Proof. intros s0. unfold memchr_char. apply getmem_bound. Qed.
Lemma memchr_count_bound:forall s0,memchr_count s0<2^32.
Proof. intros s0. unfold memchr_count. apply getmem_bound. Qed.
Lemma memchr_region_read:forall s0 used off len,
  memchr_pre s0 ->off+len<=memchr_count s0 ->
  getmem 32 LittleE len (memchr_memory s0 used) (cdecl_arg s0+off)=
  getmem 32 LittleE len (s0 V_MEM32) (cdecl_arg s0+off).
Proof. intros s0 used off len [_ NO] FIT. apply save4_region_read with (n:=memchr_count s0);assumption. Qed.
Lemma memchr_local_load:forall s0,
  getmem 32 LittleE 4 (memchr_memory s0 true) (msub 32 (s0 R_ESP) 20)=memchr_endpoint s0.
Proof.
  intros s0. unfold memchr_memory,memchr_local. rewrite save4_local_load.
  unfold memchr_endpoint. apply mp2_mod_mod.
Qed.

Lemma memchr_prefix_step1:forall s0 used k,
  memchr_pre s0 ->k<memchr_count s0 ->memchr_prefix s0 k ->
  getmem 32 LittleE 1 (memchr_memory s0 used) (cdecl_arg s0+k)<>memchr_char s0 ->
  memchr_prefix s0 (k+1).
Proof.
  intros s0 used k PRE K PREFIX BYTE.
  rewrite (memchr_region_read s0 used k 1 PRE ltac:(clear - K;lia)) in BYTE.
  apply nonmatching_prefix_advance1;[exact PREFIX|]. rewrite getmem_mod_l. exact BYTE.
Qed.
Lemma memchr_prefix_step4:forall s0 k,
  memchr_pre s0 ->k+4<=memchr_count s0 ->memchr_prefix s0 k ->
  zero_mask32 (N.lxor (getmem 32 LittleE 4 (memchr_memory s0 true) (cdecl_arg s0+k))
    (repeated_byte32 (memchr_char s0)))=0 ->memchr_prefix s0 (k+4).
Proof.
  intros s0 k PRE K PREFIX MASK.
  rewrite (memchr_region_read s0 true k 4 PRE K) in MASK.
  apply nonmatching_prefix_advance4;[apply memchr_char_bound|exact PREFIX|].
  rewrite getmem_mod_l. exact MASK.
Qed.
Lemma memchr_found:forall s0 used k,
  memchr_pre s0 ->k<memchr_count s0 ->memchr_prefix s0 k ->
  getmem 32 LittleE 1 (memchr_memory s0 used) (cdecl_arg s0+k)=memchr_char s0 ->
  memchr_result s0 ((cdecl_arg s0+k) mod 2^32).
Proof.
  intros s0 used k PRE K PREFIX BYTE. left. exists k.
  split;[exact K|]. split;[exact PREFIX|]. split;[|reflexivity].
  rewrite <- (memchr_region_read s0 used k 1 PRE ltac:(clear - K;lia)). exact BYTE.
Qed.
Lemma memchr_exhausted:forall s0 k,
  k<=memchr_count s0 ->memchr_count s0-k=0 ->memchr_prefix s0 k ->memchr_result s0 0.
Proof.
  intros s0 k K ZERO PREFIX. right. split;[reflexivity|].
  assert (EQ:k=memchr_count s0) by (set (n:=memchr_count s0) in *;clearbody n;clear - K ZERO;lia).
  rewrite <- EQ. exact PREFIX.
Qed.

Lemma memchr_remaining_load:forall s0 k,k<=memchr_count s0 ->
  msub 32 (msub 32 (getmem 32 LittleE 4 (memchr_memory s0 true)
    (msub 32 (s0 R_ESP) 20)) (cdecl_arg s0)) k=memchr_count s0-k.
Proof.
  intros s0 k K. rewrite memchr_local_load. unfold memchr_endpoint. psimpl.
  rewrite msub_sub by exact K. apply N.mod_small.
  pose proof (memchr_count_bound s0). clear - K H;lia.
Qed.
