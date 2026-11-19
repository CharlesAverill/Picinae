(* Three-argument PIC call snapshots and count-bounded prefix transport. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_unary_call i386_binary_call.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition ternary_arg3 (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition ternary_m3 (s0:store) (tr:N):=
  setmem 32 LittleE 4 (unary_m2 s0 tr) (msub 32 (s0 R_ESP) 20) (ternary_arg3 s0).
Definition ternary_m4 (s0:store) (tr:N):=
  setmem 32 LittleE 4 (ternary_m3 s0 tr) (msub 32 (s0 R_ESP) 24) (binary_arg2 s0).
Definition ternary_m5 (s0:store) (tr:N):=
  setmem 32 LittleE 4 (ternary_m4 s0 tr) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition ternary_entry_memory (s0:store) (tr cr:N):=
  setmem 32 LittleE 4 (ternary_m5 s0 tr) (msub 32 (s0 R_ESP) 32) cr.
Lemma ternary_callee_args:forall s0 tr cr sc,
  unary_frame s0 (ternary_entry_memory s0 tr cr) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ binary_arg2 sc=binary_arg2 s0 /\ ternary_arg3 sc=ternary_arg3 s0.
Proof.
  intros s0 tr cr sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold binary_arg2 at 1. unfold ternary_arg3 at 1. rewrite MEM,SP. psimpl.
  unfold ternary_entry_memory,ternary_m5,ternary_m4,ternary_m3. split;[|split].
  all: repeat (rewrite deep_saved_word_frame by lia);rewrite getmem_setmem by lia;apply N.mod_small.
  - unfold cdecl_arg;apply getmem_bound.
  - unfold binary_arg2;apply getmem_bound.
  - unfold ternary_arg3;apply getmem_bound.
Qed.
Lemma ternary_outer_stack:forall s0 tr cr off,off<=16 ->
  getmem 32 LittleE 4 (ternary_entry_memory s0 tr cr) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 tr cr off OFF. unfold ternary_entry_memory,ternary_m5,ternary_m4,ternary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma ternary_saved_bx:forall s0 tr cr,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (ternary_entry_memory s0 tr cr) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 tr cr BOUND. unfold ternary_entry_memory,ternary_m5,ternary_m4,ternary_m3,unary_m2.
  repeat (rewrite deep_saved_word_frame by lia). apply saved_ebx_load;exact BOUND.
Qed.
Lemma ternary_call_address:forall s0 tr cr,
  getmem 32 LittleE 4 (ternary_entry_memory s0 tr cr) (msub 32 (s0 R_ESP) 32)=cr mod 2^32.
Proof. intros. unfold ternary_entry_memory. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma conditional_prefix_transfer_bounded:forall (r1 r2:N->N) bound,
  (forall k,k<bound ->(forall i,i<k ->r1 i<>0) ->r2 k=r1 k) ->
  forall k,k<=bound ->(forall i,i<k ->r2 i<>0) ->forall i,i<k ->r1 i<>0.
Proof.
  intros r1 r2 bound READ k. induction k using N.peano_ind.
  - intros B P i I. lia.
  - intros B P i I. assert (OLD:forall j,j<k ->r1 j<>0).
    { apply IHk;[lia|]. intros j J. apply P;lia. }
    destruct (N.lt_ge_cases i k) as [LT|GE];[exact (OLD i LT)|].
    replace i with k by lia. rewrite <- (READ k ltac:(lia) OLD). apply P;lia.
Qed.
