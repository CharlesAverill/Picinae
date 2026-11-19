(* Shared stack snapshots for PIC wrappers calling a pure unary callee. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_stack i386_deep_stack i386_calls.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition unary_m1 (s0:store):=save_ebx_memory s0.
Definition unary_m2 (s0:store) (thunk_ra:N):=
  setmem 32 LittleE 4 (unary_m1 s0) (msub 32 (s0 R_ESP) 8) thunk_ra.
Definition unary_m3 (s0:store) (thunk_ra:N):=
  setmem 32 LittleE 4 (unary_m2 s0 thunk_ra) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition unary_memory (s0:store) (thunk_ra call_ra:N):=
  setmem 32 LittleE 4 (unary_m3 s0 thunk_ra) (msub 32 (s0 R_ESP) 32) call_ra.
Definition unary_reference (s0:store) (thunk_ra call_ra:N):=
  s0[V_MEM32:=unary_memory s0 thunk_ra call_ra].
Definition unary_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Lemma unary_m2_stack:forall s0 tr off,off<=8 ->
  getmem 32 LittleE 4 (unary_m2 s0 tr) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 tr off OFF. unfold unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma unary_outer_stack:forall s0 tr cr off,off<=8 ->
  getmem 32 LittleE 4 (unary_memory s0 tr cr) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 tr cr off OFF. unfold unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma unary_saved_bx:forall s0 tr cr,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (unary_memory s0 tr cr) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 tr cr BOUND. unfold unary_memory,unary_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma unary_call_address:forall s0 tr cr,
  getmem 32 LittleE 4 (unary_memory s0 tr cr) (msub 32 (s0 R_ESP) 32)=cr mod 2^32.
Proof. intros s0 tr cr. unfold unary_memory. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma unary_callee_arg:forall s0 tr cr sc,
  unary_frame s0 (unary_memory s0 tr cr) 32 sc ->cdecl_arg sc=cdecl_arg s0.
Proof.
  intros s0 tr cr sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. rewrite MEM,SP. psimpl. unfold unary_memory,unary_m3.
  rewrite deep_saved_word_frame by lia. rewrite getmem_setmem by lia.
  apply N.mod_small. unfold cdecl_arg. apply getmem_bound.
Qed.
Lemma unary_call_return:forall s0 tr cr got (value:N->N) sc x se,
  unary_frame s0 (unary_memory s0 tr cr) 32 sc ->sc R_EBX=got ->
  cdecl_returned sc (value (cdecl_arg sc)) x se ->
  x=Addr (cr mod 2^32) /\ unary_frame s0 (unary_memory s0 tr cr) 28 se /\
  se R_EBX=got /\ se R_EAX=value (cdecl_arg s0).
Proof.
  intros s0 tr cr got value sc x se FRAME BX RETURN.
  pose proof (unary_callee_arg s0 tr cr sc FRAME) as ARG.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned in RETURN. rewrite ARG,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite unary_call_address in PC. split;[exact PC|]. split.
  - unfold unary_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.

Lemma unary_leaf_supported:forall own entry ret s0 value,
  (forall s,own s entry<>None) ->(forall s,own s ret<>None) ->
  code_supported own (leaf_invs entry ret s0 value) (at_address ret).
Proof.
  intros own entry ret s0 value EN RT [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold leaf_invs,at_address. destruct (a=?entry) eqn:E.
  - apply N.eqb_eq in E. subst a. exfalso. exact (EN s NO).
  - destruct (a=?ret) eqn:R;[|split;reflexivity].
    apply N.eqb_eq in R. subst a. exfalso. exact (RT s NO).
Qed.
