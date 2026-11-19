(* strchr -- musl i386, non-leaf byte search

   SEMANTICS / SPECIFICATION
   Return the first occurrence of the int argument converted to unsigned char,
   or NULL if absent. The terminator participates in the search. Source: local
   Linux man-pages 6.9.1, /usr/share/man/man3/strchr.3.gz (paraphrased).
   No input length, terminator or match witness is a caller premise.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x6605e, image base 0x10000, global RET 0x7607d.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and int argument: entry ESP+4 and ESP+8, with declared register widths.
   Every four-byte read through the first NUL avoids the 80-byte nested frame.
   All int bit patterns are accepted. The actual strchrnul call includes its
   PIC thunk, optimized mask scans and conditional strlen call. Exact memory
   records eight effective stack-word writes, or ten for a zero needle.
   All four callee-saved registers, permissions and original return address
   are restored; RET adds four. Partial correctness in every containing
   program; termination and successful concrete accesses are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_binary_call
  i386_strings i386_byte_search strchr_support strchr_i386
  strchrnul_support strchrnul_proof strchrnul_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strchr_post (s0 s:store):=
  cdecl_leaf_frame (strchr_reference s0) s /\ strchr_result s0 (s R_EAX).
Definition strchr_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x7605e=>Some (s=s0)
  | 0x76069=>Some (strchr_frame s0 (strchr_m2 s0) 28 s)
  | 0x7606e=>Some (strchr_frame s0 (strchr_memory s0) 28 s /\ strchrnul_result s0 (s R_EAX))
  | 0x7607d=>Some (strchr_post s0 s)
  | _=>None end | _=>None end.
Definition strchr_exit:=at_address 0x7607d.
Lemma strchr_callee_supported:forall s0,code_supported strchrnul_linked (strchrnul_invs s0) strchrnul_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strchrnul_linked,updateall2,updateall,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in NO.
  unfold strchrnul_invs,strchrnul_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strchr_callee_disjoint:forall s0 a s t,strchrnul_linked s a<>None ->
  strchr_invs s0 ((Addr a,s)::t)=None /\ strchr_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strchrnul_linked,updateall2,updateall,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in CODE.
  unfold strchr_invs,strchr_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strchr_callee_call:forall s0 sc,strchr_pre s0 ->strchr_frame s0 (strchr_m3 s0) 32 sc ->
  models x86typctx sc ->forall t,
  nextinv strchr_linked (strchr_invs s0) strchr_exit true ((Addr 0x31400,sc)::t).
Proof.
  intros s0 sc PRE FRAME MDL t. pose proof (strchr_callee_pre s0 sc PRE FRAME MDL) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strchrnul_linked (strchrnul_invs sc)) (xp2:=strchrnul_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strchr_linked_callee.
    + intros a s h EX NO. exact (proj1 (strchr_callee_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strchrnul_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strchr_linked_callee.
    + apply strchr_callee_supported.
    + apply strchr_callee_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strchrnul_exit,at_address in POST.
    destruct (a=?0x31453) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strchrnul_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (strchr_result_back s0 sc _ PRE FRAME RESULT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strchrnul_reference sc) (sr R_EAX)
      (exitof (0x31453+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strchr_linked) (ret:=0x31453) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strchr_call_return s0 sc _ _ _ FRAME RETURN) as (PC & RF & VALUE).
    rewrite PC. apply NIHere'. change (strchr_frame s0 (strchr_memory s0) 28 (reset_temps sr s2) /\
      strchrnul_result s0 ((reset_temps sr s2) R_EAX)).
    rewrite VALUE. exact (conj RF ORIGINAL).
Qed.
Theorem strchr_correct_local:forall s0 (PRE0:strchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x7605e,s0)),
  satisfies_all strchr_linked (strchr_invs s0) strchr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x7605e,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strchr_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strchr_frame,strchr_m2,strchr_m1. psimpl;elimstore;psimpl.
      unfold cdecl_arg,binary_arg2. repeat split;reflexivity.
    + ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strchr_linked_welltyped|].
      intro CMDL. apply strchr_callee_call;[exact PRE0| |exact CMDL].
      unfold strchr_frame in *. destruct PRE as (MEM & SP & BX & SI & DI & BP & RD & WR).
      unfold strchr_m3. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F [k [PREFIX [STOP VALUE]]]].
      pose proof (strchr_read_byte s0 true k PRE0 (proj1 PREFIX)) as READ.
      change (getmem 32 LittleE 1 (strchr_memory s0) (cdecl_arg s0+k)=
        getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)) in READ.
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof (strchrnul_char_bound s0) as CHAR. clear PRE0 MDL.
      unfold strchr_frame in F. destruct F as (MEM & SP & BX & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold strchr_post,cdecl_leaf_frame,strchr_reference;psimpl;elimstore;psimpl.
      all: rewrite ?strchr_outer_char,?VALUE,?getmem_mod_l,?READ in *;csimpl.
      all: rewrite (N.mod_small _ _ SPBOUND).
      all: split;[repeat split;first[reflexivity|assumption]|].
      * exists k. split;[exact PREFIX|]. left. split;[assumption|reflexivity].
      * exists k. split;[exact PREFIX|]. right. destruct STOP;[|contradiction]. repeat split;first[assumption|congruence].
Qed.
Theorem strchr_correct:forall prog (EXT:strchr_linked ⊆2 prog) s0 (PRE0:strchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x7605e,s0)),
  satisfies_all prog (strchr_invs s0) strchr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strchr_invs,strchr_linked,strchrnul_linked,updateall2,updateall,
      strchr_i386,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strchr_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strchr_returns:forall prog (EXT:strchr_linked ⊆2 prog) s0 (PRE0:strchr_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x7607d,s)=(Addr 0x7605e,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x7607d,s)::t)) (UT:unterminated strchr_exit t),
  exists value,strchr_result s0 value /\ cdecl_returned (strchr_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strchr_correct prog EXT s0 PRE0 t (Addr 0x7607d,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strchr_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (strchr_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x7607d) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strchr_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (strchr_outer_stack s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
