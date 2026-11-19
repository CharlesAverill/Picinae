(* strcoll -- musl i386 non-leaf collation with thread locale

   SEMANTICS / SPECIFICATION
   This binary reads the thread locale through GS and forwards to strcoll_l,
   whose checked contract ignores every locale representation. Result is the
   original-memory lexical comparison (exact unsigned-byte difference).
   Source: local Linux man-pages6.9.1, strcoll(3), paraphrased;
   binary call composition establishes locale-independent comparison here.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Global entry0x55300, RET0x55329, image base0x10000.
   Ghidra12.0 PUBLIC frozen strict typed lifter plus exact i386 GS-base name
   mapping (register0x114/32) documented and tested in segment_adapter.py.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Two pointers at ESP+4/+8 and declared register widths. Each original input
   through its first NUL avoids the72-byte nested frame. No caller lengths,
   stopping witnesses or locale-value restrictions. Actual GS loads remain
   modeled; exact memory includes the fetched locale word and nested call slots.
   Preserve all callee-saved registers, permissions and original return address.
   Partial correctness in all containing programs; no termination/access claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call
  strcoll_support strcoll_i386 pc_thunk_bx_i386 strcoll_l_i386 strcoll_l_proof
  strcoll_l_support i386_tls_call i386_strings i386_stringcmp i386_wstringcmp strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcoll_post (s0 s:store):=
  cdecl_leaf_frame (strcoll_reference s0) s /\ strcoll_result s0 (s R_EAX).
Definition strcoll_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x55300=>Some (s=s0)
  | 0x55301=>Some (strcoll_frame s0 (strcoll_m1 s0) 4 s /\ s R_GS_BASE=s0 R_GS_BASE)
  | 0x55306=>Some (strcoll_frame s0 (strcoll_m2 s0) 4 s /\ s R_EBX=0x55306 /\ s R_GS_BASE=s0 R_GS_BASE)
  | 0x55320=>Some (strcoll_frame s0 (strcoll_m5 s0) 28 s /\ s R_EBX=strcoll_got)
  | 0x55325=>Some (strcoll_frame s0 (strcoll_memory s0) 28 s /\
      s R_EBX=strcoll_got /\ strcoll_result s0 (s R_EAX))
  | 0x55329=>Some (strcoll_post s0 s)
  | _=>None end | _=>None end.
Definition strcoll_exit:=at_address 0x55329.
Lemma strcoll_l_nested_code_supported:forall s0,
  code_supported strcoll_l_linked (strcoll_l_invs s0) strcoll_l_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strcoll_l_linked,updateall2,updateall,strcoll_l_i386,pc_thunk_bx_i386,strcmp_i386 in NO.
  unfold strcoll_l_invs,strcoll_l_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strcoll_strcoll_l_disjoint:forall s0 a s t,strcoll_l_linked s a<>None ->
  strcoll_invs s0 ((Addr a,s)::t)=None /\ strcoll_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strcoll_l_linked,updateall2,updateall,strcoll_l_i386,pc_thunk_bx_i386,strcmp_i386 in CODE.
  unfold strcoll_invs,strcoll_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strcoll_strcoll_l_call:forall s0 sc,strcoll_pre s0 ->models x86typctx sc ->
  strcoll_frame s0 (strcoll_m6 s0) 32 sc ->sc R_EBX=strcoll_got ->forall t,
  nextinv strcoll_linked (strcoll_invs s0) strcoll_exit true ((Addr 0x552df,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (strcoll_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strcoll_l_linked (strcoll_l_invs sc)) (xp2:=strcoll_l_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strcoll_linked_callee.
    + intros a s h EX NO. exact (proj1 (strcoll_l_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strcoll_l_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strcoll_linked_callee.
    + apply strcoll_l_nested_code_supported.
    + apply strcoll_strcoll_l_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strcoll_l_exit,at_address in POST.
    destruct (a=?0x552ff) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strcoll_l_post sc sr) in POST. destruct POST as [FRAME0 OUT].
    pose proof (strcoll_result_back s0 sc (sr R_EAX) PRE0 FRAME OUT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strcoll_l_reference sc) (sr R_EAX)
      (exitof (0x552ff+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strcoll_linked) (ret:=0x552ff) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strcoll_call_return s0 sc _ _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (
      strcoll_frame s0 (strcoll_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strcoll_got /\
      strcoll_result s0 ((reset_temps sr s2) R_EAX)).
    rewrite R. exact (conj F (conj B ORIGINAL)).
Qed.
Theorem strcoll_correct_local:forall s0 (PRE0:strcoll_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55300,s0)),
  satisfies_all strcoll_linked (strcoll_invs s0) strcoll_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x55300,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strcoll_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strcoll_frame,unary_frame,strcoll_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F GS]. unfold strcoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcoll_frame,unary_frame,strcoll_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as (F & BX & GS). unfold strcoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcoll_frame,unary_frame,strcoll_m5,tls_m5,tls_m4,tls_m3,tls_locale,tls_root,strcoll_got.
      psimpl;elimstore;psimpl.
      rewrite ?GS. rewrite !strcoll_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strcoll_linked_welltyped|].
      intro CMDL. apply strcoll_strcoll_l_call;[exact PRE0|exact CMDL| |].
      * unfold strcoll_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strcoll_m6,tls_entry. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as (F & BX & OUT). unfold strcoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold strcoll_post,cdecl_leaf_frame,strcoll_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strcoll_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact OUT].
Qed.

Theorem strcoll_correct:forall prog (EXT:strcoll_linked ⊆2 prog) s0 (PRE0:strcoll_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55300,s0)),
  satisfies_all prog (strcoll_invs s0) strcoll_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strcoll_invs,strcoll_linked,updateall2,updateall,
      strcoll_i386,pc_thunk_bx_i386,strcoll_l_i386,strcmp_i386,strcoll_l_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strcoll_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strcoll_returns:forall prog (EXT:strcoll_linked ⊆2 prog) s0 (PRE0:strcoll_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x55329,s)=(Addr 0x55300,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x55329,s)::t)) (UT:unterminated strcoll_exit t),
  exists value,strcoll_result s0 value /\ cdecl_returned (strcoll_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strcoll_correct prog EXT s0 PRE0 t (Addr 0x55329,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strcoll_post s0 s) in INV. destruct INV as [FRAME OUT].
  assert (RETURN:cdecl_returned (strcoll_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x55329) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strcoll_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (strcoll_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
