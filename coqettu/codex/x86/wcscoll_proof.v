(* wcscoll -- musl i386 non-leaf collation with thread locale

   SEMANTICS / SPECIFICATION
   This binary reads the thread locale through GS and forwards to wcscoll_l,
   whose checked contract ignores every locale representation. Result is the
   original-memory lexical comparison (signed wide-character ordering).
   Source: local Linux man-pages6.9.1, wcscoll(3), paraphrased;
   binary call composition establishes locale-independent comparison here.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Global entry0x55592, RET0x555bb, image base0x10000.
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
  wcscoll_support wcscoll_i386 pc_thunk_bx_i386 wcscoll_l_i386 wcscoll_l_proof
  wcscoll_l_support i386_tls_call i386_strings i386_stringcmp i386_wstringcmp wcscmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcscoll_post (s0 s:store):=
  cdecl_leaf_frame (wcscoll_reference s0) s /\ wcscoll_result s0 (s R_EAX).
Definition wcscoll_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x55592=>Some (s=s0)
  | 0x55593=>Some (wcscoll_frame s0 (wcscoll_m1 s0) 4 s /\ s R_GS_BASE=s0 R_GS_BASE)
  | 0x55598=>Some (wcscoll_frame s0 (wcscoll_m2 s0) 4 s /\ s R_EBX=0x55598 /\ s R_GS_BASE=s0 R_GS_BASE)
  | 0x555b2=>Some (wcscoll_frame s0 (wcscoll_m5 s0) 28 s /\ s R_EBX=wcscoll_got)
  | 0x555b7=>Some (wcscoll_frame s0 (wcscoll_memory s0) 28 s /\
      s R_EBX=wcscoll_got /\ wcscoll_result s0 (s R_EAX))
  | 0x555bb=>Some (wcscoll_post s0 s)
  | _=>None end | _=>None end.
Definition wcscoll_exit:=at_address 0x555bb.
Lemma wcscoll_l_nested_code_supported:forall s0,
  code_supported wcscoll_l_linked (wcscoll_l_invs s0) wcscoll_l_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wcscoll_l_linked,updateall2,updateall,wcscoll_l_i386,pc_thunk_bx_i386,wcscmp_i386 in NO.
  unfold wcscoll_l_invs,wcscoll_l_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wcscoll_wcscoll_l_disjoint:forall s0 a s t,wcscoll_l_linked s a<>None ->
  wcscoll_invs s0 ((Addr a,s)::t)=None /\ wcscoll_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold wcscoll_l_linked,updateall2,updateall,wcscoll_l_i386,pc_thunk_bx_i386,wcscmp_i386 in CODE.
  unfold wcscoll_invs,wcscoll_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wcscoll_wcscoll_l_call:forall s0 sc,wcscoll_pre s0 ->models x86typctx sc ->
  wcscoll_frame s0 (wcscoll_m6 s0) 32 sc ->sc R_EBX=wcscoll_got ->forall t,
  nextinv wcscoll_linked (wcscoll_invs s0) wcscoll_exit true ((Addr 0x55571,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (wcscoll_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wcscoll_l_linked (wcscoll_l_invs sc)) (xp2:=wcscoll_l_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wcscoll_linked_callee.
    + intros a s h EX NO. exact (proj1 (wcscoll_l_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wcscoll_l_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wcscoll_linked_callee.
    + apply wcscoll_l_nested_code_supported.
    + apply wcscoll_wcscoll_l_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wcscoll_l_exit,at_address in POST.
    destruct (a=?0x55591) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (wcscoll_l_post sc sr) in POST. destruct POST as [FRAME0 OUT].
    pose proof (wcscoll_result_back s0 sc (sr R_EAX) PRE0 FRAME OUT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (wcscoll_l_reference sc) (sr R_EAX)
      (exitof (0x55591+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wcscoll_linked) (ret:=0x55591) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wcscoll_call_return s0 sc _ _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (
      wcscoll_frame s0 (wcscoll_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wcscoll_got /\
      wcscoll_result s0 ((reset_temps sr s2) R_EAX)).
    rewrite R. exact (conj F (conj B ORIGINAL)).
Qed.
Theorem wcscoll_correct_local:forall s0 (PRE0:wcscoll_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55592,s0)),
  satisfies_all wcscoll_linked (wcscoll_invs s0) wcscoll_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x55592,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wcscoll_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wcscoll_frame,unary_frame,wcscoll_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F GS]. unfold wcscoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcscoll_frame,unary_frame,wcscoll_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as (F & BX & GS). unfold wcscoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcscoll_frame,unary_frame,wcscoll_m5,tls_m5,tls_m4,tls_m3,tls_locale,tls_root,wcscoll_got.
      psimpl;elimstore;psimpl.
      rewrite ?GS. rewrite !wcscoll_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wcscoll_linked_welltyped|].
      intro CMDL. apply wcscoll_wcscoll_l_call;[exact PRE0|exact CMDL| |].
      * unfold wcscoll_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wcscoll_m6,tls_entry. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as (F & BX & OUT). unfold wcscoll_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold wcscoll_post,cdecl_leaf_frame,wcscoll_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wcscoll_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact OUT].
Qed.

Theorem wcscoll_correct:forall prog (EXT:wcscoll_linked ⊆2 prog) s0 (PRE0:wcscoll_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55592,s0)),
  satisfies_all prog (wcscoll_invs s0) wcscoll_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcscoll_invs,wcscoll_linked,updateall2,updateall,
      wcscoll_i386,pc_thunk_bx_i386,wcscoll_l_i386,wcscmp_i386,wcscoll_l_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcscoll_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wcscoll_returns:forall prog (EXT:wcscoll_linked ⊆2 prog) s0 (PRE0:wcscoll_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x555bb,s)=(Addr 0x55592,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x555bb,s)::t)) (UT:unterminated wcscoll_exit t),
  exists value,wcscoll_result s0 value /\ cdecl_returned (wcscoll_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcscoll_correct prog EXT s0 PRE0 t (Addr 0x555bb,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcscoll_post s0 s) in INV. destruct INV as [FRAME OUT].
  assert (RETURN:cdecl_returned (wcscoll_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x555bb) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wcscoll_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wcscoll_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
