(* wcscoll_l -- musl i386, non-leaf locale collation wrapper

   SEMANTICS / SPECIFICATION
   Compare the two strings by the existing wcscmp contract. This binary ignores
   the locale word and forwards to lexical comparison. The result is the exact
   signed wide-character ordering (-1,0,+1) at the first mismatch or common NUL.
   Background: local Linux man-pages 6.9.1,
   /usr/share/man/man3/wcscmp.3.gz (paraphrased).
   The ignored locale and exact result follow from this binary's CALL target.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Public wcscoll_l and strong __wcscoll_l alias: ELF VA 0x45571.
   Ghidra image base 0x10000; global RET 0x55591. Frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Two string pointers and a locale word: entry ESP+4, ESP+8 and ESP+12.
   Architectural registers have declared widths. Each original string through
   its first NUL avoids the 40-byte nested-call stack region. No length or stop
   witness is a caller premise, and no locale bit pattern is excluded.
   The exact memory snapshot includes five caller and two callee stack-word
   writes. All callee-saved registers, permissions and the original return
   address are restored; RET adds four. Partial correctness in all containing
   programs; neither termination nor concrete access success is asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_calls i386_unary_call i386_binary_call
  wcscoll_l_support wcscoll_l_i386 pc_thunk_bx_i386 wcscmp_i386 wcscmp_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcscoll_l_post (s0 s:store):=
  cdecl_leaf_frame (wcscoll_l_reference s0) s /\ wcscoll_l_result s0 (s R_EAX).
Definition wcscoll_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x55571=>Some (s=s0)
  | 0x55572=>Some (wcscoll_l_frame s0 (wcscoll_l_m1 s0) 4 s)
  | 0x55577=>Some (wcscoll_l_frame s0 (wcscoll_l_m2 s0) 4 s /\ s R_EBX=0x55577)
  | 0x55588=>Some (wcscoll_l_frame s0 (wcscoll_l_m4 s0) 28 s /\ s R_EBX=wcscoll_l_got)
  | 0x5558d=>Some (wcscoll_l_frame s0 (wcscoll_l_memory s0) 28 s /\ s R_EBX=wcscoll_l_got /\ wcscoll_l_result s0 (s R_EAX))
  | 0x55591=>Some (wcscoll_l_post s0 s)
  | _=>None end | _=>None end.
Definition wcscoll_l_exit:=at_address 0x55591.

Lemma wcscoll_l_callee_supported:forall s0,code_supported wcscmp_i386 (wcscmp_invs s0) wcscmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wcscmp_i386 in NO. unfold wcscmp_invs,wcscmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wcscoll_l_callee_disjoint:forall s0 a s t,wcscmp_i386 s a<>None ->
  wcscoll_l_invs s0 ((Addr a,s)::t)=None /\ wcscoll_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold wcscmp_i386,wcscoll_l_invs,wcscoll_l_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wcscoll_l_callee_call:forall s0 sc,wcscoll_l_pre s0 ->models x86typctx sc ->
  wcscoll_l_frame s0 (wcscoll_l_m5 s0) 32 sc ->sc R_EBX=wcscoll_l_got ->forall t,
  nextinv wcscoll_l_linked (wcscoll_l_invs s0) wcscoll_l_exit true ((Addr 0x3f860,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (wcscoll_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wcscmp_i386 (wcscmp_invs sc)) (xp2:=wcscmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wcscoll_l_linked_wcscmp.
    + intros a s h EX NO. exact (proj1 (wcscoll_l_callee_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wcscmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wcscoll_l_linked_wcscmp.
    + apply wcscoll_l_callee_supported.
    + apply wcscoll_l_callee_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wcscmp_exit,at_address in POST.
    destruct (a=?0x3f8a2) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (wcscmp_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (wcscoll_l_callee_result s0 sc (sr R_EAX) PRE0 FRAME RESULT) as RESULT0.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_si_bx_reference sc) (sr R_EAX)
      (exitof (0x3f8a2+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wcscoll_l_linked) (ret:=0x3f8a2) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (binary_call_return s0 0x55577 0x5558d wcscoll_l_got sc (sr R_EAX) _ _ FRAME BX RETURN)
      as (PC & RF & B & AX).
    rewrite PC. apply NIHere'. change (wcscoll_l_frame s0 (wcscoll_l_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wcscoll_l_got /\ wcscoll_l_result s0 ((reset_temps sr s2) R_EAX)).
    split;[exact RF|]. split;[exact B|]. rewrite AX. exact RESULT0.
Qed.

Theorem wcscoll_l_correct_local:forall s0 (PRE0:wcscoll_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55571,s0)),
  satisfies_all wcscoll_l_linked (wcscoll_l_invs s0) wcscoll_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x55571,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wcscoll_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wcscoll_l_frame,unary_frame,wcscoll_l_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold wcscoll_l_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcscoll_l_frame,unary_frame,wcscoll_l_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold wcscoll_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcscoll_l_frame,unary_frame,wcscoll_l_m4,binary_m4,binary_m3,wcscoll_l_got.
      psimpl;elimstore;psimpl.
      rewrite !wcscoll_l_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wcscoll_l_linked_welltyped|].
      intro CMDL. apply wcscoll_l_callee_call;[exact PRE0|exact CMDL| |].
      * unfold wcscoll_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wcscoll_l_m5,binary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [F [BX RESULT]]. unfold wcscoll_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold wcscoll_l_post,cdecl_leaf_frame,wcscoll_l_reference,binary_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wcscoll_l_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem wcscoll_l_correct:forall prog (EXT:wcscoll_l_linked ⊆2 prog) s0 (PRE0:wcscoll_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x55571,s0)),
  satisfies_all prog (wcscoll_l_invs s0) wcscoll_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcscoll_l_invs,wcscoll_l_linked,updateall2,updateall,
      wcscoll_l_i386,pc_thunk_bx_i386,wcscmp_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcscoll_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wcscoll_l_returns:forall prog (EXT:wcscoll_l_linked ⊆2 prog) s0 (PRE0:wcscoll_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x55591,s)=(Addr 0x55571,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x55591,s)::t)) (UT:unterminated wcscoll_l_exit t),
  exists value,wcscoll_l_result s0 value /\ cdecl_returned (wcscoll_l_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcscoll_l_correct prog EXT s0 PRE0 t (Addr 0x55591,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcscoll_l_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (wcscoll_l_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x55591) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wcscoll_l_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wcscoll_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
