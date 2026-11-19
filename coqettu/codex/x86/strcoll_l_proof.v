(* strcoll_l -- musl i386, non-leaf locale collation wrapper

   SEMANTICS / SPECIFICATION
   Compare the two strings by the existing strcmp contract. This binary ignores
   the locale word and forwards to lexical comparison. The result is the exact
   unsigned-byte difference at the first mismatch or common NUL.
   Background: local Linux man-pages 6.9.1,
   /usr/share/man/man3/strcoll.3.gz (paraphrased).
   The ignored locale and exact result follow from this binary's CALL target.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Public strcoll_l and strong __strcoll_l alias: ELF VA 0x452df.
   Ghidra image base 0x10000; global RET 0x552ff. Frozen strict typed lifter.
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
  strcoll_l_support strcoll_l_i386 pc_thunk_bx_i386 strcmp_i386 strcmp_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcoll_l_post (s0 s:store):=
  cdecl_leaf_frame (strcoll_l_reference s0) s /\ strcoll_l_result s0 (s R_EAX).
Definition strcoll_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x552df=>Some (s=s0)
  | 0x552e0=>Some (strcoll_l_frame s0 (strcoll_l_m1 s0) 4 s)
  | 0x552e5=>Some (strcoll_l_frame s0 (strcoll_l_m2 s0) 4 s /\ s R_EBX=0x552e5)
  | 0x552f6=>Some (strcoll_l_frame s0 (strcoll_l_m4 s0) 28 s /\ s R_EBX=strcoll_l_got)
  | 0x552fb=>Some (strcoll_l_frame s0 (strcoll_l_memory s0) 28 s /\ s R_EBX=strcoll_l_got /\ strcoll_l_result s0 (s R_EAX))
  | 0x552ff=>Some (strcoll_l_post s0 s)
  | _=>None end | _=>None end.
Definition strcoll_l_exit:=at_address 0x552ff.

Lemma strcoll_l_callee_supported:forall s0,code_supported strcmp_i386 (strcmp_invs s0) strcmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strcmp_i386 in NO. unfold strcmp_invs,strcmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strcoll_l_callee_disjoint:forall s0 a s t,strcmp_i386 s a<>None ->
  strcoll_l_invs s0 ((Addr a,s)::t)=None /\ strcoll_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strcmp_i386,strcoll_l_invs,strcoll_l_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strcoll_l_callee_call:forall s0 sc,strcoll_l_pre s0 ->models x86typctx sc ->
  strcoll_l_frame s0 (strcoll_l_m5 s0) 32 sc ->sc R_EBX=strcoll_l_got ->forall t,
  nextinv strcoll_l_linked (strcoll_l_invs s0) strcoll_l_exit true ((Addr 0x3f400,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (strcoll_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strcmp_i386 (strcmp_invs sc)) (xp2:=strcmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strcoll_l_linked_strcmp.
    + intros a s h EX NO. exact (proj1 (strcoll_l_callee_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strcmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strcoll_l_linked_strcmp.
    + apply strcoll_l_callee_supported.
    + apply strcoll_l_callee_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strcmp_exit,at_address in POST.
    destruct (a=?0x3f43e) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strcmp_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (strcoll_l_callee_result s0 sc (sr R_EAX) PRE0 FRAME RESULT) as RESULT0.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_si_bx_reference sc) (sr R_EAX)
      (exitof (0x3f43e+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strcoll_l_linked) (ret:=0x3f43e) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (binary_call_return s0 0x552e5 0x552fb strcoll_l_got sc (sr R_EAX) _ _ FRAME BX RETURN)
      as (PC & RF & B & AX).
    rewrite PC. apply NIHere'. change (strcoll_l_frame s0 (strcoll_l_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strcoll_l_got /\ strcoll_l_result s0 ((reset_temps sr s2) R_EAX)).
    split;[exact RF|]. split;[exact B|]. rewrite AX. exact RESULT0.
Qed.

Theorem strcoll_l_correct_local:forall s0 (PRE0:strcoll_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x552df,s0)),
  satisfies_all strcoll_l_linked (strcoll_l_invs s0) strcoll_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x552df,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strcoll_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strcoll_l_frame,unary_frame,strcoll_l_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold strcoll_l_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcoll_l_frame,unary_frame,strcoll_l_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold strcoll_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcoll_l_frame,unary_frame,strcoll_l_m4,binary_m4,binary_m3,strcoll_l_got.
      psimpl;elimstore;psimpl.
      rewrite !strcoll_l_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strcoll_l_linked_welltyped|].
      intro CMDL. apply strcoll_l_callee_call;[exact PRE0|exact CMDL| |].
      * unfold strcoll_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strcoll_l_m5,binary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [F [BX RESULT]]. unfold strcoll_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold strcoll_l_post,cdecl_leaf_frame,strcoll_l_reference,binary_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strcoll_l_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem strcoll_l_correct:forall prog (EXT:strcoll_l_linked ⊆2 prog) s0 (PRE0:strcoll_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x552df,s0)),
  satisfies_all prog (strcoll_l_invs s0) strcoll_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strcoll_l_invs,strcoll_l_linked,updateall2,updateall,
      strcoll_l_i386,pc_thunk_bx_i386,strcmp_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strcoll_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strcoll_l_returns:forall prog (EXT:strcoll_l_linked ⊆2 prog) s0 (PRE0:strcoll_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x552ff,s)=(Addr 0x552df,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x552ff,s)::t)) (UT:unterminated strcoll_l_exit t),
  exists value,strcoll_l_result s0 value /\ cdecl_returned (strcoll_l_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strcoll_l_correct prog EXT s0 PRE0 t (Addr 0x552ff,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strcoll_l_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (strcoll_l_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x552ff) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strcoll_l_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (strcoll_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
