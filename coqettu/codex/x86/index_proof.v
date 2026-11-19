(* index -- musl i386 non-leaf first-byte search wrapper

   SEMANTICS / SPECIFICATION
   First occurrence of the low argument byte in the original NUL-terminated
   string, including a search for NUL itself; return its pointer or zero if
   absent. Source: local Linux man-pages6.9.1, index(3), paraphrased.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF0x65ed5/global0x75ed5, RET0x75ef5, Ghidra image base0x10000.
   Frozen Ghidra12.0 PUBLIC strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and character at ESP+4/+8, every32-bit character representation.
   Declared register widths; each original character through first NUL has a
   four-byte read disjoint from the112-byte nested frame. No length or stopping
   witness input. Compose strchr, strchrnul, strlen and both actual PIC calls.
   Exact conditional nested memory, original-memory first-match result, all
   callee-saved registers and access permissions. RET pops original address.
   Partial correctness in any containing program; no termination claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call
  index_support index_i386 pc_thunk_bx_i386 strchr_i386 strchr_proof
  strchr_support strchrnul_support strchrnul_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition index_post (s0 s:store):=
  cdecl_leaf_frame (index_reference s0) s /\ strchr_result s0 (s R_EAX).
Definition index_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x75ed5=>Some (s=s0)
  | 0x75ed6=>Some (index_frame s0 (index_m1 s0) 4 s)
  | 0x75edb=>Some (index_frame s0 (index_m2 s0) 4 s /\ s R_EBX=0x75edb)
  | 0x75eec=>Some (index_frame s0 (index_m4 s0) 28 s /\ s R_EBX=index_got)
  | 0x75ef1=>Some (index_frame s0 (index_memory s0) 28 s /\
      s R_EBX=index_got /\ strchr_result s0 (s R_EAX))
  | 0x75ef5=>Some (index_post s0 s)
  | _=>None end | _=>None end.
Definition index_exit:=at_address 0x75ef5.
Lemma strchr_nested_code_supported:forall s0,
  code_supported strchr_linked (strchr_invs s0) strchr_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strchr_linked,updateall2,updateall,strchr_i386,strchrnul_i386,pc_thunk_bx_i386,strlen_i386,strchrnul_linked in NO.
  unfold strchr_invs,strchr_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma index_strchr_disjoint:forall s0 a s t,strchr_linked s a<>None ->
  index_invs s0 ((Addr a,s)::t)=None /\ index_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strchr_linked,updateall2,updateall,strchr_i386,strchrnul_i386,pc_thunk_bx_i386,strlen_i386,strchrnul_linked in CODE.
  unfold index_invs,index_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma index_strchr_call:forall s0 sc,index_pre s0 ->models x86typctx sc ->
  index_frame s0 (index_m5 s0) 32 sc ->sc R_EBX=index_got ->forall t,
  nextinv index_linked (index_invs s0) index_exit true ((Addr 0x7605e,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (index_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strchr_linked (strchr_invs sc)) (xp2:=strchr_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply index_linked_callee.
    + intros a s h EX NO. exact (proj1 (strchr_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strchr_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply index_linked_callee.
    + apply strchr_nested_code_supported.
    + apply index_strchr_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strchr_exit,at_address in POST.
    destruct (a=?0x7607d) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strchr_post sc sr) in POST. destruct POST as [FRAME0 OUT].
    pose proof (index_result_back s0 sc (sr R_EAX) PRE0 FRAME OUT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strchr_reference sc) (sr R_EAX)
      (exitof (0x7607d+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=index_linked) (ret:=0x7607d) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (index_call_return s0 sc _ _ _ PRE0 FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (
      index_frame s0 (index_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=index_got /\
      strchr_result s0 ((reset_temps sr s2) R_EAX)).
    rewrite R. exact (conj F (conj B ORIGINAL)).
Qed.
Theorem index_correct_local:forall s0 (PRE0:index_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75ed5,s0)),
  satisfies_all index_linked (index_invs s0) index_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x75ed5,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply index_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold index_frame,unary_frame,index_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold index_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold index_frame,unary_frame,index_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold index_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold index_frame,unary_frame,index_m4,binary_m4,binary_m3,index_got.
      psimpl;elimstore;psimpl.
      rewrite !index_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply index_linked_welltyped|].
      intro CMDL. apply index_strchr_call;[exact PRE0|exact CMDL| |].
      * unfold index_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold index_m5,binary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as (F & BX & OUT). unfold index_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold index_post,cdecl_leaf_frame,index_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(index_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact OUT].
Qed.

Theorem index_correct:forall prog (EXT:index_linked ⊆2 prog) s0 (PRE0:index_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75ed5,s0)),
  satisfies_all prog (index_invs s0) index_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold index_invs,index_linked,updateall2,updateall,
      index_i386,pc_thunk_bx_i386,strchr_i386,strchrnul_i386,strlen_i386,strchrnul_linked,strchr_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply index_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem index_returns:forall prog (EXT:index_linked ⊆2 prog) s0 (PRE0:index_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x75ef5,s)=(Addr 0x75ed5,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x75ef5,s)::t)) (UT:unterminated index_exit t),
  exists value,strchr_result s0 value /\ cdecl_returned (index_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (index_correct prog EXT s0 PRE0 t (Addr 0x75ef5,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (index_post s0 s) in INV. destruct INV as [FRAME OUT].
  assert (RETURN:cdecl_returned (index_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x75ef5) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (index_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (index_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
