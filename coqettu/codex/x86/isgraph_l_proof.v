(* isgraph_l -- musl i386, non-leaf locale classifier wrapper

   SEMANTICS / SPECIFICATION
   Return the existing isgraph predicate for the first argument. The binary
   ignores the locale argument. Predicate source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/isgraph.3.gz (paraphrased); exact forwarding is established
   from this binary's calls. The accepted value is an ASCII graphical character.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Public isgraph_l and strong __isgraph_l alias share ELF VA 0x3ef83.
   Ghidra image base 0x10000; global RET 0x4ef9f. Frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Character and locale words: entry ESP+4 and ESP+8. Architectural registers
   have declared widths. No character or locale bit-pattern restriction.
   EAX is exactly the callee's zero/one result. Four stack-word writes are
   specified by the shared unary-call memory snapshot. Callee-saved registers,
   permissions and the original return address are restored; RET adds four.
   Scope: partial correctness in all programs containing caller, PIC thunk and
   callee. Neither termination nor concrete access success is asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call
  isgraph_l_support isgraph_l_i386 pc_thunk_bx_i386 isgraph_i386 isgraph_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition isgraph_l_spec:=isgraph_spec.
Definition isgraph_l_post (s0 s:store):=
  cdecl_leaf_post (isgraph_l_reference s0) (isgraph_l_spec (cdecl_arg s0)) s.
Definition isgraph_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4ef83=>Some (s=s0)
  | 0x4ef84=>Some (isgraph_l_frame s0 (isgraph_l_m1 s0) 4 s)
  | 0x4ef89=>Some (isgraph_l_frame s0 (isgraph_l_m2 s0) 4 s /\ s R_EBX=0x4ef89)
  | 0x4ef96=>Some (isgraph_l_frame s0 (isgraph_l_m3 s0) 28 s /\ s R_EBX=isgraph_l_got)
  | 0x4ef9b=>Some (isgraph_l_frame s0 (isgraph_l_m4 s0) 28 s /\ s R_EBX=isgraph_l_got /\
      s R_EAX=isgraph_l_spec (cdecl_arg s0))
  | 0x4ef9f=>Some (isgraph_l_post s0 s)
  | _=>None end | _=>None end.
Definition isgraph_l_exit:=at_address 0x4ef9f.

Lemma isgraph_code_supported:forall s0,code_supported isgraph_i386 (isgraph_invs s0) isgraph_exit.
Proof. intro s0. apply unary_leaf_supported;intros;discriminate. Qed.
Lemma isgraph_l_isgraph_disjoint:forall s0 a s t,isgraph_i386 s a<>None ->
  isgraph_l_invs s0 ((Addr a,s)::t)=None /\ isgraph_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold isgraph_i386,isgraph_l_invs,isgraph_l_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma isgraph_l_call_return:forall s0 sc x se,
  isgraph_l_frame s0 (isgraph_l_m4 s0) 32 sc ->sc R_EBX=isgraph_l_got ->
  cdecl_returned sc (isgraph_spec (cdecl_arg sc)) x se ->
  x=Addr 0x4ef9b /\ isgraph_l_frame s0 (isgraph_l_m4 s0) 28 se /\
  se R_EBX=isgraph_l_got /\ se R_EAX=isgraph_l_spec (cdecl_arg s0).
Proof. intros. exact (unary_call_return s0 0x4ef89 0x4ef9b isgraph_l_got isgraph_spec sc x se H H0 H1). Qed.
Lemma isgraph_l_isgraph_call:forall s0 sc,
  isgraph_l_frame s0 (isgraph_l_m4 s0) 32 sc ->sc R_EBX=isgraph_l_got ->forall t,
  nextinv isgraph_l_linked (isgraph_l_invs s0) isgraph_l_exit true ((Addr 0x4ef72,sc)::t).
Proof.
  intros s0 sc FRAME BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs isgraph_i386 (isgraph_invs sc)) (xp2:=isgraph_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply isgraph_l_linked_isgraph.
    + intros a s h EX NO. exact (proj1 (isgraph_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply isgraph_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply isgraph_l_linked_isgraph.
    + apply isgraph_code_supported.
    + apply isgraph_l_isgraph_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,isgraph_exit,at_address in POST.
    destruct (a=?0x4ef82) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (cdecl_leaf_post sc (isgraph_spec (cdecl_arg sc)) sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (isgraph_spec (cdecl_arg sc))
      (exitof (0x4ef82+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=isgraph_l_linked) (ret:=0x4ef82) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (isgraph_l_call_return s0 sc _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (isgraph_l_frame s0 (isgraph_l_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=isgraph_l_got /\ (reset_temps sr s2) R_EAX=isgraph_l_spec (cdecl_arg s0)).
    exact (conj F (conj B R)).
Qed.

Theorem isgraph_l_correct_local:forall s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4ef83,s0)),
  satisfies_all isgraph_l_linked (isgraph_l_invs s0) isgraph_l_exit (xs::t).
Proof.
  intros s0 MDL0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL0.
    destruct_inv 32 PRE.
    + clear MDL0. subst s. repeat x86_step.
      unfold isgraph_l_frame,unary_frame,isgraph_l_m1,unary_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear MDL0. unfold isgraph_l_frame,unary_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold isgraph_l_frame,unary_frame,isgraph_l_m2,unary_m2,isgraph_l_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. unfold isgraph_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold isgraph_l_frame,unary_frame,isgraph_l_m3,unary_m3,isgraph_l_got. psimpl;elimstore;psimpl.
      rewrite isgraph_l_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. ISA_invseek. apply isgraph_l_isgraph_call.
      * unfold isgraph_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold isgraph_l_m4,unary_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX AX]]. unfold isgraph_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND. clear MDL0.
      repeat x86_step. unfold isgraph_l_post,cdecl_leaf_post,cdecl_leaf_frame,isgraph_l_reference,unary_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(isgraph_l_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
Qed.

Theorem isgraph_l_correct:forall prog (EXT:isgraph_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4ef83,s0)),
  satisfies_all prog (isgraph_l_invs s0) isgraph_l_exit (xs::t).
Proof.
  intros prog EXT s0 MDL0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold isgraph_l_invs,isgraph_l_linked,updateall2,updateall,
      isgraph_l_i386,pc_thunk_bx_i386,isgraph_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply isgraph_l_correct_local;[exact MDL0|]. rewrite START. exact ENTRY.
Qed.

Theorem isgraph_l_returns:forall prog (EXT:isgraph_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x4ef9f,s)=(Addr 0x4ef83,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4ef9f,s)::t)) (UT:unterminated isgraph_l_exit t),
  cdecl_returned (isgraph_l_reference s0) (isgraph_l_spec (cdecl_arg s0)) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL0 t s x s' ENTRY XP UT.
  pose proof (isgraph_l_correct prog EXT s0 MDL0 t (Addr 0x4ef9f,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (isgraph_l_post s0 s) in INV.
  assert (RETURN:cdecl_returned (isgraph_l_reference s0) (isgraph_l_spec (cdecl_arg s0)) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4ef9f) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (isgraph_l_m4 s0) (s0 R_ESP))) in ADDRESS.
  pose proof (isgraph_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
