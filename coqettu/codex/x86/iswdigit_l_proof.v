(* iswdigit_l -- musl i386, non-leaf locale classifier wrapper

   SEMANTICS / SPECIFICATION
   Return the existing iswdigit predicate for the first argument. The binary
   ignores the locale argument. Predicate source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/iswdigit.3.gz (paraphrased); exact forwarding is established
   from this binary's calls. The accepted value is an ASCII decimal digit.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Public iswdigit_l and strong __iswdigit_l alias share ELF VA 0x3f366.
   Ghidra image base 0x10000; global RET 0x4f382. Frozen strict typed lifter.
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
  iswdigit_l_support iswdigit_l_i386 pc_thunk_bx_i386 iswdigit_i386 iswdigit_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition iswdigit_l_spec:=iswdigit_spec.
Definition iswdigit_l_post (s0 s:store):=
  cdecl_leaf_post (iswdigit_l_reference s0) (iswdigit_l_spec (cdecl_arg s0)) s.
Definition iswdigit_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4f366=>Some (s=s0)
  | 0x4f367=>Some (iswdigit_l_frame s0 (iswdigit_l_m1 s0) 4 s)
  | 0x4f36c=>Some (iswdigit_l_frame s0 (iswdigit_l_m2 s0) 4 s /\ s R_EBX=0x4f36c)
  | 0x4f379=>Some (iswdigit_l_frame s0 (iswdigit_l_m3 s0) 28 s /\ s R_EBX=iswdigit_l_got)
  | 0x4f37e=>Some (iswdigit_l_frame s0 (iswdigit_l_m4 s0) 28 s /\ s R_EBX=iswdigit_l_got /\
      s R_EAX=iswdigit_l_spec (cdecl_arg s0))
  | 0x4f382=>Some (iswdigit_l_post s0 s)
  | _=>None end | _=>None end.
Definition iswdigit_l_exit:=at_address 0x4f382.

Lemma iswdigit_code_supported:forall s0,code_supported iswdigit_i386 (iswdigit_invs s0) iswdigit_exit.
Proof. intro s0. apply unary_leaf_supported;intros;discriminate. Qed.
Lemma iswdigit_l_iswdigit_disjoint:forall s0 a s t,iswdigit_i386 s a<>None ->
  iswdigit_l_invs s0 ((Addr a,s)::t)=None /\ iswdigit_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold iswdigit_i386,iswdigit_l_invs,iswdigit_l_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma iswdigit_l_call_return:forall s0 sc x se,
  iswdigit_l_frame s0 (iswdigit_l_m4 s0) 32 sc ->sc R_EBX=iswdigit_l_got ->
  cdecl_returned sc (iswdigit_spec (cdecl_arg sc)) x se ->
  x=Addr 0x4f37e /\ iswdigit_l_frame s0 (iswdigit_l_m4 s0) 28 se /\
  se R_EBX=iswdigit_l_got /\ se R_EAX=iswdigit_l_spec (cdecl_arg s0).
Proof. intros. exact (unary_call_return s0 0x4f36c 0x4f37e iswdigit_l_got iswdigit_spec sc x se H H0 H1). Qed.
Lemma iswdigit_l_iswdigit_call:forall s0 sc,
  iswdigit_l_frame s0 (iswdigit_l_m4 s0) 32 sc ->sc R_EBX=iswdigit_l_got ->forall t,
  nextinv iswdigit_l_linked (iswdigit_l_invs s0) iswdigit_l_exit true ((Addr 0x4f355,sc)::t).
Proof.
  intros s0 sc FRAME BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs iswdigit_i386 (iswdigit_invs sc)) (xp2:=iswdigit_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply iswdigit_l_linked_iswdigit.
    + intros a s h EX NO. exact (proj1 (iswdigit_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply iswdigit_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply iswdigit_l_linked_iswdigit.
    + apply iswdigit_code_supported.
    + apply iswdigit_l_iswdigit_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,iswdigit_exit,at_address in POST.
    destruct (a=?0x4f365) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (cdecl_leaf_post sc (iswdigit_spec (cdecl_arg sc)) sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (iswdigit_spec (cdecl_arg sc))
      (exitof (0x4f365+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=iswdigit_l_linked) (ret:=0x4f365) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (iswdigit_l_call_return s0 sc _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (iswdigit_l_frame s0 (iswdigit_l_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=iswdigit_l_got /\ (reset_temps sr s2) R_EAX=iswdigit_l_spec (cdecl_arg s0)).
    exact (conj F (conj B R)).
Qed.

Theorem iswdigit_l_correct_local:forall s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f366,s0)),
  satisfies_all iswdigit_l_linked (iswdigit_l_invs s0) iswdigit_l_exit (xs::t).
Proof.
  intros s0 MDL0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL0.
    destruct_inv 32 PRE.
    + clear MDL0. subst s. repeat x86_step.
      unfold iswdigit_l_frame,unary_frame,iswdigit_l_m1,unary_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear MDL0. unfold iswdigit_l_frame,unary_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold iswdigit_l_frame,unary_frame,iswdigit_l_m2,unary_m2,iswdigit_l_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. unfold iswdigit_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold iswdigit_l_frame,unary_frame,iswdigit_l_m3,unary_m3,iswdigit_l_got. psimpl;elimstore;psimpl.
      rewrite iswdigit_l_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. ISA_invseek. apply iswdigit_l_iswdigit_call.
      * unfold iswdigit_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold iswdigit_l_m4,unary_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX AX]]. unfold iswdigit_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND. clear MDL0.
      repeat x86_step. unfold iswdigit_l_post,cdecl_leaf_post,cdecl_leaf_frame,iswdigit_l_reference,unary_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(iswdigit_l_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
Qed.

Theorem iswdigit_l_correct:forall prog (EXT:iswdigit_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f366,s0)),
  satisfies_all prog (iswdigit_l_invs s0) iswdigit_l_exit (xs::t).
Proof.
  intros prog EXT s0 MDL0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold iswdigit_l_invs,iswdigit_l_linked,updateall2,updateall,
      iswdigit_l_i386,pc_thunk_bx_i386,iswdigit_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply iswdigit_l_correct_local;[exact MDL0|]. rewrite START. exact ENTRY.
Qed.

Theorem iswdigit_l_returns:forall prog (EXT:iswdigit_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x4f382,s)=(Addr 0x4f366,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f382,s)::t)) (UT:unterminated iswdigit_l_exit t),
  cdecl_returned (iswdigit_l_reference s0) (iswdigit_l_spec (cdecl_arg s0)) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL0 t s x s' ENTRY XP UT.
  pose proof (iswdigit_l_correct prog EXT s0 MDL0 t (Addr 0x4f382,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (iswdigit_l_post s0 s) in INV.
  assert (RETURN:cdecl_returned (iswdigit_l_reference s0) (iswdigit_l_spec (cdecl_arg s0)) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f382) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (iswdigit_l_m4 s0) (s0 R_ESP))) in ADDRESS.
  pose proof (iswdigit_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
