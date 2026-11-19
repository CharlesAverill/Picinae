(* iswblank -- musl i386, PIC wrapper around isblank

   SEMANTICS / SPECIFICATION
   Return one exactly for U+0009 (tab) or U+0020 (space), zero otherwise.
   Source: /usr/share/man/man3/iswblank.3.gz, Linux man-pages 6.9.1
   (paraphrased). This states the concrete musl predicate for all wint_t bits.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x3f17e; Ghidra image base 0x10000; global RET 0x4f19a.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Input: word at entry ESP+4, with architectural registers at their declared
   widths. The result is exactly zero or one. Memory changes by four word
   writes below entry ESP, specified by iswblank_m4. Callee-saved registers,
   the original return address and access permissions are restored; RET adds
   four to entry ESP. No input-value restriction, including WEOF.
   Scope: partial correctness for any program containing caller, thunk and
   isblank. Concrete access success and termination are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls iswblank_support
  iswblank_i386 pc_thunk_bx_i386 isblank_i386 isblank_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition iswblank_spec:=isblank_spec.
Definition iswblank_post (s0 s:store):=
  cdecl_leaf_post (iswblank_reference s0) (iswblank_spec (cdecl_arg s0)) s.
Definition iswblank_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4f17e=>Some (s=s0)
  | 0x4f17f=>Some (iswblank_frame s0 (iswblank_m1 s0) 4 s)
  | 0x4f184=>Some (iswblank_frame s0 (iswblank_m2 s0) 4 s /\ s R_EBX=0x4f184)
  | 0x4f191=>Some (iswblank_frame s0 (iswblank_m3 s0) 28 s /\ s R_EBX=iswblank_got)
  | 0x4f196=>Some (iswblank_frame s0 (iswblank_m4 s0) 28 s /\ s R_EBX=iswblank_got /\
      s R_EAX=iswblank_spec (cdecl_arg s0))
  | 0x4f19a=>Some (iswblank_post s0 s)
  | _=>None end | _=>None end.
Definition iswblank_exit:=at_address 0x4f19a.

Lemma isblank_code_supported:forall s0,code_supported isblank_i386 (isblank_invs s0) isblank_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold isblank_i386,isblank_invs,leaf_invs,isblank_exit,at_address in *.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma iswblank_isblank_disjoint:forall s0 a s t,isblank_i386 s a<>None ->
  iswblank_invs s0 ((Addr a,s)::t)=None /\ iswblank_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold isblank_i386,iswblank_invs,iswblank_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma iswblank_call_return:forall s0 sc x se,
  iswblank_frame s0 (iswblank_m4 s0) 32 sc -> sc R_EBX=iswblank_got ->
  cdecl_returned sc (isblank_spec (cdecl_arg sc)) x se ->
  x=Addr 0x4f196 /\ iswblank_frame s0 (iswblank_m4 s0) 28 se /\
  se R_EBX=iswblank_got /\ se R_EAX=iswblank_spec (cdecl_arg s0).
Proof.
  intros s0 sc x se FRAME BX RETURN.
  pose proof (iswblank_call_arg s0 sc FRAME) as ARG.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned in RETURN. rewrite ARG,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite iswblank_call_address in PC. split;[exact PC|]. split.
  - unfold iswblank_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;first[reflexivity|assumption].
  - exact (conj EBX AX).
Qed.
Lemma iswblank_isblank_call:forall s0 sc,
  iswblank_frame s0 (iswblank_m4 s0) 32 sc ->sc R_EBX=iswblank_got ->forall t,
  nextinv iswblank_linked (iswblank_invs s0) iswblank_exit true ((Addr 0x4eede,sc)::t).
Proof.
  intros s0 sc FRAME BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs isblank_i386 (isblank_invs sc)) (xp2:=isblank_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply iswblank_linked_isblank.
    + intros a s h EX NO. exact (proj1 (isblank_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply isblank_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply iswblank_linked_isblank.
    + apply isblank_code_supported.
    + apply iswblank_isblank_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,isblank_exit,at_address in POST.
    destruct (a=?0x4eef3) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (cdecl_leaf_post sc (isblank_spec (cdecl_arg sc)) sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (isblank_spec (cdecl_arg sc))
      (exitof (0x4eef3+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=iswblank_linked) (ret:=0x4eef3) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (iswblank_call_return s0 sc _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (iswblank_frame s0 (iswblank_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=iswblank_got /\ (reset_temps sr s2) R_EAX=iswblank_spec (cdecl_arg s0)).
    exact (conj F (conj B R)).
Qed.

Theorem iswblank_correct_local:forall s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f17e,s0)),
  satisfies_all iswblank_linked (iswblank_invs s0) iswblank_exit (xs::t).
Proof.
  intros s0 MDL0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL0.
    destruct_inv 32 PRE.
    + clear MDL0. subst s. repeat x86_step.
      unfold iswblank_frame,iswblank_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear MDL0. unfold iswblank_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold iswblank_frame,iswblank_m2,iswblank_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. unfold iswblank_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold iswblank_frame,iswblank_m3,iswblank_got. psimpl;elimstore;psimpl.
      rewrite iswblank_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. ISA_invseek. apply iswblank_isblank_call.
      * unfold iswblank_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold iswblank_m4. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX AX]]. unfold iswblank_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND. clear MDL0.
      repeat x86_step. unfold iswblank_post,cdecl_leaf_post,cdecl_leaf_frame,iswblank_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(iswblank_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
Qed.

Theorem iswblank_correct:forall prog (EXT:iswblank_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f17e,s0)),
  satisfies_all prog (iswblank_invs s0) iswblank_exit (xs::t).
Proof.
  intros prog EXT s0 MDL0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold iswblank_invs,iswblank_linked,updateall2,updateall,
      iswblank_i386,pc_thunk_bx_i386,isblank_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply iswblank_correct_local;[exact MDL0|]. rewrite START. exact ENTRY.
Qed.

Theorem iswblank_returns:forall prog (EXT:iswblank_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x4f19a,s)=(Addr 0x4f17e,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f19a,s)::t)) (UT:unterminated iswblank_exit t),
  cdecl_returned (iswblank_reference s0) (iswblank_spec (cdecl_arg s0)) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL0 t s x s' ENTRY XP UT.
  pose proof (iswblank_correct prog EXT s0 MDL0 t (Addr 0x4f19a,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (iswblank_post s0 s) in INV.
  assert (RETURN:cdecl_returned (iswblank_reference s0) (iswblank_spec (cdecl_arg s0)) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f19a) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (iswblank_m4 s0) (s0 R_ESP))) in ADDRESS.
  pose proof (iswblank_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
