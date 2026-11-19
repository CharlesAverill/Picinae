(* wctrans_l -- musl i386, non-leaf locale transformation-name wrapper

   SEMANTICS / SPECIFICATION
   Recognize "toupper" as descriptor1, "tolower" as descriptor2, otherwise0.
   This binary ignores the locale argument and calls wctrans. Source: local
   Linux man-pages6.9.1, /usr/share/man/man3/wctrans.3.gz (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256:8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   wctrans_l and strong __wctrans_l alias: ELF0x3f8dc; image base0x10000.
   Global RET0x4f8f8. Ghidra12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Name and locale: entry ESP+4 and ESP+8; registers have declared widths.
   Every locale representation is accepted. The fixed name strings have their
   ELF byte values. The name and static strings through first NUL avoid the
   72-byte nested frame. No caller length, match or stopping witness.
   Both nested strcmp calls and both PIC calls are composed. Exact conditional
   stack memory is specified by a canonical child entry store. Full callee-saved
   register and permission frame; RET pops the original address and adds four.
   Partial correctness in every containing program. No termination or concrete
   memory-access success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call
  wctrans_l_support wctrans_l_i386 pc_thunk_bx_i386 wctrans_i386 wctrans_proof
  wctrans_support strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wctrans_l_spec:=wctrans_spec.
Definition wctrans_l_post (s0 s:store):=
  cdecl_leaf_post (wctrans_l_reference s0) (wctrans_l_spec s0) s.
Definition wctrans_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4f8dc=>Some (s=s0)
  | 0x4f8dd=>Some (wctrans_l_frame s0 (wctrans_l_m1 s0) 4 s)
  | 0x4f8e2=>Some (wctrans_l_frame s0 (wctrans_l_m2 s0) 4 s /\ s R_EBX=0x4f8e2)
  | 0x4f8ef=>Some (wctrans_l_frame s0 (wctrans_l_m3 s0) 28 s /\ s R_EBX=wctrans_l_got)
  | 0x4f8f4=>Some (wctrans_l_frame s0 (wctrans_l_memory s0) 28 s /\ s R_EBX=wctrans_l_got /\
      s R_EAX=wctrans_l_spec s0)
  | 0x4f8f8=>Some (wctrans_l_post s0 s)
  | _=>None end | _=>None end.
Definition wctrans_l_exit:=at_address 0x4f8f8.

Lemma wctrans_nested_code_supported:forall s0,
  code_supported wctrans_linked (wctrans_invs s0) wctrans_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wctrans_linked,updateall2,updateall,wctrans_i386,pc_thunk_bx_i386,strcmp_i386 in NO.
  unfold wctrans_invs,wctrans_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wctrans_l_wctrans_disjoint:forall s0 a s t,wctrans_linked s a<>None ->
  wctrans_l_invs s0 ((Addr a,s)::t)=None /\ wctrans_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold wctrans_linked,updateall2,updateall,wctrans_i386,pc_thunk_bx_i386,strcmp_i386 in CODE.
  unfold wctrans_l_invs,wctrans_l_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wctrans_l_wctrans_call:forall s0 sc,wctrans_l_pre s0 ->models x86typctx sc ->
  wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->sc R_EBX=wctrans_l_got ->forall t,
  nextinv wctrans_l_linked (wctrans_l_invs s0) wctrans_l_exit true ((Addr 0x4f848,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (wctrans_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wctrans_linked (wctrans_invs sc)) (xp2:=wctrans_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wctrans_l_linked_wctrans.
    + intros a s h EX NO. exact (proj1 (wctrans_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wctrans_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wctrans_l_linked_wctrans.
    + apply wctrans_nested_code_supported.
    + apply wctrans_l_wctrans_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wctrans_exit,at_address in POST.
    destruct (a=?0x4f877) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (wctrans_post sc sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (wctrans_reference sc) (wctrans_spec sc)
      (exitof (0x4f877+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wctrans_l_linked) (ret:=0x4f877) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wctrans_l_call_return s0 sc _ _ PRE0 FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (wctrans_l_frame s0 (wctrans_l_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wctrans_l_got /\ (reset_temps sr s2) R_EAX=wctrans_l_spec s0).
    exact (conj F (conj B R)).
Qed.

Theorem wctrans_l_correct_local:forall s0 (PRE0:wctrans_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f8dc,s0)),
  satisfies_all wctrans_l_linked (wctrans_l_invs s0) wctrans_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x4f8dc,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wctrans_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL.
    destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wctrans_l_frame,unary_frame,wctrans_l_m1,unary_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold wctrans_l_frame,unary_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctrans_l_frame,unary_frame,wctrans_l_m2,unary_m2,wctrans_l_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold wctrans_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctrans_l_frame,unary_frame,wctrans_l_m3,unary_m3,wctrans_l_got. psimpl;elimstore;psimpl.
      rewrite wctrans_l_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wctrans_l_linked_welltyped|].
      intro CMDL. apply wctrans_l_wctrans_call;[exact PRE0|exact CMDL| |].
      * unfold wctrans_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wctrans_l_m4,unary_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [F [BX AX]]. unfold wctrans_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold wctrans_l_post,cdecl_leaf_post,cdecl_leaf_frame,wctrans_l_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wctrans_l_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
Qed.

Theorem wctrans_l_correct:forall prog (EXT:wctrans_l_linked ⊆2 prog) s0 (PRE0:wctrans_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f8dc,s0)),
  satisfies_all prog (wctrans_l_invs s0) wctrans_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wctrans_l_invs,wctrans_l_linked,updateall2,updateall,
      wctrans_l_i386,pc_thunk_bx_i386,wctrans_i386,strcmp_i386,wctrans_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wctrans_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wctrans_l_returns:forall prog (EXT:wctrans_l_linked ⊆2 prog) s0 (PRE0:wctrans_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x4f8f8,s)=(Addr 0x4f8dc,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f8f8,s)::t)) (UT:unterminated wctrans_l_exit t),
  cdecl_returned (wctrans_l_reference s0) (wctrans_l_spec s0) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wctrans_l_correct prog EXT s0 PRE0 t (Addr 0x4f8f8,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wctrans_l_post s0 s) in INV.
  assert (RETURN:cdecl_returned (wctrans_l_reference s0) (wctrans_l_spec s0) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f8f8) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wctrans_l_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wctrans_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
