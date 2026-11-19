(* strncasecmp_l -- musl i386, non-leaf bounded locale comparison wrapper

   SEMANTICS / SPECIFICATION
   Compare up to n original bytes after ASCII lowercase conversion. Zero count
   returns zero without reading input data. Otherwise the execution supplies
   k<n with equal folded nonzero prefixes, stopping at count, NUL, or mismatch;
   return the exact modular folded-byte difference. Every locale word is ignored.
   Source: local Linux man-pages 6.9.1, strcasecmp(3), paraphrased; forwarding and
   exact difference follow this binary.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA0x66260 / global0x76260, RET0x76284, Ghidra image base0x10000.
   Ghidra12.0 PUBLIC frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   P, Q, count, locale are entry ESP+4,+8,+12,+16. Declared register widths;
   each original input byte below count and through its first NUL avoids the
   96-byte nested frame. No input read premise for count0, no caller lengths or
   stopping witness, no extra count or non-wrapping restriction. Compose both
   PIC thunks and all child calls. Exact conditional memory records child save
   words, optional count store, final argument/return pair, and wrapper copies.
   Preserve all callee-saved registers, permissions, outer stack and original RA.
   Partial correctness in every containing program, no termination assertion.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call i386_ternary_call
  strncasecmp_l_support strncasecmp_l_i386 pc_thunk_bx_i386 pc_thunk_ax_i386 strncasecmp_i386 strncasecmp_proof
  strncasecmp_support tolower_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strncasecmp_l_post (s0 s:store):=exists called stop,
  cdecl_leaf_frame (strncasecmp_l_reference s0 called stop) s /\ strncasecmp_outcome s0 called stop (s R_EAX).
Definition strncasecmp_l_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x76260=>Some (s=s0)
  | 0x76261=>Some (strncasecmp_l_frame s0 (strncasecmp_l_m1 s0) 4 s)
  | 0x76266=>Some (strncasecmp_l_frame s0 (strncasecmp_l_m2 s0) 4 s /\ s R_EBX=0x76266)
  | 0x7627b=>Some (strncasecmp_l_frame s0 (strncasecmp_l_m5 s0) 28 s /\ s R_EBX=strncasecmp_l_got)
  | 0x76280=>Some (exists called stop,strncasecmp_l_frame s0 (strncasecmp_l_memory s0 called stop) 28 s /\
      s R_EBX=strncasecmp_l_got /\ strncasecmp_outcome s0 called stop (s R_EAX))
  | 0x76284=>Some (strncasecmp_l_post s0 s)
  | _=>None end | _=>None end.
Definition strncasecmp_l_exit:=at_address 0x76284.
Lemma strncasecmp_nested_code_supported:forall s0,
  code_supported strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strncasecmp_linked,updateall2,updateall,strncasecmp_i386,pc_thunk_ax_i386,tolower_i386 in NO.
  unfold strncasecmp_invs,strncasecmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strncasecmp_l_strncasecmp_disjoint:forall s0 a s t,strncasecmp_linked s a<>None ->
  strncasecmp_l_invs s0 ((Addr a,s)::t)=None /\ strncasecmp_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strncasecmp_linked,updateall2,updateall,strncasecmp_i386,pc_thunk_ax_i386,tolower_i386 in CODE.
  unfold strncasecmp_l_invs,strncasecmp_l_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strncasecmp_l_strncasecmp_call:forall s0 sc,strncasecmp_l_pre s0 ->models x86typctx sc ->
  strncasecmp_l_frame s0 (strncasecmp_l_m6 s0) 32 sc ->sc R_EBX=strncasecmp_l_got ->forall t,
  nextinv strncasecmp_l_linked (strncasecmp_l_invs s0) strncasecmp_l_exit true ((Addr 0x761b4,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (strncasecmp_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strncasecmp_linked (strncasecmp_invs sc)) (xp2:=strncasecmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strncasecmp_l_linked_callee.
    + intros a s h EX NO. exact (proj1 (strncasecmp_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strncasecmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strncasecmp_l_linked_callee.
    + apply strncasecmp_nested_code_supported.
    + apply strncasecmp_l_strncasecmp_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strncasecmp_exit,at_address in POST.
    destruct (a=?0x7625f) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strncasecmp_post sc sr) in POST. destruct POST as [called [stop [FRAME0 OUT]]].
    destruct (strncasecmp_l_outcome s0 sc called stop (sr R_EAX) PRE0 FRAME BX OUT) as [ORIGINAL MM].
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strncasecmp_reference sc called stop) (sr R_EAX)
      (exitof (0x7625f+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strncasecmp_l_linked) (ret:=0x7625f) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strncasecmp_l_call_return s0 sc called stop _ _ _ FRAME BX MM RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (exists called stop,
      strncasecmp_l_frame s0 (strncasecmp_l_memory s0 called stop) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strncasecmp_l_got /\
      strncasecmp_outcome s0 called stop ((reset_temps sr s2) R_EAX)).
    exists called,stop. rewrite R. exact (conj F (conj B ORIGINAL)).
Qed.
Theorem strncasecmp_l_correct_local:forall s0 (PRE0:strncasecmp_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x76260,s0)),
  satisfies_all strncasecmp_l_linked (strncasecmp_l_invs s0) strncasecmp_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x76260,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strncasecmp_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strncasecmp_l_frame,unary_frame,strncasecmp_l_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold strncasecmp_l_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strncasecmp_l_frame,unary_frame,strncasecmp_l_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold strncasecmp_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strncasecmp_l_frame,unary_frame,strncasecmp_l_m5,ternary_m5,ternary_m4,ternary_m3,strncasecmp_l_got.
      psimpl;elimstore;psimpl.
      rewrite !strncasecmp_l_m2_stack by lia.
      unfold cdecl_arg,binary_arg2,ternary_arg3. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strncasecmp_l_linked_welltyped|].
      intro CMDL. apply strncasecmp_l_strncasecmp_call;[exact PRE0|exact CMDL| |].
      * unfold strncasecmp_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strncasecmp_l_m6,ternary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [called [stop (F & BX & OUT)]]. unfold strncasecmp_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold strncasecmp_l_post,cdecl_leaf_frame,strncasecmp_l_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strncasecmp_l_saved_bx s0 called stop BXBOUND).
      exists called,stop. split;[repeat split;first[reflexivity|assumption]|exact OUT].
Qed.

Theorem strncasecmp_l_correct:forall prog (EXT:strncasecmp_l_linked ⊆2 prog) s0 (PRE0:strncasecmp_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x76260,s0)),
  satisfies_all prog (strncasecmp_l_invs s0) strncasecmp_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strncasecmp_l_invs,strncasecmp_l_linked,updateall2,updateall,
      strncasecmp_l_i386,pc_thunk_bx_i386,pc_thunk_ax_i386,strncasecmp_i386,tolower_i386,strncasecmp_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strncasecmp_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strncasecmp_l_returns:forall prog (EXT:strncasecmp_l_linked ⊆2 prog) s0 (PRE0:strncasecmp_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x76284,s)=(Addr 0x76260,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x76284,s)::t)) (UT:unterminated strncasecmp_l_exit t),
  exists value called stop,strncasecmp_result s0 value /\ strncasecmp_outcome s0 called stop value /\
    cdecl_returned (strncasecmp_l_reference s0 called stop) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strncasecmp_l_correct prog EXT s0 PRE0 t (Addr 0x76284,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strncasecmp_l_post s0 s) in INV. destruct INV as [called [stop [FRAME OUT]]].
  assert (RETURN:cdecl_returned (strncasecmp_l_reference s0 called stop) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x76284) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),called,stop. split;[eapply strncasecmp_outcome_result;exact OUT|].
  split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strncasecmp_l_memory s0 called stop) (s0 R_ESP))) in ADDRESS.
  pose proof (strncasecmp_l_outer_stack s0 called stop 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
