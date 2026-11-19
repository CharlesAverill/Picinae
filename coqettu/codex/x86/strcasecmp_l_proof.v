(* strcasecmp_l -- musl i386, non-leaf locale comparison wrapper

   SEMANTICS / SPECIFICATION
   Compare original strings after ASCII lowercase conversion. Return the exact
   modular byte difference at the first folded mismatch or either NUL. This
   binary ignores its locale word. Source: local Linux man-pages 6.9.1,
   strcasecmp(3), paraphrased; exact forwarding follows the binary's call.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   strcasecmp_l / strong __strcasecmp_l alias: ELF VA 0x65fba, base 0x10000.
   Global RET 0x75fda. Ghidra 12.0 PUBLIC frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   String pointers and locale: entry ESP+4, ESP+8 and ESP+12; registers have
   declared widths. Every locale word is accepted. Each original string through
   first NUL avoids the 80-byte nested frame. No caller lengths or stop witness.
   Both PIC calls and all four nested tolower call sites compose checked callee
   contracts. Exact memory records twelve effective word writes, with the final
   original Q-byte argument and terminal return address overwriting prior calls.
   Full callee-saved register and permission frame; RET pops the original address
   and adds four. Partial correctness in every containing program; no termination
   or successful concrete access claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call
  strcasecmp_l_support strcasecmp_l_i386 pc_thunk_bx_i386 strcasecmp_i386 strcasecmp_proof
  strcasecmp_support tolower_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcasecmp_l_post (s0 s:store):=exists k,strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\
  cdecl_leaf_frame (strcasecmp_l_reference s0 k) s /\ s R_EAX=strcasecmp_diff s0 k.
Definition strcasecmp_l_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x75fba=>Some (s=s0)
  | 0x75fbb=>Some (strcasecmp_l_frame s0 (strcasecmp_l_m1 s0) 4 s)
  | 0x75fc0=>Some (strcasecmp_l_frame s0 (strcasecmp_l_m2 s0) 4 s /\ s R_EBX=0x75fc0)
  | 0x75fd1=>Some (strcasecmp_l_frame s0 (strcasecmp_l_m4 s0) 28 s /\ s R_EBX=strcasecmp_l_got)
  | 0x75fd6=>Some (exists k,strcasecmp_l_frame s0 (strcasecmp_l_memory s0 k) 28 s /\
      s R_EBX=strcasecmp_l_got /\ strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\ s R_EAX=strcasecmp_diff s0 k)
  | 0x75fda=>Some (strcasecmp_l_post s0 s)
  | _=>None end | _=>None end.
Definition strcasecmp_l_exit:=at_address 0x75fda.
Lemma strcasecmp_nested_code_supported:forall s0,
  code_supported strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strcasecmp_linked,updateall2,updateall,strcasecmp_i386,pc_thunk_bx_i386,tolower_i386 in NO.
  unfold strcasecmp_invs,strcasecmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strcasecmp_l_strcasecmp_disjoint:forall s0 a s t,strcasecmp_linked s a<>None ->
  strcasecmp_l_invs s0 ((Addr a,s)::t)=None /\ strcasecmp_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strcasecmp_linked,updateall2,updateall,strcasecmp_i386,pc_thunk_bx_i386,tolower_i386 in CODE.
  unfold strcasecmp_l_invs,strcasecmp_l_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strcasecmp_l_strcasecmp_call:forall s0 sc,strcasecmp_l_pre s0 ->models x86typctx sc ->
  strcasecmp_l_frame s0 (strcasecmp_l_m5 s0) 32 sc ->sc R_EBX=strcasecmp_l_got ->forall t,
  nextinv strcasecmp_l_linked (strcasecmp_l_invs s0) strcasecmp_l_exit true ((Addr 0x75f40,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (strcasecmp_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strcasecmp_linked (strcasecmp_invs sc)) (xp2:=strcasecmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strcasecmp_l_linked_strcasecmp.
    + intros a s h EX NO. exact (proj1 (strcasecmp_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strcasecmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strcasecmp_l_linked_strcasecmp.
    + apply strcasecmp_nested_code_supported.
    + apply strcasecmp_l_strcasecmp_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strcasecmp_exit,at_address in POST.
    destruct (a=?0x75fb9) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strcasecmp_post sc sr) in POST. destruct POST as [k (PREFIX & STOP & FRAME0 & VALUE)].
    destruct (strcasecmp_l_transport s0 sc k PRE0 FRAME PREFIX) as (ORIGINAL & P & Q).
    unfold strcasecmp_stop in STOP. rewrite P,Q in STOP.
    unfold strcasecmp_diff in VALUE. rewrite P,Q in VALUE. fold (strcasecmp_diff s0 k) in VALUE.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strcasecmp_reference sc k) (sr R_EAX)
      (exitof (0x75fb9+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strcasecmp_l_linked) (ret:=0x75fb9) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strcasecmp_l_call_return s0 sc k _ _ _ FRAME BX Q RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (exists k,
      strcasecmp_l_frame s0 (strcasecmp_l_memory s0 k) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strcasecmp_l_got /\ strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\
      (reset_temps sr s2) R_EAX=strcasecmp_diff s0 k).
    exists k. rewrite R. exact (conj F (conj B (conj ORIGINAL (conj STOP VALUE)))).
Qed.
Theorem strcasecmp_l_correct_local:forall s0 (PRE0:strcasecmp_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75fba,s0)),
  satisfies_all strcasecmp_l_linked (strcasecmp_l_invs s0) strcasecmp_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x75fba,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strcasecmp_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strcasecmp_l_frame,unary_frame,strcasecmp_l_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold strcasecmp_l_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcasecmp_l_frame,unary_frame,strcasecmp_l_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold strcasecmp_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strcasecmp_l_frame,unary_frame,strcasecmp_l_m4,binary_m4,binary_m3,strcasecmp_l_got.
      psimpl;elimstore;psimpl.
      rewrite !strcasecmp_l_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strcasecmp_l_linked_welltyped|].
      intro CMDL. apply strcasecmp_l_strcasecmp_call;[exact PRE0|exact CMDL| |].
      * unfold strcasecmp_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strcasecmp_l_m5,binary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [k (F & BX & PREFIX & STOP & VALUE)]. unfold strcasecmp_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold strcasecmp_l_post,cdecl_leaf_frame,strcasecmp_l_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strcasecmp_l_saved_bx s0 k BXBOUND).
      exists k. split;[exact PREFIX|]. split;[exact STOP|]. split;[repeat split;first[reflexivity|assumption]|exact VALUE].
Qed.

Theorem strcasecmp_l_correct:forall prog (EXT:strcasecmp_l_linked ⊆2 prog) s0 (PRE0:strcasecmp_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75fba,s0)),
  satisfies_all prog (strcasecmp_l_invs s0) strcasecmp_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strcasecmp_l_invs,strcasecmp_l_linked,updateall2,updateall,
      strcasecmp_l_i386,pc_thunk_bx_i386,strcasecmp_i386,tolower_i386,strcasecmp_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strcasecmp_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strcasecmp_l_returns:forall prog (EXT:strcasecmp_l_linked ⊆2 prog) s0 (PRE0:strcasecmp_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x75fda,s)=(Addr 0x75fba,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x75fda,s)::t)) (UT:unterminated strcasecmp_l_exit t),
  exists value k,strcasecmp_result s0 value /\ strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\
    cdecl_returned (strcasecmp_l_reference s0 k) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strcasecmp_l_correct prog EXT s0 PRE0 t (Addr 0x75fda,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strcasecmp_l_post s0 s) in INV. destruct INV as [k (PREFIX & STOP & FRAME & VALUE)].
  assert (RETURN:cdecl_returned (strcasecmp_l_reference s0 k) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x75fda) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),k. split;[rewrite VALUE;apply strcasecmp_result_at_stop;assumption|].
  split;[exact PREFIX|]. split;[exact STOP|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strcasecmp_l_memory s0 k) (s0 R_ESP))) in ADDRESS.
  pose proof (strcasecmp_l_outer_stack s0 k 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
