(* ispunct_l -- musl i386, non-leaf locale classifier wrapper

   SEMANTICS / SPECIFICATION
   Return the existing ispunct predicate for the first argument. The binary
   ignores the locale argument. Predicate source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/ispunct.3.gz (paraphrased); exact forwarding is established
   from this binary's calls. ASCII punctuation is graphical and nonalphanumeric.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Public ispunct_l and strong __ispunct_l alias share ELF VA 0x3f034.
   Ghidra image base 0x10000; global RET 0x4f050. Frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Character and locale words: entry ESP+4 and ESP+8. Architectural registers
   have declared widths. No character or locale bit-pattern restriction.
   EAX is exactly the callee's zero/one result. Six or eight nested stack-word writes within 64 bytes are
   specified by the nested-call memory snapshot. Callee-saved registers,
   permissions and the original return address are restored; RET adds four.
   Scope: partial correctness in all programs containing caller, PIC thunk and
   callee. Neither termination nor concrete access success is asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call
  ispunct_l_support ispunct_l_i386 pc_thunk_bx_i386 ispunct_i386 ispunct_proof
  ispunct_support isalnum_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ispunct_l_spec:=ispunct_spec.
Definition ispunct_l_post (s0 s:store):=
  cdecl_leaf_post (ispunct_l_reference s0) (ispunct_l_spec (cdecl_arg s0)) s.
Definition ispunct_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4f034=>Some (s=s0)
  | 0x4f035=>Some (ispunct_l_frame s0 (ispunct_l_m1 s0) 4 s)
  | 0x4f03a=>Some (ispunct_l_frame s0 (ispunct_l_m2 s0) 4 s /\ s R_EBX=0x4f03a)
  | 0x4f047=>Some (ispunct_l_frame s0 (ispunct_l_m3 s0) 28 s /\ s R_EBX=ispunct_l_got)
  | 0x4f04c=>Some (ispunct_l_frame s0 (ispunct_l_memory s0) 28 s /\ s R_EBX=ispunct_l_got /\
      s R_EAX=ispunct_l_spec (cdecl_arg s0))
  | 0x4f050=>Some (ispunct_l_post s0 s)
  | _=>None end | _=>None end.
Definition ispunct_l_exit:=at_address 0x4f050.

Lemma ispunct_nested_code_supported:forall s0,
  code_supported ispunct_linked (ispunct_invs s0) ispunct_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold ispunct_linked,updateall2,updateall,ispunct_i386,pc_thunk_bx_i386,isalnum_i386 in NO.
  unfold ispunct_invs,ispunct_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma ispunct_l_ispunct_disjoint:forall s0 a s t,ispunct_linked s a<>None ->
  ispunct_l_invs s0 ((Addr a,s)::t)=None /\ ispunct_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold ispunct_linked,updateall2,updateall,ispunct_i386,pc_thunk_bx_i386,isalnum_i386 in CODE.
  unfold ispunct_l_invs,ispunct_l_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma ispunct_l_ispunct_call:forall s0 sc,models x86typctx sc ->
  ispunct_l_frame s0 (ispunct_l_m4 s0) 32 sc ->sc R_EBX=ispunct_l_got ->forall t,
  nextinv ispunct_l_linked (ispunct_l_invs s0) ispunct_l_exit true ((Addr 0x4effc,sc)::t).
Proof.
  intros s0 sc MDL FRAME BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs ispunct_linked (ispunct_invs sc)) (xp2:=ispunct_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply ispunct_l_linked_ispunct.
    + intros a s h EX NO. exact (proj1 (ispunct_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply ispunct_correct_local;[exact MDL|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply ispunct_l_linked_ispunct.
    + apply ispunct_nested_code_supported.
    + apply ispunct_l_ispunct_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,ispunct_exit,at_address in POST.
    destruct (a=?0x4f01d) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (ispunct_post sc sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (ispunct_reference sc) (ispunct_spec (cdecl_arg sc))
      (exitof (0x4f01d+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=ispunct_l_linked) (ret:=0x4f01d) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (ispunct_l_call_return s0 sc _ _ ispunct_spec FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (ispunct_l_frame s0 (ispunct_l_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=ispunct_l_got /\ (reset_temps sr s2) R_EAX=ispunct_l_spec (cdecl_arg s0)).
    exact (conj F (conj B R)).
Qed.

Theorem ispunct_l_correct_local:forall s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f034,s0)),
  satisfies_all ispunct_l_linked (ispunct_l_invs s0) ispunct_l_exit (xs::t).
Proof.
  intros s0 MDL0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x4f034,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact MDL0|apply ispunct_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE MDL0 MDL.
    destruct_inv 32 PRE.
    + clear MDL0 MDL. subst s. repeat x86_step.
      unfold ispunct_l_frame,unary_frame,ispunct_l_m1,unary_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear MDL0 MDL. unfold ispunct_l_frame,unary_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold ispunct_l_frame,unary_frame,ispunct_l_m2,unary_m2,ispunct_l_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0 MDL. destruct PRE as [F BX]. unfold ispunct_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold ispunct_l_frame,unary_frame,ispunct_l_m3,unary_m3,ispunct_l_got. psimpl;elimstore;psimpl.
      rewrite ispunct_l_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply ispunct_l_linked_welltyped|].
      intro CMDL. apply ispunct_l_ispunct_call;[exact CMDL| |].
      * unfold ispunct_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold ispunct_l_m4,unary_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [F [BX AX]]. unfold ispunct_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND. clear MDL0.
      repeat x86_step. unfold ispunct_l_post,cdecl_leaf_post,cdecl_leaf_frame,ispunct_l_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(ispunct_l_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
Qed.

Theorem ispunct_l_correct:forall prog (EXT:ispunct_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f034,s0)),
  satisfies_all prog (ispunct_l_invs s0) ispunct_l_exit (xs::t).
Proof.
  intros prog EXT s0 MDL0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold ispunct_l_invs,ispunct_l_linked,updateall2,updateall,
      ispunct_l_i386,pc_thunk_bx_i386,ispunct_i386,isalnum_i386,ispunct_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply ispunct_l_correct_local;[exact MDL0|]. rewrite START. exact ENTRY.
Qed.

Theorem ispunct_l_returns:forall prog (EXT:ispunct_l_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x4f050,s)=(Addr 0x4f034,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f050,s)::t)) (UT:unterminated ispunct_l_exit t),
  cdecl_returned (ispunct_l_reference s0) (ispunct_l_spec (cdecl_arg s0)) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL0 t s x s' ENTRY XP UT.
  pose proof (ispunct_l_correct prog EXT s0 MDL0 t (Addr 0x4f050,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (ispunct_l_post s0 s) in INV.
  assert (RETURN:cdecl_returned (ispunct_l_reference s0) (ispunct_l_spec (cdecl_arg s0)) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f050) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (ispunct_l_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (ispunct_l_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
