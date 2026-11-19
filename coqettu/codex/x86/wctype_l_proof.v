(* wctype_l -- musl i386, non-leaf locale classification-name wrapper

   SEMANTICS / SPECIFICATION
   Return the wctype descriptor for the original name. This binary ignores
   the locale word. Recognized names and descriptor numbers follow the checked
   wctype table and its first-match result. Source: local Linux man-pages
   6.9.1, /usr/share/man/man3/wctype.3.gz (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   wctype_l and strong __wctype_l alias: ELF VA 0x3f338; image base 0x10000.
   Global RET 0x4f354. Frozen Ghidra 12.0 PUBLIC strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Name and locale: entry ESP+4 and ESP+8. Registers have declared widths;
   every locale word is accepted. The name through first NUL and the fixed
   73-byte ELF table avoid the 88-byte nested frame. Table bytes have their
   ELF values. No caller length, first-NUL or match witness.
   Both PIC calls and every nested strcmp call are composed. Exact stack
   memory uses a canonical child entry and execution-derived comparison history.
   All callee-saved registers and permissions are restored; RET pops the
   original return address and adds four. Partial correctness in every
   containing program; no termination or concrete access-success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call
  wctype_l_support wctype_l_i386 pc_thunk_bx_i386 wctype_i386 wctype_proof
  wctype_support strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wctype_l_post (s0 s:store):=exists calls,
  cdecl_leaf_frame (wctype_l_reference s0 calls) s /\ wctype_result s0 (s R_EAX).
Definition wctype_l_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4f338=>Some (s=s0)
  | 0x4f339=>Some (wctype_l_frame s0 (wctype_l_m1 s0) 4 s)
  | 0x4f33e=>Some (wctype_l_frame s0 (wctype_l_m2 s0) 4 s /\ s R_EBX=0x4f33e)
  | 0x4f34b=>Some (wctype_l_frame s0 (wctype_l_m3 s0) 28 s /\ s R_EBX=wctype_l_got)
  | 0x4f350=>Some (exists calls,wctype_l_frame s0 (wctype_l_memory s0 calls) 28 s /\ s R_EBX=wctype_l_got /\
      wctype_result s0 (s R_EAX))
  | 0x4f354=>Some (wctype_l_post s0 s)
  | _=>None end | _=>None end.
Definition wctype_l_exit:=at_address 0x4f354.

Lemma wctype_nested_code_supported:forall s0,
  code_supported wctype_linked (wctype_invs s0) wctype_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wctype_linked,updateall2,updateall,wctype_i386,pc_thunk_bx_i386,strcmp_i386 in NO.
  unfold wctype_invs,wctype_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wctype_l_wctype_disjoint:forall s0 a s t,wctype_linked s a<>None ->
  wctype_l_invs s0 ((Addr a,s)::t)=None /\ wctype_l_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold wctype_linked,updateall2,updateall,wctype_i386,pc_thunk_bx_i386,strcmp_i386 in CODE.
  unfold wctype_l_invs,wctype_l_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wctype_l_wctype_call:forall s0 sc,wctype_l_pre s0 ->models x86typctx sc ->
  wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->sc R_EBX=wctype_l_got ->forall t,
  nextinv wctype_l_linked (wctype_l_invs s0) wctype_l_exit true ((Addr 0x35160,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (wctype_l_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wctype_linked (wctype_invs sc)) (xp2:=wctype_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wctype_l_linked_wctype.
    + intros a s h EX NO. exact (proj1 (wctype_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wctype_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wctype_l_linked_wctype.
    + apply wctype_nested_code_supported.
    + apply wctype_l_wctype_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wctype_exit,at_address in POST.
    destruct (a=?0x351d0) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (wctype_post sc sr) in POST. destruct POST as [calls [FRAME0 RESULT0]].
    pose proof (wctype_l_result_back s0 sc _ PRE0 FRAME RESULT0) as RESULT.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (wctype_reference sc calls) (sr R_EAX)
      (exitof (0x351d0+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wctype_l_linked) (ret:=0x351d0) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wctype_l_call_return s0 sc calls _ _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (exists calls,
      wctype_l_frame s0 (wctype_l_memory s0 calls) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wctype_l_got /\ wctype_result s0 ((reset_temps sr s2) R_EAX)).
    exists calls. rewrite R. exact (conj F (conj B RESULT)).
Qed.

Theorem wctype_l_correct_local:forall s0 (PRE0:wctype_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f338,s0)),
  satisfies_all wctype_l_linked (wctype_l_invs s0) wctype_l_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x4f338,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wctype_l_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL.
    destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wctype_l_frame,unary_frame,wctype_l_m1,unary_m1,save_ebx_memory. psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold wctype_l_frame,unary_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctype_l_frame,unary_frame,wctype_l_m2,unary_m2,wctype_l_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold wctype_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctype_l_frame,unary_frame,wctype_l_m3,unary_m3,wctype_l_got. psimpl;elimstore;psimpl.
      rewrite wctype_l_m2_stack by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wctype_l_linked_welltyped|].
      intro CMDL. apply wctype_l_wctype_call;[exact PRE0|exact CMDL| |].
      * unfold wctype_l_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wctype_l_m4,unary_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [calls [F [BX RESULT]]]. unfold wctype_l_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold wctype_l_post,cdecl_leaf_frame,wctype_l_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wctype_l_saved_bx s0 calls BXBOUND).
      exists calls. split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem wctype_l_correct:forall prog (EXT:wctype_l_linked ⊆2 prog) s0 (PRE0:wctype_l_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f338,s0)),
  satisfies_all prog (wctype_l_invs s0) wctype_l_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wctype_l_invs,wctype_l_linked,updateall2,updateall,
      wctype_l_i386,pc_thunk_bx_i386,wctype_i386,strcmp_i386,wctype_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wctype_l_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wctype_l_returns:forall prog (EXT:wctype_l_linked ⊆2 prog) s0 (PRE0:wctype_l_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x4f354,s)=(Addr 0x4f338,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f354,s)::t)) (UT:unterminated wctype_l_exit t),
  exists value calls,wctype_result s0 value /\ cdecl_returned (wctype_l_reference s0 calls) value x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wctype_l_correct prog EXT s0 PRE0 t (Addr 0x4f354,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wctype_l_post s0 s) in INV. destruct INV as [calls [FRAME RESULT]].
  assert (RETURN:cdecl_returned (wctype_l_reference s0 calls) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f354) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),calls. split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wctype_l_memory s0 calls) (s0 R_ESP))) in ADDRESS.
  pose proof (wctype_l_outer_stack s0 calls 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
