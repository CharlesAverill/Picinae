(* wctrans -- musl i386, non-leaf transformation-name lookup

   SEMANTICS / SPECIFICATION
   Recognize exactly "toupper" (descriptor 1) and "tolower" (descriptor 2),
   returning zero for every other NUL-terminated name. Source: local Linux
   man-pages 6.9.1, /usr/share/man/man3/wctrans.3.gz (paraphrased); numeric
   descriptors and exact case-sensitive comparisons follow from this binary.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x3f848, image base 0x10000, global RET 0x4f877.
   Actual static strings: ELF 0xa3060 and 0xa3068, global 0xb3060/0xb3068.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Name pointer: entry ESP+4. Registers have declared widths. The fixed static
   strings have their ELF byte values; name and constants through first NUL
   avoid the 40-byte nested frame. No input length or stop/match witness is
   assumed. Actual PIC and strcmp calls are composed. Exact memory includes
   the conditional second call's overwrites, all callee-saved registers and
   permissions are restored, and RET pops the original return address.
   Partial correctness in every containing program. No termination or concrete
   memory-access success is claimed.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_calls i386_unary_call
  i386_binary_call wctrans_support wctrans_i386 pc_thunk_bx_i386 strcmp_i386 strcmp_proof.
From Stdlib Require Import NArith Lia Bool.
Import X86Notations.
Open Scope N.
Definition wctrans_post (s0 s:store):=
  cdecl_leaf_post (wctrans_reference s0) (wctrans_spec s0) s.
Definition wctrans_aftercall (s0:store) (second:bool) (s:store):=
  wctrans_frame s0 (wctrans_after s0 second) 28 s /\ s R_EBX=wctrans_got /\
  (s R_EAX=0 <->wctrans_matchb s0 second=true) /\
  (second=true ->wctrans_matchb s0 false=false).
Definition wctrans_prepop (s0 s:store):=
  wctrans_frame s0 (wctrans_memory s0) 12 s /\ s R_EAX=wctrans_spec s0.
Definition wctrans_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x4f848=>Some (s=s0)
  | 0x4f849=>Some (wctrans_frame s0 (wctrans_m1 s0) 4 s)
  | 0x4f84e=>Some (wctrans_frame s0 (wctrans_m2 s0) 4 s /\ s R_EBX=0x4f84e)
  | 0x4f862=>Some (wctrans_frame s0 (wctrans_args s0 false) 28 s /\ s R_EBX=wctrans_got)
  | 0x4f867=>Some (wctrans_aftercall s0 false s)
  | 0x4f873=>Some (wctrans_prepop s0 s)
  | 0x4f878=>Some (wctrans_frame s0 (wctrans_after s0 false) 12 s /\
      s R_EBX=wctrans_got /\ wctrans_matchb s0 false=false)
  | 0x4f886=>Some (wctrans_frame s0 (wctrans_args s0 true) 28 s /\
      s R_EBX=wctrans_got /\ wctrans_matchb s0 false=false)
  | 0x4f88b=>Some (wctrans_aftercall s0 true s)
  | 0x4f877=>Some (wctrans_post s0 s)
  | _=>None end | _=>None end.
Definition wctrans_exit:=at_address 0x4f877.
Lemma wctrans_callee_supported:forall s0,code_supported strcmp_i386 (strcmp_invs s0) strcmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strcmp_i386 in NO. unfold strcmp_invs,strcmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wctrans_callee_disjoint:forall s0 a s t,strcmp_i386 s a<>None ->
  wctrans_invs s0 ((Addr a,s)::t)=None /\ wctrans_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strcmp_i386,wctrans_invs,wctrans_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wctrans_callee_call:forall s0 second sc,wctrans_pre s0 ->models x86typctx sc ->
  wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->sc R_EBX=wctrans_got ->
  (second=true ->wctrans_matchb s0 false=false) ->forall t,
  nextinv wctrans_linked (wctrans_invs s0) wctrans_exit true ((Addr 0x3f400,sc)::t).
Proof.
  intros s0 second sc PRE0 MDL FRAME BX SECOND t.
  pose proof (wctrans_callee_pre s0 second sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strcmp_i386 (strcmp_invs sc)) (xp2:=strcmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wctrans_linked_strcmp.
    + intros a s h EX NO. exact (proj1 (wctrans_callee_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strcmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wctrans_linked_strcmp.
    + apply wctrans_callee_supported.
    + apply wctrans_callee_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strcmp_exit,at_address in POST.
    destruct (a=?0x3f43e) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strcmp_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (wctrans_callee_result s0 second sc (sr R_EAX) PRE0 FRAME RESULT) as RESULT0.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_si_bx_reference sc) (sr R_EAX)
      (exitof (0x3f43e+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wctrans_linked) (ret:=0x3f43e) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wctrans_call_return s0 second sc _ _ _ FRAME BX RETURN) as (PC & RF & B & AX).
    rewrite PC. destruct second.
    + apply NIHere'. change (wctrans_aftercall s0 true (reset_temps sr s2)).
      unfold wctrans_aftercall;rewrite AX;exact (conj RF (conj B (conj RESULT0 SECOND))).
    + apply NIHere'. change (wctrans_aftercall s0 false (reset_temps sr s2)).
      unfold wctrans_aftercall;rewrite AX;exact (conj RF (conj B (conj RESULT0 SECOND))).
Qed.
Theorem wctrans_correct_local:forall s0 (PRE0:wctrans_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f848,s0)),
  satisfies_all wctrans_linked (wctrans_invs s0) wctrans_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x4f848,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wctrans_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wctrans_frame,unary_frame,wctrans_m1,unary_m1,save_ebx_memory. psimpl. repeat split;reflexivity.
    + clear PRE0 MDL. unfold wctrans_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR). repeat x86_step.
      unfold wctrans_frame,unary_frame,wctrans_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold wctrans_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR). repeat x86_step.
      unfold wctrans_frame,unary_frame,wctrans_args,wctrans_args_on,wctrans_before,wctrans_got,wctrans_target.
      psimpl;elimstore;psimpl. unfold wctrans_m2. rewrite unary_m2_stack by lia. unfold cdecl_arg.
      repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wctrans_linked_welltyped|].
      intro CMDL. apply (wctrans_callee_call s0 false);[exact PRE0|exact CMDL| | |discriminate].
      * unfold wctrans_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wctrans_entry,wctrans_entry_on,wctrans_ra. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear PRE0 MDL. destruct PRE as (F & BX & RESULT & SECOND).
      unfold wctrans_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold wctrans_prepop,wctrans_frame,unary_frame;psimpl;elimstore;psimpl.
      all: csimpl.
      * assert (MATCH:wctrans_matchb s0 false=true) by (apply RESULT;assumption).
        unfold wctrans_memory,wctrans_spec. rewrite MATCH. split;[repeat split;first[reflexivity|assumption]|reflexivity].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[exact BX|].
        destruct (wctrans_matchb s0 false) eqn:M;[|reflexivity]. pose proof (proj2 RESULT eq_refl). contradiction.
    + clear MDL. destruct PRE as [F VALUE].
      unfold wctrans_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      assert (SAVED:getmem 32 LittleE 4 (wctrans_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX).
      { unfold wctrans_memory. destruct (wctrans_matchb s0 false);apply wctrans_saved_bx;exact BXBOUND. }
      repeat x86_step. unfold wctrans_post,cdecl_leaf_post,cdecl_leaf_frame,wctrans_reference.
      psimpl;elimstore;psimpl. rewrite (N.mod_small _ _ SPBOUND),SAVED. repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as (F & BX & NOMATCH).
      unfold wctrans_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctrans_frame,unary_frame,wctrans_args,wctrans_args_on,wctrans_before,wctrans_got,wctrans_target.
      psimpl;elimstore;psimpl. rewrite (wctrans_outer_stack s0 false 4 ltac:(lia)). unfold cdecl_arg.
      split;[repeat split;first[reflexivity|assumption]|]. split;first[reflexivity|assumption].
    + destruct PRE as (F & BX & NOMATCH). ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wctrans_linked_welltyped|].
      intro CMDL. apply (wctrans_callee_call s0 true);[exact PRE0|exact CMDL| | |intro;exact NOMATCH].
      * unfold wctrans_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wctrans_entry,wctrans_entry_on,wctrans_ra. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear PRE0 MDL. destruct PRE as (F & BX & RESULT & SECOND).
      pose proof (SECOND eq_refl) as NOMATCH.
      unfold wctrans_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wctrans_prepop,wctrans_frame,unary_frame,wctrans_memory,wctrans_spec.
      psimpl;elimstore;psimpl. rewrite NOMATCH.
      split;[repeat split;first[reflexivity|assumption]|].
      destruct (wctrans_matchb s0 true) eqn:M.
      * pose proof (proj2 RESULT eq_refl) as ZERO. rewrite ZERO. reflexivity.
      * assert (NZ:s R_EAX<>0) by (intro Z;apply RESULT in Z;congruence).
        rewrite (proj2 (N.eqb_neq _ _) NZ). reflexivity.
Qed.
Theorem wctrans_correct:forall prog (EXT:wctrans_linked ⊆2 prog) s0 (PRE0:wctrans_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x4f848,s0)),
  satisfies_all prog (wctrans_invs s0) wctrans_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wctrans_invs,wctrans_linked,updateall2,updateall,
      wctrans_i386,pc_thunk_bx_i386,strcmp_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wctrans_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wctrans_returns:forall prog (EXT:wctrans_linked ⊆2 prog) s0 (PRE0:wctrans_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x4f877,s)=(Addr 0x4f848,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f877,s)::t)) (UT:unterminated wctrans_exit t),
  cdecl_returned (wctrans_reference s0) (wctrans_spec s0) x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wctrans_correct prog EXT s0 PRE0 t (Addr 0x4f877,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wctrans_post s0 s) in INV.
  assert (RETURN:cdecl_returned (wctrans_reference s0) (wctrans_spec s0) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f877) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wctrans_memory s0) (s0 R_ESP))) in ADDRESS.
  unfold wctrans_memory in ADDRESS. destruct (wctrans_matchb s0 false).
  - pose proof (wctrans_outer_stack s0 false 0 ltac:(lia)) as STACK.
    rewrite N.add_0_l in STACK;rewrite STACK in ADDRESS;exact ADDRESS.
  - pose proof (wctrans_outer_stack s0 true 0 ltac:(lia)) as STACK.
    rewrite N.add_0_l in STACK;rewrite STACK in ADDRESS;exact ADDRESS.
Qed.
