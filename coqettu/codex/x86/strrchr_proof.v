(* strrchr -- musl i386, composition of strlen and memrchr

   SEMANTICS / SPECIFICATION
   Search backwards through the first NUL for the last occurrence of the int
   argument converted to unsigned char. Return its pointer, or NULL if absent.
   The strlen call determines the NUL position; memrchr searches length+1 bytes.
   Source: local Linux man-pages 6.9.1, /usr/share/man/man3/strrchr.3.gz
   (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x663b6; image base 0x10000; global RET 0x763e6.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and int argument: entry ESP+4 and ESP+8, with declared register widths.
   The original byte string is non-NULL, non-wrapping through its first NUL and
   outside the 40-byte nested-call stack frame. No caller length or match/stop
   witness is assumed; the terminator-inclusive count bound is derived from
   object validity. Every int bit pattern is accepted. Exact memory describes
   all ten word writes, including overwritten argument/return slots and both
   callee saves. All saved registers, permissions and original return address
   are restored; RET adds four. Partial correctness in every containing program
   with caller, PIC thunk, strlen and memrchr; no termination/access-success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_stack4 i386_deep_stack i386_unary_call
  i386_binary_call i386_reverse i386_calls i386_strings strrchr_support
  strrchr_i386 pc_thunk_bx_i386 strlen_i386 strlen_proof memrchr_i386 memrchr_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strrchr_post (s0 s:store):=exists n,
  first_nul (s0 V_MEM32) (cdecl_arg s0) n /\
  cdecl_leaf_frame (strrchr_reference s0 n) s /\ strrchr_search s0 n (s R_EAX).
Definition strrchr_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x763b6=>Some (s=s0)
  | 0x763b7=>Some (strrchr_frame s0 (strrchr_m1 s0) 4 s)
  | 0x763bc=>Some (strrchr_frame s0 (strrchr_m2 s0) 4 s /\ s R_EBX=0x763bc)
  | 0x763c9=>Some (strrchr_frame s0 (strrchr_m3 s0) 28 s /\ s R_EBX=strrchr_got)
  | 0x763ce=>Some (strrchr_frame s0 (strrchr_m4 s0) 28 s /\ s R_EBX=strrchr_got /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) (s R_EAX))
  | 0x763dd=>Some (exists n,strrchr_frame s0 (strrchr_m7 s0 n) 28 s /\ s R_EBX=strrchr_got /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) n)
  | 0x763e2=>Some (exists n,strrchr_frame s0 (strrchr_memory s0 n) 28 s /\ s R_EBX=strrchr_got /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ strrchr_search s0 n (s R_EAX))
  | 0x763e6=>Some (strrchr_post s0 s)
  | _=>None end | _=>None end.
Definition strrchr_exit:=at_address 0x763e6.

Lemma strrchr_strlen_supported:forall s0,code_supported strlen_i386 (strlen_invs s0) strlen_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strlen_i386 in NO. unfold strlen_invs,strlen_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strrchr_strlen_disjoint:forall s0 a s t,strlen_i386 s a<>None ->
  strrchr_invs s0 ((Addr a,s)::t)=None /\ strrchr_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strlen_i386,strrchr_invs,strrchr_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strrchr_memrchr_supported:forall s0,code_supported memrchr_i386 (memrchr_invs s0) memrchr_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold memrchr_i386 in NO. unfold memrchr_invs,memrchr_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strrchr_memrchr_disjoint:forall s0 a s t,memrchr_i386 s a<>None ->
  strrchr_invs s0 ((Addr a,s)::t)=None /\ strrchr_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold memrchr_i386,strrchr_invs,strrchr_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strrchr_strlen_call:forall s0 sc,strrchr_pre s0 ->
  strrchr_frame s0 (strrchr_m4 s0) 32 sc ->sc R_EBX=strrchr_got ->forall t,
  nextinv strrchr_linked (strrchr_invs s0) strrchr_exit true ((Addr 0x3f500,sc)::t).
Proof.
  intros s0 sc PRE FRAME BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strlen_i386 (strlen_invs sc)) (xp2:=strlen_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strrchr_linked_strlen.
    + intros a s h EX NO. exact (proj1 (strrchr_strlen_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strlen_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strrchr_linked_strlen.
    + apply strrchr_strlen_supported.
    + apply strrchr_strlen_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strlen_exit,at_address in POST.
    destruct (a=?0x3f54c) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strlen_post sc sr) in POST. destruct POST as [F [n [AX FIRST]]].
    rewrite (unary_callee_arg s0 0x763bc 0x763ce sc FRAME),(proj1 FRAME) in FIRST.
    pose proof (strrchr_first_transport s0 n PRE FIRST) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (0x3f54c+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strrchr_linked) (ret:=0x3f54c) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (unary_call_return s0 0x763bc 0x763ce strrchr_got (fun _=>sr R_EAX) sc _ _ FRAME BX RETURN)
      as (PC & RF & B & VALUE).
    rewrite PC. apply NIHere'. change (strrchr_frame s0 (strrchr_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strrchr_got /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) ((reset_temps sr s2) R_EAX)).
    rewrite VALUE,AX. exact (conj RF (conj B ORIGINAL)).
Qed.
Lemma strrchr_memrchr_call:forall s0 n sc,strrchr_pre s0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  models x86typctx sc ->strrchr_frame s0 (strrchr_m8 s0 n) 32 sc ->sc R_EBX=strrchr_got ->forall t,
  nextinv strrchr_linked (strrchr_invs s0) strrchr_exit true ((Addr 0x47b00,sc)::t).
Proof.
  intros s0 n sc PRE FIRST MDL FRAME BX t.
  pose proof (strrchr_callee_pre s0 n sc PRE FIRST MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs memrchr_i386 (memrchr_invs sc)) (xp2:=memrchr_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strrchr_linked_memrchr.
    + intros a s h EX NO. exact (proj1 (strrchr_memrchr_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply memrchr_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strrchr_linked_memrchr.
    + apply strrchr_memrchr_supported.
    + apply strrchr_memrchr_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,memrchr_exit,at_address in POST.
    destruct (a=?0x47b38) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (memrchr_post sc sr) in POST. destruct POST as [F RESULT].
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_si_bx_reference sc) (sr R_EAX)
      (exitof (0x47b38+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strrchr_linked) (ret:=0x47b38) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strrchr_call_return s0 n sc sr _ _ PRE FIRST FRAME BX RESULT RETURN) as (PC & RF & B & SEARCH).
    rewrite PC. apply NIHere'. exists n.
    change (strrchr_frame s0 (strrchr_memory s0 n) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strrchr_got /\ first_nul (s0 V_MEM32) (cdecl_arg s0) n /\
      strrchr_search s0 n ((reset_temps sr s2) R_EAX)).
    exact (conj RF (conj B (conj FIRST SEARCH))).
Qed.

Theorem strrchr_correct_local:forall s0 (PRE0:strrchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x763b6,s0)),
  satisfies_all strrchr_linked (strrchr_invs s0) strrchr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x763b6,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strrchr_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold strrchr_frame,unary_frame,strrchr_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold strrchr_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strrchr_frame,unary_frame,strrchr_m2,unary_m2,unary_m1.
      psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold strrchr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strrchr_frame,unary_frame,strrchr_m3,unary_m3,strrchr_got.
      psimpl;elimstore;psimpl. rewrite strrchr_m2_stack by lia.
      unfold cdecl_arg. repeat split;first[reflexivity|assumption].
    + clear MDL. destruct PRE as [F BX]. ISA_invseek. apply strrchr_strlen_call;[exact PRE0| |].
      * unfold strrchr_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strrchr_m4,unary_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl.
        repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX FIRST]].
      pose proof (strrchr_bound s0 (s R_EAX) PRE0 FIRST) as BOUND. clear PRE0 MDL.
      unfold strrchr_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. exists (s R_EAX).
      unfold strrchr_frame,unary_frame,strrchr_m7,strrchr_m6,strrchr_m5.
      psimpl;elimstore;psimpl.
      rewrite !strrchr_m4_stack by lia. unfold cdecl_arg,binary_arg2.
      split;[repeat split;first[reflexivity|assumption]|]. split;[assumption|exact FIRST].
    + destruct PRE as [n [F [BX FIRST]]]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strrchr_linked_welltyped|].
      intro CMDL. apply strrchr_memrchr_call with (n:=n);[exact PRE0|exact FIRST|exact CMDL| |].
      * unfold strrchr_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strrchr_m8. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [n [F [BX [FIRST SEARCH]]]]. unfold strrchr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0 MDL.
      repeat x86_step. unfold strrchr_post. exists n. split;[exact FIRST|].
      unfold cdecl_leaf_frame,strrchr_reference. psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strrchr_saved_bx s0 n BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact SEARCH].
Qed.

Theorem strrchr_correct:forall prog (EXT:strrchr_linked ⊆2 prog) s0 (PRE0:strrchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x763b6,s0)),
  satisfies_all prog (strrchr_invs s0) strrchr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strrchr_invs,strrchr_linked,updateall2,updateall,
      strrchr_i386,pc_thunk_bx_i386,strlen_i386,memrchr_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strrchr_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strrchr_returns:forall prog (EXT:strrchr_linked ⊆2 prog) s0 (PRE0:strrchr_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x763e6,s)=(Addr 0x763b6,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x763e6,s)::t)) (UT:unterminated strrchr_exit t),
  exists n value,first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ strrchr_search s0 n value /\
    cdecl_returned (strrchr_reference s0 n) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strrchr_correct prog EXT s0 PRE0 t (Addr 0x763e6,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strrchr_post s0 s) in INV. destruct INV as [n [FIRST [FRAME SEARCH]]].
  assert (RETURN:cdecl_returned (strrchr_reference s0 n) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x763e6) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists n,(s R_EAX). split;[exact FIRST|]. split;[exact SEARCH|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strrchr_memory s0 n) (s0 R_ESP))) in ADDRESS.
  pose proof (strrchr_outer_stack s0 n 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
