(* rindex -- musl i386 non-leaf last-byte search wrapper

   SEMANTICS / SPECIFICATION
   Last occurrence of the low argument byte through the original string's
   first NUL (inclusive); its pointer, or zero if absent. Source: local Linux
   man-pages6.9.1, index(3), paraphrased.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF0x65f1f/global0x75f1f, RET0x75f3f, Ghidra image base0x10000.
   Frozen Ghidra12.0 PUBLIC strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and character at ESP+4/+8; every32-bit character representation.
   Declared register widths, positive base pointer, every original nonzero
   prefix plus its next byte fits the address space and avoids the72-byte nested
   frame. No length or stopping witness input. Compose strrchr, strlen, memrchr
   and both PIC calls. Execution supplies first-NUL and last-match witnesses.
   Exact nested memory, all callee-saved registers and access permissions;
   RET pops original address. Partial correctness in every containing program.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call i386_strings
  rindex_support rindex_i386 pc_thunk_bx_i386 strrchr_i386 strrchr_proof
  strrchr_support i386_reverse memrchr_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition rindex_post (s0 s:store):=exists n,first_nul (s0 V_MEM32) (cdecl_arg s0) n /\
  cdecl_leaf_frame (rindex_reference s0 n) s /\ strrchr_search s0 n (s R_EAX).
Definition rindex_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x75f1f=>Some (s=s0)
  | 0x75f20=>Some (rindex_frame s0 (rindex_m1 s0) 4 s)
  | 0x75f25=>Some (rindex_frame s0 (rindex_m2 s0) 4 s /\ s R_EBX=0x75f25)
  | 0x75f36=>Some (rindex_frame s0 (rindex_m4 s0) 28 s /\ s R_EBX=rindex_got)
  | 0x75f3b=>Some (exists n,rindex_frame s0 (rindex_memory s0 n) 28 s /\
      s R_EBX=rindex_got /\ first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ strrchr_search s0 n (s R_EAX))
  | 0x75f3f=>Some (rindex_post s0 s)
  | _=>None end | _=>None end.
Definition rindex_exit:=at_address 0x75f3f.
Lemma strrchr_nested_code_supported:forall s0,
  code_supported strrchr_linked (strrchr_invs s0) strrchr_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strrchr_linked,updateall2,updateall,strrchr_i386,memrchr_i386,pc_thunk_bx_i386,strlen_i386,memrchr_i386 in NO.
  unfold strrchr_invs,strrchr_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma rindex_strrchr_disjoint:forall s0 a s t,strrchr_linked s a<>None ->
  rindex_invs s0 ((Addr a,s)::t)=None /\ rindex_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE.
  unfold strrchr_linked,updateall2,updateall,strrchr_i386,memrchr_i386,pc_thunk_bx_i386,strlen_i386,memrchr_i386 in CODE.
  unfold rindex_invs,rindex_exit,at_address.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma rindex_strrchr_call:forall s0 sc,rindex_pre s0 ->models x86typctx sc ->
  rindex_frame s0 (rindex_m5 s0) 32 sc ->sc R_EBX=rindex_got ->forall t,
  nextinv rindex_linked (rindex_invs s0) rindex_exit true ((Addr 0x763b6,sc)::t).
Proof.
  intros s0 sc PRE0 MDL FRAME BX t.
  pose proof (rindex_callee_pre s0 sc PRE0 MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strrchr_linked (strrchr_invs sc)) (xp2:=strrchr_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply rindex_linked_callee.
    + intros a s h EX NO. exact (proj1 (strrchr_nested_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strrchr_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply rindex_linked_callee.
    + apply strrchr_nested_code_supported.
    + apply rindex_strrchr_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strrchr_exit,at_address in POST.
    destruct (a=?0x763e6) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strrchr_post sc sr) in POST. destruct POST as [n [FIRST [FRAME0 OUT]]].
    pose proof (rindex_first_back s0 sc n PRE0 FRAME FIRST) as ORIGINAL.
    pose proof (rindex_search_back s0 sc n (sr R_EAX) PRE0 FRAME ORIGINAL OUT) as SEARCH.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (strrchr_reference sc n) (sr R_EAX)
      (exitof (0x763e6+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=rindex_linked) (ret:=0x763e6) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl FRAME0).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (rindex_call_return s0 sc n _ _ _ PRE0 FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (exists n,
      rindex_frame s0 (rindex_memory s0 n) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=rindex_got /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) n /\
      strrchr_search s0 n ((reset_temps sr s2) R_EAX)).
    exists n. rewrite R. exact (conj F (conj B (conj ORIGINAL SEARCH))).
Qed.
Theorem rindex_correct_local:forall s0 (PRE0:rindex_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75f1f,s0)),
  satisfies_all rindex_linked (rindex_invs s0) rindex_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x75f1f,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply rindex_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold rindex_frame,unary_frame,rindex_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. unfold rindex_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold rindex_frame,unary_frame,rindex_m2,unary_m2,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0 MDL. destruct PRE as [F BX]. unfold rindex_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold rindex_frame,unary_frame,rindex_m4,binary_m4,binary_m3,rindex_got.
      psimpl;elimstore;psimpl.
      rewrite !rindex_m2_stack by lia.
      unfold cdecl_arg,binary_arg2. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply rindex_linked_welltyped|].
      intro CMDL. apply rindex_strrchr_call;[exact PRE0|exact CMDL| |].
      * unfold rindex_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold rindex_m5,binary_entry_memory. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear MDL. destruct PRE as [n (F & BX & FIRST & OUT)]. unfold rindex_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold rindex_post,cdecl_leaf_frame,rindex_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(rindex_saved_bx s0 n BXBOUND).
      exists n. split;[exact FIRST|]. split;[repeat split;first[reflexivity|assumption]|exact OUT].
Qed.

Theorem rindex_correct:forall prog (EXT:rindex_linked ⊆2 prog) s0 (PRE0:rindex_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75f1f,s0)),
  satisfies_all prog (rindex_invs s0) rindex_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold rindex_invs,rindex_linked,updateall2,updateall,
      rindex_i386,pc_thunk_bx_i386,strrchr_i386,memrchr_i386,strlen_i386,strrchr_linked in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply rindex_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem rindex_returns:forall prog (EXT:rindex_linked ⊆2 prog) s0 (PRE0:rindex_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x75f3f,s)=(Addr 0x75f1f,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x75f3f,s)::t)) (UT:unterminated rindex_exit t),
  exists value n,first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ strrchr_search s0 n value /\
    cdecl_returned (rindex_reference s0 n) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (rindex_correct prog EXT s0 PRE0 t (Addr 0x75f3f,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (rindex_post s0 s) in INV. destruct INV as [n [FIRST [FRAME OUT]]].
  assert (RETURN:cdecl_returned (rindex_reference s0 n) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x75f3f) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),n. split;[exact FIRST|]. split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (rindex_memory s0 n) (s0 R_ESP))) in ADDRESS.
  pose proof (rindex_outer_stack s0 n 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
