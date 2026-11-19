(* strnlen -- musl i386, PIC wrapper composed with the optimized memchr

   SEMANTICS / SPECIFICATION
   Return the first NUL index below n, or n when all n bytes are nonzero.
   Source: /usr/share/man/man3/strnlen.3.gz, Linux man-pages 6.9.1
   (paraphrased). No caller-provided string length or terminator is required.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x6634f; Ghidra image base 0x10000; global RET 0x76384.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and bound are entry words at ESP+4 and ESP+8. Architectural
   registers have their declared widths. The n-byte input region avoids
   the 52-byte nested-call frame and address zero (normal valid-object
   requirement, so the wrapper's NULL test cannot discard a real match).
   n=0 permits a NULL pointer. Memory is exactly the specified ten word
   saves/call arguments/return addresses plus optional callee endpoint.
   The original return address, ESP, callee-saved registers and access
   permissions are restored. RET adds four to entry ESP.
   Scope: partial correctness for all 32-bit bounds in every containing
   program with caller/thunk/memchr code. Addresses wrap modulo 2^32.
   Termination and successful concrete accesses are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_strings i386_byte_search i386_calls
  strnlen_i386 pc_thunk_bx_i386 memchr_i386 memchr_support memchr_proof strnlen_support.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strnlen_post (s0 s:store):=exists used,
  cdecl_leaf_frame (strnlen_reference s0 used) s /\ strnlen_result s0 (s R_EAX).
Definition strnlen_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ =>match a with
  | 0x7634f=>Some (s=s0)
  | 0x76350=>Some (strnlen_frame s0 (strnlen_m1 s0) 4 s)
  | 0x76355=>Some (strnlen_frame s0 (strnlen_m2 s0) 4 s /\ s R_EBX=0x76355)
  | 0x76368=>Some (strnlen_frame s0 (strnlen_m5 s0) 28 s /\ s R_EBX=strnlen_got)
  | 0x7636d=>Some (exists used,strnlen_frame s0 (strnlen_memory s0 used) 28 s /\
      s R_EBX=strnlen_got /\
      forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) (s R_EAX))
  | 0x76384=>Some (strnlen_post s0 s)
  | _=>None end | _=>None end.
Definition strnlen_exit:=at_address 0x76384.
Lemma memchr_code_supported:forall s0,code_supported memchr_i386 (memchr_invs s0) memchr_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold memchr_i386,memchr_invs,memchr_exit,at_address in *.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strnlen_memchr_disjoint:forall s0 a s t,memchr_i386 s a<>None ->
  strnlen_invs s0 ((Addr a,s)::t)=None /\ strnlen_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold memchr_i386,strnlen_invs,strnlen_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strnlen_memchr_call:forall s0 sc,strnlen_pre s0 ->models x86typctx sc ->
  strnlen_frame s0 (strnlen_m6 s0) 32 sc ->sc R_EBX=strnlen_got ->forall t,
  nextinv strnlen_linked (strnlen_invs s0) strnlen_exit true ((Addr 0x30f00,sc)::t).
Proof.
  intros s0 sc PRE MDL FRAME BX t.
  pose proof (strnlen_callee_pre s0 sc PRE MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs memchr_i386 (memchr_invs sc)) (xp2:=memchr_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strnlen_linked_memchr.
    + intros a s h EX NO. exact (proj1 (memchr_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply memchr_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strnlen_linked_memchr.
    + apply memchr_code_supported.
    + apply strnlen_memchr_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,memchr_exit,at_address in POST.
    destruct (a=?0x30fde) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a. change (memchr_post sc sr) in POST.
    destruct POST as [used [LEAF RESULT]].
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (memchr_reference sc used) (sr R_EAX)
      (exitof (0x30fde+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strnlen_linked) (ret:=0x30fde) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl LEAF).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strnlen_call_return s0 sc sr used _ _ PRE FRAME BX RESULT RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (exists used,
      strnlen_frame s0 (strnlen_memory s0 used) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strnlen_got /\
      forward_search_result (s0 V_MEM32) (cdecl_arg s0) 0 (strnlen_count s0) ((reset_temps sr s2) R_EAX)).
    exists used. exact (conj F (conj B R)).
Qed.

Theorem strnlen_correct_local:forall s0 (PRE0:strnlen_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x7634f,s0)),
  satisfies_all strnlen_linked (strnlen_invs s0) strnlen_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x7634f,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strnlen_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold strnlen_frame,strnlen_m1,save_ebx_memory. psimpl. repeat split;reflexivity.
    + unfold strnlen_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strnlen_frame,strnlen_m2,strnlen_m1. psimpl;elimstore;psimpl.
      repeat split;reflexivity.
    + destruct PRE as [F BX]. unfold strnlen_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold strnlen_frame,strnlen_m5,strnlen_m4,strnlen_m3,strnlen_got.
      psimpl;elimstore;psimpl. rewrite !strnlen_m2_stack by lia.
      unfold strnlen_count,cdecl_arg. repeat split;reflexivity.
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply strnlen_linked_welltyped|].
      intro CMDL. apply strnlen_memchr_call;[exact PRE0|exact CMDL| |].
      * unfold strnlen_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold strnlen_m6. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [used [F [BX SEARCH]]]. unfold strnlen_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: exists used;unfold cdecl_leaf_frame,strnlen_reference;psimpl;elimstore;psimpl.
      all: pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      all: pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      all: rewrite (N.mod_small _ _ SPBOUND),(strnlen_saved_bx s0 used BXBOUND).
      all: rewrite !strnlen_outer_stack by lia.
      all: split;[repeat split;first[reflexivity|assumption]|].
      all: csimpl.
      * apply strnlen_null_result;[exact PRE0|]. rewrite BC in SEARCH. exact SEARCH.
      * apply strnlen_found_result;assumption.
Qed.

Theorem strnlen_correct:forall prog (EXT:strnlen_linked ⊆2 prog) s0 (PRE0:strnlen_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x7634f,s0)),
  satisfies_all prog (strnlen_invs s0) strnlen_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strnlen_invs,strnlen_linked,updateall2,updateall,
      strnlen_i386,pc_thunk_bx_i386,memchr_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strnlen_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strnlen_returns:forall prog (EXT:strnlen_linked ⊆2 prog) s0 (PRE0:strnlen_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x76384,s)=(Addr 0x7634f,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x76384,s)::t)) (UT:unterminated strnlen_exit t),
  exists used result,strnlen_result s0 result /\
    cdecl_returned (strnlen_reference s0 used) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strnlen_correct prog EXT s0 PRE0 t (Addr 0x76384,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strnlen_post s0 s) in INV. destruct INV as [used [FRAME RESULT]].
  assert (RETURN:cdecl_returned (strnlen_reference s0 used) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x76384) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists used,(s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strnlen_memory s0 used) (s0 R_ESP))) in ADDRESS.
  pose proof (strnlen_outer_stack s0 used 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.

