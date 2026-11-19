(* wcsnlen -- musl i386, PIC call composition with wmemchr

   SEMANTICS / SPECIFICATION
   Search at most n four-byte wchar_t values for the first NUL. Return n
   when all n differ from zero; otherwise compute the signed 32-bit pointer
   difference divided by four. Source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/wcsnlen.3.gz (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x668a0; Ghidra image base 0x10000; global RET 0x768d8.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and bound: entry ESP+4 and ESP+8. Registers have declared widths.
   The 4*n-byte input region avoids the 32-byte nested-call frame and address
   zero. A zero bound permits NULL. No terminator or length witness is assumed.
   Exact memory: six word writes for EBX, the PIC return, copied arguments,
   and the callee return. Callee-saved registers, access permissions and the
   original return address are restored; RET adds four to entry ESP.
   Scope: partial correctness for every 32-bit bound in containing programs
   with caller/thunk/wmemchr code. The full theorem describes the exact SAR
   result; the count corollary applies when the signed byte difference fits.
   Addresses wrap modulo 2^32. Termination/access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_strings i386_wstrlen i386_calls
  wcsnlen_i386 pc_thunk_bx_i386 wmemchr_i386 wmemchr_proof wcsnlen_support.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcsnlen_post (s0 s:store):=
  cdecl_leaf_frame (wcsnlen_reference s0) s /\ wcsnlen_result s0 (s R_EAX).
Definition wcsnlen_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ =>match a with
  | 0x768a0=>Some (s=s0)
  | 0x768a1=>Some (wcsnlen_frame s0 (wcsnlen_m1 s0) 4 s)
  | 0x768a6=>Some (wcsnlen_frame s0 (wcsnlen_m2 s0) 4 s /\ s R_EBX=0x768a6)
  | 0x768b9=>Some (wcsnlen_frame s0 (wcsnlen_m5 s0) 28 s /\ s R_EBX=wcsnlen_got)
  | 0x768be=>Some (wcsnlen_frame s0 (wcsnlen_m6 s0) 28 s /\
      s R_EBX=wcsnlen_got /\
      wcsnlen_search s0 (s R_EAX))
  | 0x768d8=>Some (wcsnlen_post s0 s)
  | _=>None end | _=>None end.
Definition wcsnlen_exit:=at_address 0x768d8.
Lemma wmemchr_code_supported:forall s0,code_supported wmemchr_i386 (wmemchr_invs s0) wmemchr_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wmemchr_i386,wmemchr_invs,wmemchr_exit,at_address in *.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wcsnlen_wmemchr_disjoint:forall s0 a s t,wmemchr_i386 s a<>None ->
  wcsnlen_invs s0 ((Addr a,s)::t)=None /\ wcsnlen_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold wmemchr_i386,wcsnlen_invs,wcsnlen_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wcsnlen_wmemchr_call:forall s0 sc,wcsnlen_pre s0 ->models x86typctx sc ->
  wcsnlen_frame s0 (wcsnlen_m6 s0) 32 sc ->sc R_EBX=wcsnlen_got ->forall t,
  nextinv wcsnlen_linked (wcsnlen_invs s0) wcsnlen_exit true ((Addr 0x47c80,sc)::t).
Proof.
  intros s0 sc PRE MDL FRAME BX t.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wmemchr_i386 (wmemchr_invs sc)) (xp2:=wmemchr_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wcsnlen_linked_wmemchr.
    + intros a s h EX NO. exact (proj1 (wmemchr_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wmemchr_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wcsnlen_linked_wmemchr.
    + apply wmemchr_code_supported.
    + apply wcsnlen_wmemchr_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition in POST.
    destruct (wmemchr_exit ((Addr a,sr)::tl++t)) eqn:EXIT;[|contradiction].
    assert (RET:a=0x47c9e \/ a=0x47ca1).
    { unfold wmemchr_exit,at_address in EXIT. apply Bool.orb_true_iff in EXIT.
      destruct EXIT as [EQ|EQ];apply N.eqb_eq in EQ;[left|right];exact EQ. }
    assert (LEAFPOST:wmemchr_post sc sr) by (destruct RET as [EQ|EQ];subst a;exact POST).
    destruct LEAFPOST as [LEAF RESULT].
    assert (LOOK:wcsnlen_linked sr a=Some (1,i386_ret)) by
      (destruct RET as [EQ|EQ];subst a;reflexivity).
    assert (NOI:effinv true wcsnlen_linked (wcsnlen_invs s0) wcsnlen_exit
      ((Addr a,sr)::tl++t)=None) by (destruct RET as [EQ|EQ];subst a;reflexivity).
    eapply NIStep';[exact NOI|exact LOOK|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (a+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wcsnlen_linked) (ret:=a) (s:=sr).
      - exact LOOK.
      - exact (conj eq_refl LEAF).
      - eapply CanStep;[exact LOOK|exact XS]. }
    destruct (wcsnlen_call_return s0 sc sr _ _ PRE FRAME BX RESULT RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (
      wcsnlen_frame s0 (wcsnlen_m6 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wcsnlen_got /\ wcsnlen_search s0 ((reset_temps sr s2) R_EAX)).
    exact (conj F (conj B R)).
Qed.

Theorem wcsnlen_correct_local:forall s0 (PRE0:wcsnlen_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x768a0,s0)),
  satisfies_all wcsnlen_linked (wcsnlen_invs s0) wcsnlen_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x768a0,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wcsnlen_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold wcsnlen_frame,wcsnlen_m1,save_ebx_memory. psimpl. repeat split;reflexivity.
    + unfold wcsnlen_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcsnlen_frame,wcsnlen_m2,wcsnlen_m1. psimpl;elimstore;psimpl.
      repeat split;reflexivity.
    + destruct PRE as [F BX]. unfold wcsnlen_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcsnlen_frame,wcsnlen_m5,wcsnlen_m4,wcsnlen_m3,wcsnlen_got.
      psimpl;elimstore;psimpl. rewrite !wcsnlen_m2_stack by lia.
      unfold wcsnlen_count,cdecl_arg. repeat split;reflexivity.
    + destruct PRE as [F BX]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wcsnlen_linked_welltyped|].
      intro CMDL. apply wcsnlen_wmemchr_call;[exact PRE0|exact CMDL| |].
      * unfold wcsnlen_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wcsnlen_m6. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX SEARCH]]. unfold wcsnlen_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold cdecl_leaf_frame,wcsnlen_reference;psimpl;elimstore;psimpl.
      all: pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      all: pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      all: rewrite (N.mod_small _ _ SPBOUND),(wcsnlen_saved_bx s0 BXBOUND).
      all: rewrite !wcsnlen_outer_stack by lia.
      all: split;[repeat split;first[reflexivity|assumption]|].
      all: csimpl.
      * apply wcsnlen_null_result;[exact PRE0|]. rewrite BC in SEARCH. exact SEARCH.
      * apply wcsnlen_found_result;assumption.
Qed.

Theorem wcsnlen_correct:forall prog (EXT:wcsnlen_linked ⊆2 prog) s0 (PRE0:wcsnlen_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x768a0,s0)),
  satisfies_all prog (wcsnlen_invs s0) wcsnlen_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcsnlen_invs,wcsnlen_linked,updateall2,updateall,
      wcsnlen_i386,pc_thunk_bx_i386,wmemchr_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcsnlen_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wcsnlen_returns:forall prog (EXT:wcsnlen_linked ⊆2 prog) s0 (PRE0:wcsnlen_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x768d8,s)=(Addr 0x768a0,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x768d8,s)::t)) (UT:unterminated wcsnlen_exit t),
  exists result,wcsnlen_result s0 result /\ cdecl_returned (wcsnlen_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcsnlen_correct prog EXT s0 PRE0 t (Addr 0x768d8,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcsnlen_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (wcsnlen_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x768d8) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wcsnlen_m6 s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wcsnlen_outer_stack s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.

Corollary wcsnlen_result_small_bound:forall s0 result,
  wcsnlen_count s0<=2^29 ->wcsnlen_result s0 result ->
  (result=wcsnlen_count s0 /\ wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 (wcsnlen_count s0)) \/
  (exists k,k<wcsnlen_count s0 /\ wide_first_nul (s0 V_MEM32) (cdecl_arg s0) k /\ result=k).
Proof.
  intros s0 result BOUND [NONE|(k & K & FIRST & VALUE)];[left;exact NONE|].
  right. exists k. split;[exact K|]. split;[exact FIRST|]. rewrite VALUE.
  apply wide_length32_small. set (n:=wcsnlen_count s0) in *;clearbody n;clear - K BOUND;lia.
Qed.
