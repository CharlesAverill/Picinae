(* bcmp -- musl i386, composition with the PIC thunk and memcmp

   SEMANTICS / SPECIFICATION
   Compare n bytes, returning zero exactly when the regions agree.
   Source: /usr/share/man/man3/bcmp.3.gz, Linux man-pages 6.9.1
   (paraphrased). This binary returns memcmp's exact first-byte difference.
   The System V i386 cdecl frame and original return address are restored.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   bcmp ELF VA 0x65d1d, global entry 0x75d1d, RET 0x75d41.
   Ghidra 12.0 PUBLIC, image base 0x10000, frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Arguments are entry stack words at ESP+4, ESP+8 and ESP+12.
   Both input regions must avoid the 36-byte nested-call stack footprint.
   Memory is exactly the seven word writes in bcmp_m7; all other bytes
   are preserved. EBX, ESI, EDI, EBP and access permissions are restored.
   Scope: partial correctness for every 32-bit count, including zero,
   in any containing program with the lifted caller, thunk and memcmp.
   Addresses wrap modulo 2^32. Termination/access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_compare i386_calls
  bcmp_i386 pc_thunk_bx_i386 memcmp_i386 bcmp_support memcmp_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition bcmp_pre (s0:store) := models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 36) 36 (cdecl_arg s0) (bcmp_count s0) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 36) 36 (bcmp_arg2 s0) (bcmp_count s0).
Definition bcmp_result (s0 s:store) := compare_result (s0 V_MEM32)
  (cdecl_arg s0) (bcmp_arg2 s0) (bcmp_count s0) (s R_EAX).
Definition bcmp_post (s0 s:store) := cdecl_leaf_frame (bcmp_reference s0) s /\ bcmp_result s0 s.
Definition bcmp_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x75d1d => Some (s=s0)
  | 0x75d1e => Some (bcmp_frame s0 (bcmp_m1 s0) 4 s)
  | 0x75d23 => Some (bcmp_frame s0 (bcmp_m2 s0) 4 s /\ s R_EBX=0x75d23)
  | 0x75d38 => Some (bcmp_frame s0 (bcmp_m5 s0) 28 s /\ s R_EBX=bcmp_got)
  | 0x75d3d => Some (bcmp_frame s0 (bcmp_m7 s0) 28 s /\ s R_EBX=bcmp_got /\ bcmp_result s0 s)
  | 0x75d41 => Some (bcmp_post s0 s)
  | _=>None end | _=>None end.
Definition bcmp_exit := at_address 0x75d41.

Lemma memcmp_code_supported : forall s0,
  code_supported memcmp_i386 (memcmp_invs s0) memcmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO; try (split; reflexivity).
  unfold memcmp_i386,memcmp_invs,memcmp_exit,at_address in *.
  destruct a as [|a]; [split;reflexivity|].
  repeat (destruct a as [a|a|]; cbn in *; try (split;reflexivity); try discriminate).
Qed.
Lemma bcmp_memcmp_disjoint : forall s0 a s t, memcmp_i386 s a<>None ->
  bcmp_invs s0 ((Addr a,s)::t)=None /\ bcmp_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold memcmp_i386,bcmp_invs,bcmp_exit,at_address in *.
  destruct a as [|a]; [contradiction|].
  repeat (destruct a as [a|a|]; cbn in *; try (split;reflexivity); try contradiction).
Qed.

Lemma bcmp_callee_args : forall s0 sc,
  bcmp_frame s0 (bcmp_m6 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ memcmp_arg2 sc=bcmp_arg2 s0 /\ memcmp_count sc=bcmp_count s0.
Proof.
  intros s0 sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold memcmp_arg2,memcmp_count. rewrite MEM,SP. psimpl.
  rewrite bcmp_m6_arg1,bcmp_m6_arg2,bcmp_m6_count. repeat split;reflexivity.
Qed.
Lemma bcmp_callee_pre : forall s0 sc, bcmp_pre s0 -> models x86typctx sc ->
  bcmp_frame s0 (bcmp_m6 s0) 32 sc -> memcmp_pre sc.
Proof.
  intros s0 sc (MDL0 & NOP & NOQ) MDL FRAME.
  destruct (bcmp_callee_args s0 sc FRAME) as (P & Q & N).
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold memcmp_pre. rewrite P,Q,N,SP. psimpl.
  split; [exact MDL|]. split; apply deep_stack_subregion;try lia;assumption.
Qed.
Lemma bcmp_callee_memory : forall s0 sc,
  bcmp_frame s0 (bcmp_m6 s0) 32 sc -> sc R_EBX=bcmp_got ->
  save_ebx_memory sc=bcmp_m7 s0.
Proof.
  intros s0 sc (MEM & SP & SI & DI & BP & RD & WR) BX.
  unfold save_ebx_memory,bcmp_m7. rewrite MEM,SP,BX. psimpl. reflexivity.
Qed.
Lemma bcmp_call_return : forall s0 sc sr x se,
  bcmp_pre s0 -> bcmp_frame s0 (bcmp_m6 s0) 32 sc -> sc R_EBX=bcmp_got ->
  memcmp_post sc sr -> cdecl_returned (save_ebx_reference sc) (sr R_EAX) x se ->
  x=Addr 0x75d3d /\ bcmp_frame s0 (bcmp_m7 s0) 28 se /\
  se R_EBX=bcmp_got /\ bcmp_result s0 se.
Proof.
  intros s0 sc sr x se (MDL0 & NOP & NOQ) FRAME BX [F RESULT] RETURN.
  destruct (bcmp_callee_args s0 sc FRAME) as (P & Q & N).
  pose proof (bcmp_callee_memory s0 sc FRAME BX) as SAVED.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,save_ebx_reference in RETURN. psimpl in RETURN.
  rewrite SAVED,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite bcmp_m7_call_address in PC. split;[exact PC|].
  split.
  - unfold bcmp_frame. rewrite MM,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - split;[exact EBX|]. unfold bcmp_result. rewrite AX.
    rewrite P,Q,N,MEM in RESULT. eapply compare_result_transport;[| |exact RESULT].
    + intros i I. apply bcmp_m6_byte with (n:=bcmp_count s0);assumption.
    + intros i I. apply bcmp_m6_byte with (n:=bcmp_count s0);assumption.
Qed.

Lemma bcmp_memcmp_call : forall s0 sc,
  bcmp_pre s0 -> models x86typctx sc ->
  bcmp_frame s0 (bcmp_m6 s0) 32 sc -> sc R_EBX=bcmp_got -> forall t,
  nextinv bcmp_linked (bcmp_invs s0) bcmp_exit true ((Addr 0x3f1a0,sc)::t).
Proof.
  intros s0 sc PRE MDL FRAME BX t.
  pose proof (bcmp_callee_pre s0 sc PRE MDL FRAME) as CPRE.
  unfold nextinv. intro XP0.
  eapply exec_subroutine with
    (Invs2:=closed_invs memcmp_i386 (memcmp_invs sc)) (xp2:=memcmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply bcmp_linked_memcmp.
    + intros a s h EX NO. exact (proj1 (memcmp_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply memcmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply bcmp_linked_memcmp.
    + apply memcmp_code_supported.
    + apply bcmp_memcmp_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,memcmp_exit,at_address in POST.
    destruct (a =? 0x3f1e1) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a. change (memcmp_post sc sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_ebx_reference sc) (sr R_EAX)
      (exitof (0x3f1e1+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=bcmp_linked) (ret:=0x3f1e1) (s:=sr).
      - reflexivity.
      - split;[reflexivity|exact (proj1 POST)].
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (bcmp_call_return s0 sc sr _ _ PRE FRAME BX POST RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (bcmp_frame s0 (bcmp_m7 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=bcmp_got /\ bcmp_result s0 (reset_temps sr s2)).
    exact (conj F (conj B R)).
Qed.

Theorem bcmp_correct_local : forall s0 (PRE0:bcmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75d1d,s0)),
  satisfies_all bcmp_linked (bcmp_invs s0) bcmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x75d1d,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant; [exact (proj1 PRE0)|apply bcmp_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold bcmp_frame,bcmp_m1,save_ebx_memory. psimpl. repeat split;reflexivity.
    + unfold bcmp_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      unfold bcmp_frame,bcmp_m2,bcmp_m1. psimpl;elimstore;psimpl.
      repeat split;reflexivity.
    + destruct PRE as [PRE BX]. unfold bcmp_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      unfold bcmp_frame,bcmp_m5,bcmp_m4,bcmp_m3,bcmp_got. psimpl;elimstore;psimpl.
      rewrite !bcmp_m2_stack by lia. unfold bcmp_count,bcmp_arg2,cdecl_arg.
      repeat split;reflexivity.
    + destruct PRE as [F BX].
      ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply bcmp_linked_welltyped|].
      intro CMDL. apply bcmp_memcmp_call;[exact PRE0|exact CMDL| |].
      * unfold bcmp_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold bcmp_m6. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + destruct PRE as [F [BX RESULT]]. unfold bcmp_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      unfold bcmp_post,cdecl_leaf_frame,bcmp_reference,bcmp_result in *. psimpl;elimstore;psimpl.
      destruct PRE0 as (MDL0 & NOP & NOQ).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND.
      rewrite (N.mod_small _ _ SPBOUND),(bcmp_m7_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem bcmp_correct : forall prog (EXT:bcmp_linked ⊆2 prog) s0 (PRE0:bcmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75d1d,s0)),
  satisfies_all prog (bcmp_invs s0) bcmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY.
  eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold bcmp_invs,bcmp_linked,updateall2,updateall,
      bcmp_i386,pc_thunk_bx_i386,memcmp_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply bcmp_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem bcmp_returns : forall prog (EXT:bcmp_linked ⊆2 prog) s0 (PRE0:bcmp_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x75d41,s)=(Addr 0x75d1d,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x75d41,s)::t))
  (UT:unterminated bcmp_exit t),
  exists result,compare_result (s0 V_MEM32) (cdecl_arg s0) (bcmp_arg2 s0) (bcmp_count s0) result /\
    cdecl_returned (bcmp_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (bcmp_correct prog EXT s0 PRE0 t (Addr 0x75d41,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (bcmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (bcmp_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x75d41) (s:=s).
    - apply EXT. reflexivity.
    - split;[reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (bcmp_m7 s0) (s0 R_ESP))) in ADDRESS.
  pose proof (bcmp_outer_stack s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.

Corollary bcmp_zero_iff : forall s0 s,bcmp_result s0 s ->
  (s R_EAX=0 <-> equal_prefix (s0 V_MEM32) (cdecl_arg s0) (bcmp_arg2 s0) (bcmp_count s0)).
Proof.
  intros s0 s RESULT. split.
  - intro ZERO. unfold bcmp_result in RESULT. rewrite ZERO in RESULT. apply compare_result_zero;exact RESULT.
  - intro EQ. destruct RESULT as [[ZERO _]|(k & K & PREFIX & DIFF & VALUE)];[exact ZERO|].
    exfalso. apply DIFF. exact (EQ k K).
Qed.
