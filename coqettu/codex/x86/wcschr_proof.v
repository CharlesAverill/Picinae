(* wcschr -- musl i386, wide search with a conditional wcslen call

   SEMANTICS / SPECIFICATION
   Return the first matching wide-character pointer before or at the first NUL,
   or NULL if NUL is reached before a nonzero needle. The NUL-search path calls
   wcslen and reconstructs the pointer from its exact signed-shift result.
   Source: local Linux man-pages 6.9.1, /usr/share/man/man3/wcschr.3.gz
   (paraphrased). Full 32-bit wchar_t representations are covered.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x37b80; image base 0x10000; global RET 0x47bd7.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and needle: entry ESP+4 and ESP+8. Registers have declared widths.
   The original string through its first NUL avoids the 32-byte nested stack
   frame. No string length, match/stop witness or artificial count bound is
   assumed. The exact memory snapshot has two effective word writes for a
   nonzero needle and four for zero. The zero path also re-stores the unchanged
   first argument; that idempotent write is proved explicitly. Callee-saved
   registers, permissions and original return address are restored; RET adds
   four. Partial correctness in every containing program with caller, thunk
   and wcslen. Termination and concrete access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_calls
  i386_strings i386_wstrlen i386_wsearch i386_binary_call wcschr_support
  wcschr_i386 pc_thunk_bx_i386 wcslen_i386 wcslen_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcschr_post (s0 s:store):=
  cdecl_leaf_frame (wcschr_reference s0) s /\ wcschr_result s0 (s R_EAX).
Definition wcschr_cursor (s0 s:store):=
  wcschr_frame s0 (wcschr_m2 s0) 12 s /\ s R_EBX=wcschr_got /\
  s R_ECX=wcschr_needle s0 /\ wcschr_needle s0<>0 /\ exists k,
  s R_EDX=(cdecl_arg s0+4*k) mod 2^32 /\ wcschr_prefix s0 k.
Definition wcschr_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x47b80=>Some (s=s0)
  | 0x47b81=>Some (wcschr_frame s0 (wcschr_m1 s0) 4 s)
  | 0x47b86=>Some (wcschr_frame s0 (wcschr_m2 s0) 4 s /\ s R_EBX=0x47b86)
  | 0x47b9f=>Some (wcschr_frame s0 (wcschr_m3 s0) 28 s /\ s R_EBX=wcschr_got /\
      s R_EDX=cdecl_arg s0 /\ wcschr_needle s0=0)
  | 0x47ba3=>Some (wcschr_frame s0 (wcschr_m3 s0) 28 s /\ s R_EBX=wcschr_got /\ wcschr_needle s0=0)
  | 0x47ba8=>Some (wcschr_frame s0 (wcschr_m4 s0) 28 s /\ s R_EBX=wcschr_got /\
      wcschr_length s0 (s R_EAX) /\ wcschr_needle s0=0)
  | 0x47bc3=>Some (wcschr_cursor s0 s)
  | 0x47bd3=>Some (wcschr_frame s0 (wcschr_memory s0) 12 s /\ wcschr_result s0 (s R_EAX))
  | 0x47bd7=>Some (wcschr_post s0 s)
  | _=>None end | _=>None end.
Definition wcschr_exit:=at_address 0x47bd7.

Lemma wcschr_wcslen_supported:forall s0,code_supported wcslen_i386 (wcslen_invs s0) wcslen_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wcslen_i386 in NO. unfold wcslen_invs,wcslen_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wcschr_wcslen_disjoint:forall s0 a s t,wcslen_i386 s a<>None ->
  wcschr_invs s0 ((Addr a,s)::t)=None /\ wcschr_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold wcslen_i386,wcschr_invs,wcschr_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wcschr_wcslen_call:forall s0 sc,wcschr_pre s0 ->
  wcschr_frame s0 (wcschr_m4 s0) 32 sc ->sc R_EBX=wcschr_got ->wcschr_needle s0=0 ->forall t,
  nextinv wcschr_linked (wcschr_invs s0) wcschr_exit true ((Addr 0x47c10,sc)::t).
Proof.
  intros s0 sc PRE FRAME BX ZERO t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wcslen_i386 (wcslen_invs sc)) (xp2:=wcslen_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wcschr_linked_wcslen.
    + intros a s h EX NO. exact (proj1 (wcschr_wcslen_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wcslen_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wcschr_linked_wcslen.
    + apply wcschr_wcslen_supported.
    + apply wcschr_wcslen_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wcslen_exit,at_address in POST.
    destruct (a=?0x47c2e) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (wcslen_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (wcschr_callee_length s0 sc (sr R_EAX) PRE FRAME RESULT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (0x47c2e+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wcschr_linked) (ret:=0x47c2e) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (unary_call_return s0 0x47b86 0x47ba8 wcschr_got (fun _=>sr R_EAX) sc _ _ FRAME BX RETURN)
      as (PC & RF & B & AX).
    rewrite PC. apply NIHere'. change (wcschr_frame s0 (wcschr_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=wcschr_got /\ wcschr_length s0 ((reset_temps sr s2) R_EAX) /\ wcschr_needle s0=0).
    rewrite AX. exact (conj RF (conj B (conj ORIGINAL ZERO))).
Qed.

Theorem wcschr_correct_local:forall s0 (PRE0:wcschr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x47b80,s0)),
  satisfies_all wcschr_linked (wcschr_invs s0) wcschr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + clear PRE0. subst s. repeat x86_step.
      unfold wcschr_frame,unary_frame,wcschr_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0. unfold wcschr_frame,unary_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcschr_frame,unary_frame,wcschr_m2,unary_m2,unary_m1.
      psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0. destruct PRE as [F BX]. unfold wcschr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold wcschr_cursor,wcschr_frame,unary_frame,wcschr_m3,unary_m3,wcschr_got;psimpl;elimstore;psimpl.
      all: rewrite !wcschr_m2_stack in * by lia.
      all: fold (cdecl_arg s0) in *;fold (wcschr_needle s0) in *;csimpl.
      * repeat split;first[reflexivity|assumption].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[reflexivity|].
        split;[reflexivity|]. split;[assumption|]. exists 0. unfold cdecl_arg. psimpl. split;[reflexivity|]. split;intros i I;clear - I;lia.
    + clear PRE0. destruct PRE as [F [BX [DX ZERO]]]. unfold wcschr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcschr_frame,unary_frame. psimpl;elimstore;psimpl.
      rewrite wcschr_resave_arg. repeat split;first[reflexivity|assumption].
    + destruct PRE as [F [BX ZERO]]. ISA_invseek. apply wcschr_wcslen_call;[exact PRE0| | |exact ZERO].
      * unfold wcschr_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold wcschr_m4,unary_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl.
        repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
    + clear PRE0. destruct PRE as [F [BX [LENGTH ZERO]]]. unfold wcschr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcschr_frame,unary_frame,wcschr_memory,wcschr_snapshot.
      psimpl;elimstore;psimpl. rewrite wcschr_m4_stack by lia.
      rewrite ZERO. cbn [N.eqb]. split;[repeat split;first[reflexivity|assumption]|].
      fold (cdecl_arg s0). rewrite (N.mul_comm (s R_EAX) 4).
      exact (wcschr_zero_result s0 (s R_EAX) ZERO LENGTH).
    + unfold wcschr_cursor in PRE. destruct PRE as [F [BX [CX [NONZERO [k [DX PREFIX]]]]]].
      assert (NEEDLEBOUND:wcschr_needle s0<2^32) by (unfold wcschr_needle,binary_arg2;apply getmem_bound).
      pose proof (wcschr_snapshot_read s0 false k PRE0 (proj1 PREFIX)) as READ. clear PRE0.
      change (getmem 32 LittleE 4 (wcschr_m2 s0) (cdecl_arg s0+4*k)=
        getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)) in READ.
      unfold wcschr_frame,unary_frame in F. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold wcschr_cursor,wcschr_frame,unary_frame;psimpl;elimstore;psimpl.
      all: rewrite READ in *;csimpl.
      all: try rewrite (N.mod_small _ _ NEEDLEBOUND) in *.
      * unfold wcschr_memory,wcschr_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. exists k. split;[exact PREFIX|].
        right. repeat split;assumption.
      * unfold wcschr_memory,wcschr_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. exists k. split;[exact PREFIX|].
        left. split;[assumption|reflexivity].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[exact BX|].
        split;[first[reflexivity|exact CX]|]. split;[exact NONZERO|]. exists (k+1). split.
        -- replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- apply wcschr_prefix_advance;assumption.
    + destruct PRE as [F RESULT]. unfold wcschr_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND. clear PRE0.
      repeat x86_step. unfold wcschr_post,cdecl_leaf_frame,wcschr_reference. psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wcschr_saved_bx s0 BXBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem wcschr_correct:forall prog (EXT:wcschr_linked ⊆2 prog) s0 (PRE0:wcschr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x47b80,s0)),
  satisfies_all prog (wcschr_invs s0) wcschr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcschr_invs,wcschr_linked,updateall2,updateall,
      wcschr_i386,pc_thunk_bx_i386,wcslen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcschr_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem wcschr_returns:forall prog (EXT:wcschr_linked ⊆2 prog) s0 (PRE0:wcschr_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x47bd7,s)=(Addr 0x47b80,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x47bd7,s)::t)) (UT:unterminated wcschr_exit t),
  exists value,wcschr_result s0 value /\ cdecl_returned (wcschr_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcschr_correct prog EXT s0 PRE0 t (Addr 0x47bd7,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcschr_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (wcschr_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x47bd7) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wcschr_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wcschr_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
