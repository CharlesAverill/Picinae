(* wcsrchr -- musl i386, last wide-character search via wcslen

   SEMANTICS / SPECIFICATION
   Return the last matching wide-character pointer at or before the first NUL,
   or NULL when no character matches. A zero needle returns the NUL pointer.
   Compose the actual wcslen call, then verify the descending scan and its
   unsigned pointer stop test. Source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/wcsrchr.3.gz (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x37c30; image base 0x10000; global RET 0x47c72.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and needle: entry ESP+4 and ESP+8, with declared register widths.
   The base is at least four, and the original wide string through its first
   NUL is a non-wrapping object outside the 32-byte nested-call stack frame.
   These pointer conditions justify the unsigned backwards stop test. No input
   length, stop/match witness or arbitrary count bound is supplied. Every
   32-bit needle representation is accepted. Output is the last-match/absence
   result in original memory, with an exact six-word stack-memory snapshot.
   EBX, ESI, EDI, EBP, permissions and original return address are restored;
   RET adds four to ESP. Partial correctness in every containing program with
   caller, PIC thunk and wcslen; no termination/access-success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_calls i386_unary_call
  i386_binary_call i386_strings i386_wstrlen i386_wsearch i386_backward
  wcsrchr_support wcsrchr_i386 pc_thunk_bx_i386 wcslen_i386 wcslen_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcsrchr_common (s0 s:store):=
  wcsrchr_frame s0 (wcsrchr_memory s0) 12 s /\ s R_ESI=cdecl_arg s0 /\
  s R_EDI=wcsrchr_needle s0 /\ s R_EBX=wcsrchr_got.
Definition wcsrchr_cursor (s0 s:store):=wcsrchr_common s0 s /\ wcsrchr_scan s0 (s R_EAX).
Definition wcsrchr_live (s0 s:store):=wcsrchr_common s0 s /\ exists n j,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ j<=n /\
  s R_EAX=cdecl_arg s0+4*j /\ wcsrchr_suffix s0 (j+1) n.
Definition wcsrchr_post (s0 s:store):=
  cdecl_leaf_frame (wcsrchr_reference s0) s /\ wcsrchr_result s0 (s R_EAX).
Definition wcsrchr_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x47c30=>Some (s=s0)
  | 0x47c37=>Some (wcsrchr_frame s0 (wcsrchr_m3 s0) 12 s /\ s R_ESI=cdecl_arg s0)
  | 0x47c3c=>Some (wcsrchr_frame s0 (wcsrchr_m4 s0) 12 s /\ s R_ESI=cdecl_arg s0 /\ s R_EBX=0x47c3c)
  | 0x47c4a=>Some (wcsrchr_frame s0 (wcsrchr_m5 s0) 28 s /\ s R_ESI=cdecl_arg s0 /\
      s R_EDI=wcsrchr_needle s0 /\ s R_EBX=wcsrchr_got)
  | 0x47c4f=>Some (wcsrchr_frame s0 (wcsrchr_memory s0) 28 s /\ s R_ESI=cdecl_arg s0 /\
      s R_EDI=wcsrchr_needle s0 /\ s R_EBX=wcsrchr_got /\ wcsrchr_length s0 (s R_EAX))
  | 0x47c63=>Some (wcsrchr_cursor s0 s)
  | 0x47c67=>Some (wcsrchr_live s0 s)
  | 0x47c6f=>Some (wcsrchr_frame s0 (wcsrchr_memory s0) 12 s /\ wcsrchr_result s0 (s R_EAX))
  | 0x47c72=>Some (wcsrchr_post s0 s)
  | _=>None end | _=>None end.
Definition wcsrchr_exit:=at_address 0x47c72.

Lemma wcsrchr_wcslen_supported:forall s0,code_supported wcslen_i386 (wcslen_invs s0) wcslen_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold wcslen_i386 in NO. unfold wcslen_invs,wcslen_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wcsrchr_wcslen_disjoint:forall s0 a s t,wcslen_i386 s a<>None ->
  wcsrchr_invs s0 ((Addr a,s)::t)=None /\ wcsrchr_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold wcslen_i386,wcsrchr_invs,wcsrchr_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wcsrchr_wcslen_call:forall s0 sc,wcsrchr_pre s0 ->
  wcsrchr_frame s0 (wcsrchr_memory s0) 32 sc ->sc R_ESI=cdecl_arg s0 ->
  sc R_EDI=wcsrchr_needle s0 ->sc R_EBX=wcsrchr_got ->forall t,
  nextinv wcsrchr_linked (wcsrchr_invs s0) wcsrchr_exit true ((Addr 0x47c10,sc)::t).
Proof.
  intros s0 sc PRE FRAME SI DI BX t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs wcslen_i386 (wcslen_invs sc)) (xp2:=wcslen_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wcsrchr_linked_wcslen.
    + intros a s h EX NO. exact (proj1 (wcsrchr_wcslen_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply wcslen_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wcsrchr_linked_wcslen.
    + apply wcsrchr_wcslen_supported.
    + apply wcsrchr_wcslen_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,wcslen_exit,at_address in POST.
    destruct (a=?0x47c2e) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (wcslen_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (wcsrchr_callee_length s0 sc (sr R_EAX) PRE FRAME RESULT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (0x47c2e+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wcsrchr_linked) (ret:=0x47c2e) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wcsrchr_call_return s0 sc (sr R_EAX) _ _ FRAME SI DI BX RETURN)
      as (PC & RF & S & D & B & AX).
    rewrite PC. apply NIHere'. change (wcsrchr_frame s0 (wcsrchr_memory s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_ESI=cdecl_arg s0 /\ (reset_temps sr s2) R_EDI=wcsrchr_needle s0 /\
      (reset_temps sr s2) R_EBX=wcsrchr_got /\ wcsrchr_length s0 ((reset_temps sr s2) R_EAX)).
    rewrite AX. exact (conj RF (conj S (conj D (conj B ORIGINAL)))).
Qed.

Theorem wcsrchr_correct_local:forall s0 (PRE0:wcsrchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x47c30,s0)),
  satisfies_all wcsrchr_linked (wcsrchr_invs s0) wcsrchr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + clear PRE0. subst s. repeat x86_step.
      unfold wcsrchr_frame. psimpl. fold (wcsrchr_m3 s0).
      try rewrite wcsrchr_m3_stack by lia. unfold cdecl_arg. repeat split;reflexivity.
    + clear PRE0. destruct PRE as [F SI]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold wcsrchr_frame,wcsrchr_m4. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0. destruct PRE as [F [SI BX]]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold wcsrchr_frame,wcsrchr_m5,wcsrchr_got. psimpl;elimstore;psimpl.
      rewrite wcsrchr_m4_stack by lia. unfold wcsrchr_needle,binary_arg2.
      repeat split;first[reflexivity|assumption].
    + destruct PRE as [F [SI [DI BX]]]. ISA_invseek. apply wcsrchr_wcslen_call;[exact PRE0| | | |].
      * unfold wcsrchr_frame in *. destruct F as (MEM & SP & BP & RD & WR).
        unfold wcsrchr_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl.
        repeat split;first[reflexivity|assumption].
      * psimpl. exact SI.
      * psimpl. exact DI.
      * psimpl. exact BX.
    + destruct PRE as [F [SI [DI [BX LENGTH]]]]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold wcsrchr_cursor,wcsrchr_common,wcsrchr_frame. psimpl;elimstore;psimpl.
      split;[repeat split;first[reflexivity|assumption]|].
      rewrite (N.mul_comm (s R_EAX) 4). apply wcsrchr_scan_start;assumption.
    + destruct PRE as [COMMON [n [i [FIRST [COUNT [AX SUFFIX]]]]]].
      destruct COMMON as [F [SI [DI BX]]]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      pose proof (proj1 (proj2 PRE0)) as BASE.
      pose proof (wcsrchr_first_bounds s0 n PRE0 FIRST n (N.le_refl n)) as END.
      destruct (backward_address_bounds (cdecl_arg s0) 4 n i ltac:(lia) BASE END COUNT) as [BOUND STOP].
      clear PRE0. repeat x86_step.
      all: unfold wcsrchr_live,wcsrchr_common,wcsrchr_frame;psimpl;elimstore;psimpl;csimpl.
      * pose proof (proj1 STOP BC) as ZERO. subst i.
        split;[repeat split;first[reflexivity|assumption]|]. exists n. split;[exact FIRST|].
        left. split;[reflexivity|exact SUFFIX].
      * assert (LIVE:0<i).
        { apply N.neq_0_lt_0. intro ZERO. pose proof (proj2 STOP ZERO) as LT.
          exact (N.lt_irrefl _ (N.lt_le_trans _ _ _ LT BC)). }
        split;[repeat split;first[reflexivity|assumption]|]. exists n,(i-1).
        split;[exact FIRST|]. split;[clear - COUNT LIVE;lia|]. split.
        -- try rewrite AX. apply backward_address_live;assumption.
        -- replace (i-1+1) with i by (clear - LIVE;lia). exact SUFFIX.
    + destruct PRE as [COMMON [n [j [FIRST [J [AX SUFFIX]]]]]].
      destruct COMMON as [F [SI [DI BX]]]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      pose proof (proj1 (proj2 PRE0)) as BASE.
      pose proof (wcsrchr_first_bounds s0 n PRE0 FIRST j J) as BOUND.
      pose proof (wcsrchr_read_first s0 n PRE0 FIRST j J) as READ.
      assert (NEEDLEBOUND:wcsrchr_needle s0<2^32) by (unfold wcsrchr_needle,binary_arg2;apply getmem_bound).
      clear PRE0. repeat x86_step.
      all: unfold wcsrchr_cursor,wcsrchr_common,wcsrchr_frame;psimpl;elimstore;psimpl.
      all: rewrite READ in *;csimpl.
      all: try rewrite (N.mod_small _ _ NEEDLEBOUND) in *.
      * split;[repeat split;first[reflexivity|assumption]|]. exists n. split;[exact FIRST|].
        right. exists j. repeat split;first[reflexivity|assumption].
      * split;[repeat split;first[reflexivity|assumption]|]. exists n,j.
        split;[exact FIRST|]. split;[clear - J;lia|]. split.
        -- apply backward_address_previous;assumption.
        -- intros k LO HI. destruct (N.eq_dec k j) as [EQ|NE];[subst k;assumption|].
           apply SUFFIX;[clear - LO NE;lia|exact HI].
    + destruct PRE as [F RESULT]. unfold wcsrchr_frame in F.
      destruct F as (MEM & SP & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIBOUND.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIBOUND. clear PRE0.
      repeat x86_step. unfold wcsrchr_post,cdecl_leaf_frame,wcsrchr_reference. psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wcsrchr_saved_bx s0 BXBOUND),
        (wcsrchr_saved_si s0 SIBOUND),(wcsrchr_saved_di s0 DIBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
Qed.

Theorem wcsrchr_correct:forall prog (EXT:wcsrchr_linked ⊆2 prog) s0 (PRE0:wcsrchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x47c30,s0)),
  satisfies_all prog (wcsrchr_invs s0) wcsrchr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcsrchr_invs,wcsrchr_linked,updateall2,updateall,
      wcsrchr_i386,pc_thunk_bx_i386,wcslen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcsrchr_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem wcsrchr_returns:forall prog (EXT:wcsrchr_linked ⊆2 prog) s0 (PRE0:wcsrchr_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x47c72,s)=(Addr 0x47c30,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x47c72,s)::t)) (UT:unterminated wcsrchr_exit t),
  exists value,wcsrchr_result s0 value /\ cdecl_returned (wcsrchr_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcsrchr_correct prog EXT s0 PRE0 t (Addr 0x47c72,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcsrchr_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (wcsrchr_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x47c72) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wcsrchr_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (wcsrchr_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.

Corollary wcsrchr_result_zero_needle:forall s0 result,
  wcsrchr_needle s0=0 ->wcsrchr_result s0 result ->exists n,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ result=cdecl_arg s0+4*n.
Proof.
  intros s0 result ZERO (n & FIRST & [NONE|HIT]).
  - destruct NONE as [RETURN SUFFIX].
    pose proof (SUFFIX n (N.le_0_l n) (N.le_refl n)) as DIFFERENT.
    unfold wcsrchr_word in DIFFERENT. rewrite ZERO,(proj2 (proj2 FIRST)) in DIFFERENT.
    contradiction.
  - destruct HIT as (j & J & MATCH & RETURN & SUFFIX).
    assert (SAME:j=n).
    { destruct (N.lt_ge_cases j n) as [LT|GE];[|clear - J GE;lia].
      exfalso. apply (proj1 (proj2 FIRST) j LT).
      change (wcsrchr_word s0 j=0). rewrite <- ZERO. exact MATCH. }
    subst j. exists n. split;assumption.
Qed.
