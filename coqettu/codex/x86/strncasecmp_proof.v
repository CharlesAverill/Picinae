(* strncasecmp -- musl i386, count-bounded non-leaf folded comparison

   SEMANTICS / SPECIFICATION
   Compare at most the ABI count of unsigned bytes after ASCII lowercase
   conversion. Zero count returns zero without reading either string. Otherwise
   stop on either NUL, folded mismatch, or the last allowed byte, returning the
   exact modular folded-byte difference. Source: local Linux man-pages 6.9.1,
   strcasecmp(3), paraphrased; exact folding follows this ELF's tolower calls.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x661b4, image base 0x10000, global RET 0x7625f.
   Ghidra 12.0 PUBLIC frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointers and count: ESP+4/+8/+12. Registers have declared widths. Read bytes
   before count exhaustion and through each original first NUL avoid the64-byte
   nested frame; the zero bound imposes no string-data condition. No caller
   length, stop witness, additional count bound or non-wrapping premise.
   The EAX PIC return word is overwritten by EBP's save. Exact memory includes
   four register saves, GOT local, optional saved count, and the final argument /
   return pair for nonzero counts. The argument re-store is idempotent. Compose
   all four tolower calls and both callee exits. Restore every saved register,
   permissions and original return address; RET adds four. Partial correctness
   in every containing program, without termination or access-success claims.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_calls i386_binary_call
  i386_strings i386_casecmp i386_casecmp_bounded i386_call_pair strncasecmp_support
  strncasecmp_i386 pc_thunk_ax_i386 tolower_i386 tolower_proof.
From Stdlib Require Import NArith Lia Bool.
Import X86Notations.
Open Scope N.
Definition strncasecmp_loop_regs (s0:store) (k:N) (s:store):=
  s R_ECX=cdecl_arg s0 /\ s R_EDX=strncasecmp_count s0-1 /\
  s R_ESI=(cdecl_arg s0+k) mod 2^32 /\ s R_EDI=(binary_arg2 s0+k) mod 2^32.
Definition strncasecmp_call_regs (s0:store) (k:N) (terminal:bool) (s:store):=
  s R_EDI=(binary_arg2 s0+k) mod 2^32 /\ (terminal=false ->s R_ESI=(cdecl_arg s0+k) mod 2^32).
Definition strncasecmp_guard (s0:store) (k:N) (terminal:bool):=if terminal then strncasecmp_stop s0 k else
  strncasecmp_p s0 k<>0 /\ strncasecmp_q s0 k<>0 /\ k+1<strncasecmp_count s0.
Definition strncasecmp_flag (terminal called:bool):=if terminal then called else true.
Definition strncasecmp_first_ra (terminal:bool):N:=if terminal then 0x76242 else 0x76216.
Definition strncasecmp_second_ra (terminal:bool):N:=if terminal then 0x7624f else 0x76223.
Definition strncasecmp_foldreg (terminal:bool):x86var:=if terminal then R_ESI else R_EBP.
Definition strncasecmp_pic_state (s0 s:store):=
  strncasecmp_frame s0 (strncasecmp_pic s0) 0 s /\ s R_EAX=0x761b9 /\
  s R_EBP=s0 R_EBP /\ s R_EDI=s0 R_EDI /\ s R_ESI=s0 R_ESI /\ s R_EBX=s0 R_EBX.
Definition strncasecmp_cursor (s0 s:store):=exists k called last,
  strncasecmp_frame s0 (strncasecmp_memory s0 called last) 44 s /\ strncasecmp_loop_regs s0 k s /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k.
Definition strncasecmp_advance (s0 s:store):=exists k called last,
  strncasecmp_frame s0 (strncasecmp_memory s0 called last) 44 s /\ strncasecmp_loop_regs s0 k s /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_guard s0 k false /\
  tolower_spec (strncasecmp_p s0 k)=tolower_spec (strncasecmp_q s0 k).
Definition strncasecmp_scan_prepare (s0 s:store):=exists k called last,
  strncasecmp_frame s0 (strncasecmp_memory s0 called last) 44 s /\ strncasecmp_loop_regs s0 k s /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_guard s0 k false /\ s R_EAX=strncasecmp_p s0 k.
Definition strncasecmp_terminal (s0 s:store):=exists k called last,
  strncasecmp_frame s0 (strncasecmp_memory s0 called last) 44 s /\ s R_EDI=(binary_arg2 s0+k) mod 2^32 /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_stop s0 k /\ s R_EAX=strncasecmp_p s0 k.
Definition strncasecmp_first_call (s0:store) (terminal:bool) (s:store):=exists k called last,
  strncasecmp_frame s0 (strncasecmp_argmem s0 (strncasecmp_flag terminal called) last (strncasecmp_p s0 k)) 60 s /\
  strncasecmp_call_regs s0 k terminal s /\ k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_guard s0 k terminal.
Definition strncasecmp_first_after (s0:store) (terminal:bool) (s:store):=exists k called,
  strncasecmp_frame s0 (strncasecmp_memory s0 (strncasecmp_flag terminal called)
    (Some (strncasecmp_p s0 k,strncasecmp_first_ra terminal))) 60 s /\ strncasecmp_call_regs s0 k terminal s /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_guard s0 k terminal /\ s R_EAX=tolower_spec (strncasecmp_p s0 k).
Definition strncasecmp_second_call (s0:store) (terminal:bool) (s:store):=exists k called,
  strncasecmp_frame s0 (strncasecmp_argmem s0 (strncasecmp_flag terminal called)
    (Some (strncasecmp_p s0 k,strncasecmp_first_ra terminal)) (strncasecmp_q s0 k)) 60 s /\
  strncasecmp_call_regs s0 k terminal s /\ k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\
  strncasecmp_guard s0 k terminal /\ s (strncasecmp_foldreg terminal)=tolower_spec (strncasecmp_p s0 k).
Definition strncasecmp_second_after (s0:store) (terminal:bool) (s:store):=exists k called,
  strncasecmp_frame s0 (strncasecmp_memory s0 (strncasecmp_flag terminal called)
    (Some (strncasecmp_q s0 k,strncasecmp_second_ra terminal))) 60 s /\ strncasecmp_call_regs s0 k terminal s /\
  k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_guard s0 k terminal /\
  s (strncasecmp_foldreg terminal)=tolower_spec (strncasecmp_p s0 k) /\ s R_EAX=tolower_spec (strncasecmp_q s0 k).
Definition strncasecmp_prepop (s0 s:store):=exists called stop,
  strncasecmp_frame s0 (strncasecmp_endmem s0 called stop) 44 s /\ strncasecmp_outcome s0 called stop (s R_EAX).
Definition strncasecmp_post (s0 s:store):=exists called stop,
  cdecl_leaf_frame (strncasecmp_reference s0 called stop) s /\ strncasecmp_outcome s0 called stop (s R_EAX).
Definition strncasecmp_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x761b4=>Some (s=s0)
  | 0x761b9=>Some (strncasecmp_pic_state s0 s)
  | 0x761c2=>Some (strncasecmp_frame s0 (save4_registers s0) 16 s /\ s R_EAX=strncasecmp_got)
  | 0x761e2=>Some (strncasecmp_advance s0 s)
  | 0x761e8=>Some (strncasecmp_cursor s0 s)
  | 0x76201=>Some (strncasecmp_scan_prepare s0 s)
  | 0x76211=>Some (strncasecmp_first_call s0 false s)
  | 0x76216=>Some (strncasecmp_first_after s0 false s)
  | 0x7621e=>Some (strncasecmp_second_call s0 false s)
  | 0x76223=>Some (strncasecmp_second_after s0 false s)
  | 0x76235=>Some (strncasecmp_terminal s0 s)
  | 0x7623d=>Some (strncasecmp_first_call s0 true s)
  | 0x76242=>Some (strncasecmp_first_after s0 true s)
  | 0x7624a=>Some (strncasecmp_second_call s0 true s)
  | 0x7624f=>Some (strncasecmp_second_after s0 true s)
  | 0x76258=>Some (strncasecmp_prepop s0 s)
  | 0x7625f=>Some (strncasecmp_post s0 s)
  | _=>None end | _=>None end.
Definition strncasecmp_exit:=at_address 0x7625f.
Lemma strncasecmp_tolower_supported:forall s0,code_supported tolower_i386 (tolower_invs s0) tolower_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold tolower_i386 in NO. unfold tolower_invs,tolower_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strncasecmp_tolower_disjoint:forall s0 a s t,tolower_i386 s a<>None ->
  strncasecmp_invs s0 ((Addr a,s)::t)=None /\ strncasecmp_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold tolower_i386,strncasecmp_invs,strncasecmp_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strncasecmp_tolower_call:forall s0 sc called arg ra,
  strncasecmp_frame s0 (strncasecmp_memory s0 called (Some (arg,ra))) 64 sc ->arg<256 ->ra<2^32 ->
  (forall se tail,strncasecmp_frame s0 (strncasecmp_memory s0 called (Some (arg,ra))) 60 se ->
    se R_EBX=sc R_EBX ->se R_EBP=sc R_EBP ->se R_ESI=sc R_ESI ->se R_EDI=sc R_EDI ->
    se R_EAX=tolower_spec arg ->nextinv' strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit true ((Addr ra,se)::tail)) ->
  forall t,nextinv strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 sc called arg ra FRAME ARG RA CONT t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs tolower_i386 (tolower_invs sc)) (xp2:=tolower_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strncasecmp_linked_tolower.
    + intros a s h EX NO. exact (proj1 (strncasecmp_tolower_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply tolower_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strncasecmp_linked_tolower.
    + apply strncasecmp_tolower_supported.
    + apply strncasecmp_tolower_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition in POST.
    destruct (tolower_exit ((Addr a,sr)::tl++t)) eqn:EXIT;[|contradiction].
    assert (RET:a=0x4f641 \/ a=0x4f645).
    { unfold tolower_exit,at_address in EXIT. apply Bool.orb_true_iff in EXIT.
      destruct EXIT as [EQ|EQ];apply N.eqb_eq in EQ;[left|right];exact EQ. }
    assert (LEAFPOST:cdecl_leaf_post sc (tolower_spec (cdecl_arg sc)) sr) by
      (destruct RET as [EQ|EQ];subst a;exact POST).
    assert (LOOK:strncasecmp_linked sr a=Some (1,i386_ret)) by
      (destruct RET as [EQ|EQ];subst a;reflexivity).
    assert (NOI:effinv true strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit
      ((Addr a,sr)::tl++t)=None) by (destruct RET as [EQ|EQ];subst a;reflexivity).
    eapply NIStep';[exact NOI|exact LOOK|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (tolower_spec (cdecl_arg sc))
      (exitof (a+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strncasecmp_linked) (ret:=a) (s:=sr).
      - exact LOOK.
      - exact LEAFPOST.
      - eapply CanStep;[exact LOOK|exact XS]. }
    destruct (strncasecmp_call_return s0 sc called arg ra _ _ FRAME ARG RA RETURN)
      as (PC & F & BX & BP & SI & DI & AX).
    rewrite PC. apply CONT;assumption.
Qed.
Lemma strncasecmp_first_subroutine:forall s0 k called terminal sc,
  strncasecmp_frame s0 (strncasecmp_memory s0 (strncasecmp_flag terminal called)
    (Some (strncasecmp_p s0 k,strncasecmp_first_ra terminal))) 64 sc ->
  strncasecmp_call_regs s0 k terminal sc ->k<strncasecmp_count s0 ->strncasecmp_prefix s0 k ->
  strncasecmp_guard s0 k terminal ->forall t,
  nextinv strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 k called terminal sc F REGS K PREFIX GUARD.
  apply (strncasecmp_tolower_call s0 sc (strncasecmp_flag terminal called) (strncasecmp_p s0 k) (strncasecmp_first_ra terminal) F).
  - unfold strncasecmp_p;apply getmem_bound.
  - unfold strncasecmp_first_ra;destruct terminal;lia.
  - intros se tail RF BX BP SI DI AX.
    assert (RR:strncasecmp_call_regs s0 k terminal se) by (unfold strncasecmp_call_regs in *;rewrite SI,DI;exact REGS).
    destruct terminal.
    + apply NIHere'. change (strncasecmp_first_after s0 true se). exists k,called.
      exact (conj RF (conj RR (conj K (conj PREFIX (conj GUARD AX))))).
    + apply NIHere'. change (strncasecmp_first_after s0 false se). exists k,called.
      exact (conj RF (conj RR (conj K (conj PREFIX (conj GUARD AX))))).
Qed.
Lemma strncasecmp_second_subroutine:forall s0 k called terminal sc,
  strncasecmp_frame s0 (strncasecmp_memory s0 (strncasecmp_flag terminal called)
    (Some (strncasecmp_q s0 k,strncasecmp_second_ra terminal))) 64 sc ->
  strncasecmp_call_regs s0 k terminal sc ->k<strncasecmp_count s0 ->strncasecmp_prefix s0 k ->
  strncasecmp_guard s0 k terminal ->sc (strncasecmp_foldreg terminal)=tolower_spec (strncasecmp_p s0 k) ->forall t,
  nextinv strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 k called terminal sc F REGS K PREFIX GUARD FIRST.
  apply (strncasecmp_tolower_call s0 sc (strncasecmp_flag terminal called) (strncasecmp_q s0 k) (strncasecmp_second_ra terminal) F).
  - unfold strncasecmp_q;apply getmem_bound.
  - unfold strncasecmp_second_ra;destruct terminal;lia.
  - intros se tail RF BX BP SI DI AX.
    assert (RR:strncasecmp_call_regs s0 k terminal se) by (unfold strncasecmp_call_regs in *;rewrite SI,DI;exact REGS).
    assert (FF:se (strncasecmp_foldreg terminal)=tolower_spec (strncasecmp_p s0 k)).
    { destruct terminal;cbn [strncasecmp_foldreg] in *;[rewrite SI|rewrite BP];exact FIRST. }
    destruct terminal.
    + apply NIHere'. change (strncasecmp_second_after s0 true se). exists k,called.
      exact (conj RF (conj RR (conj K (conj PREFIX (conj GUARD (conj FF AX)))))).
    + apply NIHere'. change (strncasecmp_second_after s0 false se). exists k,called.
      exact (conj RF (conj RR (conj K (conj PREFIX (conj GUARD (conj FF AX)))))).
Qed.
Theorem strncasecmp_correct_local:forall s0 (PRE0:strncasecmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x761b4,s0)),
  satisfies_all strncasecmp_linked (strncasecmp_invs s0) strncasecmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + clear PRE0. subst s. repeat x86_step.
      unfold strncasecmp_pic_state,strncasecmp_frame,strncasecmp_pic. psimpl;elimstore;psimpl. repeat split;reflexivity.
    + clear PRE0. destruct PRE as (F & AX & BP & DI & SI & BX). unfold strncasecmp_frame in F.
      destruct F as (MEM & SP & RD & WR). unfold strncasecmp_pic in MEM. repeat x86_step.
      unfold strncasecmp_frame,strncasecmp_pic,save4_registers,strncasecmp_got. psimpl;elimstore;psimpl.
      rewrite ?call_setmem_shadow. repeat split;first[reflexivity|assumption|intros;congruence].
    + destruct PRE as [F AX]. unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      pose proof (save4_stack_word s0 None 12 ltac:(lia)) as NC.
      pose proof (save4_stack_word s0 None 4 ltac:(lia)) as PP.
      pose proof (save4_stack_word s0 None 8 ltac:(lia)) as QOLD.
      pose proof (strncasecmp_outer_stack s0 false None 8 ltac:(lia)) as QQ.
      change (getmem 32 LittleE 4 (save4_registers s0) (12+s0 R_ESP)=strncasecmp_count s0) in NC.
      change (getmem 32 LittleE 4 (save4_registers s0) (4+s0 R_ESP)=cdecl_arg s0) in PP.
      change (getmem 32 LittleE 4 (save4_registers s0) (8+s0 R_ESP)=binary_arg2 s0) in QOLD.
      change (getmem 32 LittleE 4 (strncasecmp_base s0) (8+s0 R_ESP)=binary_arg2 s0) in QQ.
      pose proof (strncasecmp_count_bound s0) as CB. clear PRE0. repeat x86_step.
      all: unfold strncasecmp_prepop,strncasecmp_cursor,strncasecmp_frame,strncasecmp_loop_regs;psimpl;elimstore;psimpl.
      all: rewrite ?NC,?PP,?QQ,?QOLD in *;csimpl.
      * exists false,None. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
        unfold strncasecmp_outcome. repeat split;first[reflexivity|assumption|intros;congruence].
      * assert (DEC:msub 32 (strncasecmp_count s0) 1=strncasecmp_count s0-1) by (rewrite msub_sub,N.mod_small by lia;reflexivity).
        rewrite ?DEC. exists 0,false,None. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split.
        -- unfold cdecl_arg,binary_arg2;psimpl. repeat split;first[reflexivity|assumption|intros;congruence].
        -- split;[lia|]. unfold strncasecmp_prefix,case_equal_prefix. repeat split;intros i I;lia.
    + clear PRE0. destruct PRE as [k [called [last (F & REGS & K & PREFIX & GUARD & EQ)]]].
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_loop_regs in REGS. destruct REGS as (CX & DX & SI & DI). repeat x86_step.
      unfold strncasecmp_cursor,strncasecmp_frame,strncasecmp_loop_regs. psimpl;elimstore;psimpl.
      exists (k+1),called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split.
      * repeat split;first[reflexivity|assumption|f_equal;lia].
      * split;[exact (proj2 (proj2 GUARD))|]. apply case_equal_prefix_step;[exact PREFIX|exact (proj1 GUARD)|exact (proj1 (proj2 GUARD))|exact EQ].
    + destruct PRE as [k [called [last (F & REGS & K & PREFIX)]]].
      pose proof (strncasecmp_read_p s0 called last k PRE0 K PREFIX) as READP.
      pose proof (strncasecmp_read_q s0 called last k PRE0 K PREFIX) as READQ.
      pose proof (strncasecmp_count_bound s0) as CB.
      pose proof (bounded_case_last_pointer (cdecl_arg s0) (strncasecmp_count s0) k CB ltac:(lia) K) as END.
      clear PRE0. unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_loop_regs in REGS. destruct REGS as (CX & DX & SI & DI). repeat x86_step.
      all: unfold strncasecmp_terminal,strncasecmp_advance,strncasecmp_scan_prepare,strncasecmp_frame,strncasecmp_loop_regs;psimpl;elimstore;psimpl.
      all: rewrite ?READP,?READQ in *;csimpl.
      all: rewrite ?(N.mod_small k (2^32) ltac:(lia)) in *.
      * exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[first[reflexivity|assumption]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[unfold strncasecmp_stop;tauto|first[reflexivity|congruence]].
      * assert (LAST:k+1=strncasecmp_count s0) by lia.
        exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[first[reflexivity|assumption]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[unfold strncasecmp_stop;tauto|reflexivity].
      * exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[first[reflexivity|assumption]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[unfold strncasecmp_stop;tauto|reflexivity].
      * assert (ROOM:k+1<strncasecmp_count s0) by lia.
        exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[repeat split;assumption|congruence].
      * assert (ROOM:k+1<strncasecmp_count s0) by lia.
        exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[repeat split;assumption|reflexivity].
    + clear PRE0. destruct PRE as [k [called [last (F & REGS & K & PREFIX & GUARD & AX)]]].
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_loop_regs in REGS. destruct REGS as (CX & DX & SI & DI). repeat x86_step.
      unfold strncasecmp_first_call,strncasecmp_frame,strncasecmp_call_regs,strncasecmp_flag,strncasecmp_argmem.
      psimpl;elimstore;psimpl. rewrite strncasecmp_resave_arg,strncasecmp_setcount.
      exists k,true,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
      split;[split;first[reflexivity|assumption|intros;congruence]|]. split;[exact K|]. split;[exact PREFIX|exact GUARD].
    + clear PRE0. destruct PRE as [k [called [last (F & REGS & K & PREFIX & GUARD)]]]. ISA_invseek.
      apply (strncasecmp_first_subroutine s0 k called false);[| |exact K|exact PREFIX|exact GUARD].
      * unfold strncasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strncasecmp_entry_memory.
        repeat split;first[reflexivity|assumption|intros;congruence].
      * unfold strncasecmp_call_regs in *. destruct REGS as [DI SI]. psimpl. split;first[reflexivity|assumption|intros;congruence].
    + destruct PRE as [k [called (F & REGS & K & PREFIX & GUARD & AX)]].
      pose proof (strncasecmp_read_q s0 (strncasecmp_flag false called)
        (Some (strncasecmp_p s0 k,strncasecmp_first_ra false)) k PRE0 K PREFIX) as READQ.
      pose proof (casefold_byte_bound (strncasecmp_p s0 k) ltac:(unfold strncasecmp_p;apply getmem_bound)) as FB. clear PRE0.
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_call_regs in REGS. destruct REGS as [DI SI]. repeat x86_step.
      unfold strncasecmp_second_call,strncasecmp_frame,strncasecmp_call_regs,strncasecmp_argmem,strncasecmp_foldreg.
      psimpl;elimstore;psimpl. rewrite READQ. exists k,called. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
      split;[split;first[reflexivity|assumption|intros;congruence]|]. split;[exact K|]. split;[exact PREFIX|]. split;[exact GUARD|reflexivity].
    + clear PRE0. destruct PRE as [k [called (F & REGS & K & PREFIX & GUARD & FIRST)]]. ISA_invseek.
      apply (strncasecmp_second_subroutine s0 k called false);[| |exact K|exact PREFIX|exact GUARD|].
      * unfold strncasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strncasecmp_entry_memory.
        repeat split;first[reflexivity|assumption|intros;congruence].
      * unfold strncasecmp_call_regs in *. destruct REGS as [DI SI]. psimpl. split;first[reflexivity|assumption|intros;congruence].
      * psimpl. exact FIRST.
    + destruct PRE as [k [called (F & REGS & K & PREFIX & GUARD & FIRST & AX)]].
      cbn [strncasecmp_foldreg] in FIRST.
      pose proof (casefold_byte_bound (strncasecmp_p s0 k) ltac:(unfold strncasecmp_p;apply getmem_bound)) as FP.
      pose proof (casefold_byte_bound (strncasecmp_q s0 k) ltac:(unfold strncasecmp_q;apply getmem_bound)) as FQ.
      pose proof (strncasecmp_read_p s0 true (Some (strncasecmp_q s0 k,strncasecmp_second_ra false)) k PRE0 K PREFIX) as READP.
      pose proof (strncasecmp_outer_stack s0 true (Some (strncasecmp_q s0 k,strncasecmp_second_ra false)) 4 ltac:(lia)) as ARG.
      fold (cdecl_arg s0) in ARG. clear PRE0.
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_call_regs in REGS. destruct REGS as [DI SI]. specialize (SI eq_refl).
      unfold strncasecmp_flag in MEM.
      repeat x86_step.
      all: unfold strncasecmp_advance,strncasecmp_terminal,strncasecmp_frame,strncasecmp_loop_regs;psimpl;elimstore;psimpl.
      all: rewrite ?strncasecmp_count_load,?ARG,?READP in *;csimpl.
      * exists k,true,(Some (strncasecmp_q s0 k,strncasecmp_second_ra false)).
        split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[exact GUARD|assumption].
      * exists k,true,(Some (strncasecmp_q s0 k,strncasecmp_second_ra false)).
        split;[repeat split;first[reflexivity|assumption|intros;congruence]|]. split;[first[reflexivity|assumption]|].
        split;[exact K|]. split;[exact PREFIX|]. split;[unfold strncasecmp_stop;tauto|reflexivity].
    + clear PRE0. destruct PRE as [k [called [last (F & DI & K & PREFIX & STOP & AX)]]].
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold strncasecmp_first_call,strncasecmp_frame,strncasecmp_argmem,strncasecmp_call_regs,strncasecmp_flag.
      psimpl;elimstore;psimpl. exists k,called,last. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
      split;[split;[first[reflexivity|assumption]|discriminate]|]. split;[exact K|]. split;[exact PREFIX|exact STOP].
    + clear PRE0. destruct PRE as [k [called [last (F & REGS & K & PREFIX & GUARD)]]]. ISA_invseek.
      apply (strncasecmp_first_subroutine s0 k called true);[| |exact K|exact PREFIX|exact GUARD].
      * unfold strncasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strncasecmp_entry_memory.
        repeat split;first[reflexivity|assumption|intros;congruence].
      * unfold strncasecmp_call_regs in *. destruct REGS as [DI SI]. psimpl. split;first[reflexivity|assumption|intros;congruence].
    + destruct PRE as [k [called (F & REGS & K & PREFIX & GUARD & AX)]].
      pose proof (strncasecmp_read_q s0 (strncasecmp_flag true called)
        (Some (strncasecmp_p s0 k,strncasecmp_first_ra true)) k PRE0 K PREFIX) as READQ.
      pose proof (casefold_byte_bound (strncasecmp_p s0 k) ltac:(unfold strncasecmp_p;apply getmem_bound)) as FB. clear PRE0.
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strncasecmp_call_regs in REGS. destruct REGS as [DI SI]. repeat x86_step.
      unfold strncasecmp_second_call,strncasecmp_frame,strncasecmp_call_regs,strncasecmp_argmem,strncasecmp_foldreg.
      psimpl;elimstore;psimpl. rewrite READQ. exists k,called. split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
      split;[split;first[reflexivity|assumption|intros;congruence]|]. split;[exact K|]. split;[exact PREFIX|]. split;[exact GUARD|reflexivity].
    + clear PRE0. destruct PRE as [k [called (F & REGS & K & PREFIX & GUARD & FIRST)]]. ISA_invseek.
      apply (strncasecmp_second_subroutine s0 k called true);[| |exact K|exact PREFIX|exact GUARD|].
      * unfold strncasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strncasecmp_entry_memory.
        repeat split;first[reflexivity|assumption|intros;congruence].
      * unfold strncasecmp_call_regs in *. destruct REGS as [DI SI]. psimpl. split;first[reflexivity|assumption|intros;congruence].
      * psimpl. exact FIRST.
    + clear PRE0. destruct PRE as [k [called (F & REGS & K & PREFIX & STOP & FIRST & AX)]].
      cbn [strncasecmp_foldreg] in FIRST.
      unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold strncasecmp_prepop,strncasecmp_frame,strncasecmp_foldreg. psimpl;elimstore;psimpl.
      exists called,(Some k). split;[repeat split;first[reflexivity|assumption|intros;congruence]|].
      unfold strncasecmp_outcome. split;[exact K|]. split;[exact PREFIX|]. split;[exact STOP|reflexivity].
    + destruct PRE as [called [stop [F OUT]]]. unfold strncasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPB.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXB.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIB.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIB.
      pose proof ((proj1 PRE0) R_EBP 32 eq_refl) as BPB. clear PRE0.
      repeat x86_step. unfold strncasecmp_post,cdecl_leaf_frame,strncasecmp_reference,strncasecmp_endmem.
      psimpl;elimstore;psimpl.
      unfold strncasecmp_endmem in *. rewrite (N.mod_small _ _ SPB),(strncasecmp_saved_bx s0 called _ BXB),
        (strncasecmp_saved_si s0 called _ SIB),(strncasecmp_saved_di s0 called _ DIB),(strncasecmp_saved_bp s0 called _ BPB).
      exists called,stop. split;[repeat split;first[reflexivity|assumption|intros;congruence]|exact OUT].
Qed.
Theorem strncasecmp_correct:forall prog (EXT:strncasecmp_linked ⊆2 prog) s0 (PRE0:strncasecmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x761b4,s0)),
  satisfies_all prog (strncasecmp_invs s0) strncasecmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strncasecmp_invs,strncasecmp_linked,updateall2,updateall,
      strncasecmp_i386,pc_thunk_ax_i386,tolower_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strncasecmp_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strncasecmp_returns:forall prog (EXT:strncasecmp_linked ⊆2 prog) s0 (PRE0:strncasecmp_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x7625f,s)=(Addr 0x761b4,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x7625f,s)::t)) (UT:unterminated strncasecmp_exit t),
  exists value called stop,strncasecmp_result s0 value /\ strncasecmp_outcome s0 called stop value /\
    cdecl_returned (strncasecmp_reference s0 called stop) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strncasecmp_correct prog EXT s0 PRE0 t (Addr 0x7625f,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strncasecmp_post s0 s) in INV. destruct INV as [called [stop [FRAME OUT]]].
  assert (RETURN:cdecl_returned (strncasecmp_reference s0 called stop) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x7625f) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),called,stop. split;[eapply strncasecmp_outcome_result;exact OUT|].
  split;[exact OUT|]. split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strncasecmp_endmem s0 called stop) (s0 R_ESP))) in ADDRESS.
  unfold strncasecmp_endmem in ADDRESS. pose proof (strncasecmp_outer_stack s0 called
    (match stop with None=>None|Some k=>Some (strncasecmp_q s0 k,0x7624f) end) 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
