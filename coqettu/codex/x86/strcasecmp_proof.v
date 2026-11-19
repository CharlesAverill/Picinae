(* strcasecmp -- musl i386, repeated non-leaf ASCII-folded comparison

   SEMANTICS / SPECIFICATION
   Compare unsigned bytes after ASCII lowercase conversion, stopping at the
   first folded mismatch or either NUL. Return the exact modular folded-byte
   difference. Source: local Linux man-pages 6.9.1, strcasecmp(3), paraphrased;
   the fixed ASCII fold follows this ELF's tolower calls. No caller input
   length, first-NUL or mismatch witness is assumed.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x65f40; image base 0x10000; global RET 0x75fb9.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   String pointers: entry ESP+4 and ESP+8. Registers have declared widths.
   Each original string through its first NUL avoids the 48-byte nested frame.
   Four actual tolower call sites compose both checked callee return sites.
   Raw equal nonzero bytes skip the scan calls. Every normal return executes
   the terminal pair; the final second-byte argument and RA overwrite prior
   call-slot values. Exact memory has four original register saves, PIC return,
   and the final argument/return pair. All saved registers and permissions are
   restored; RET pops the original address and adds four. Partial correctness
   in every containing program; no termination or concrete access-success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_calls i386_binary_call
  i386_strings i386_casecmp i386_call_pair strcasecmp_support strcasecmp_i386
  pc_thunk_bx_i386 tolower_i386 tolower_proof.
From Stdlib Require Import NArith Lia Bool.
Import X86Notations.
Open Scope N.
Definition strcasecmp_first_ra (terminal:bool):N:=if terminal then 0x75f9f else 0x75f7e.
Definition strcasecmp_second_ra (terminal:bool):N:=if terminal then 0x75fac else 0x75f8b.
Definition strcasecmp_guard (s0:store) (k:N) (terminal:bool):=
  if terminal then strcasecmp_stop s0 k else strcasecmp_nz s0 k.
Definition strcasecmp_cursor (s0 s:store):=exists k last,
  strcasecmp_frame s0 (strcasecmp_memory s0 last) 28 s /\ strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k.
Definition strcasecmp_advance (s0 s:store):=exists k last,
  strcasecmp_frame s0 (strcasecmp_memory s0 last) 28 s /\ strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k /\
  strcasecmp_nz s0 k /\ tolower_spec (strcasecmp_p s0 k)=tolower_spec (strcasecmp_q s0 k).
Definition strcasecmp_terminal (s0 s:store):=exists k last,
  strcasecmp_frame s0 (strcasecmp_memory s0 last) 28 s /\ strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k /\
  strcasecmp_stop s0 k /\ s R_EAX=strcasecmp_p s0 k.
Definition strcasecmp_first_call (s0:store) (terminal:bool) (s:store):=exists k last,
  strcasecmp_frame s0 (strcasecmp_argmem s0 last (strcasecmp_p s0 k)) 44 s /\ strcasecmp_regs s0 k s /\
  strcasecmp_prefix s0 k /\ strcasecmp_guard s0 k terminal.
Definition strcasecmp_first_after (s0:store) (terminal:bool) (s:store):=exists k,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (strcasecmp_p s0 k,strcasecmp_first_ra terminal))) 44 s /\
  strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k /\ strcasecmp_guard s0 k terminal /\
  s R_EAX=tolower_spec (strcasecmp_p s0 k).
Definition strcasecmp_second_call (s0:store) (terminal:bool) (s:store):=exists k,
  strcasecmp_frame s0 (strcasecmp_argmem s0 (Some (strcasecmp_p s0 k,strcasecmp_first_ra terminal)) (strcasecmp_q s0 k)) 44 s /\
  strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k /\ strcasecmp_guard s0 k terminal /\
  s R_EDI=tolower_spec (strcasecmp_p s0 k).
Definition strcasecmp_second_after (s0:store) (terminal:bool) (s:store):=exists k,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (strcasecmp_q s0 k,strcasecmp_second_ra terminal))) 44 s /\
  strcasecmp_regs s0 k s /\ strcasecmp_prefix s0 k /\ strcasecmp_guard s0 k terminal /\
  s R_EDI=tolower_spec (strcasecmp_p s0 k) /\ s R_EAX=tolower_spec (strcasecmp_q s0 k).
Definition strcasecmp_post (s0 s:store):=exists k,strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\
  cdecl_leaf_frame (strcasecmp_reference s0 k) s /\ s R_EAX=strcasecmp_diff s0 k.
Definition strcasecmp_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x75f40=>Some (s=s0)
  | 0x75f44=>Some (strcasecmp_frame s0 (save4_registers s0) 16 s)
  | 0x75f49=>Some (strcasecmp_frame s0 (strcasecmp_base s0) 16 s /\ s R_EBX=0x75f49)
  | 0x75f5c=>Some (strcasecmp_advance s0 s)
  | 0x75f62=>Some (strcasecmp_cursor s0 s)
  | 0x75f79=>Some (strcasecmp_first_call s0 false s)
  | 0x75f7e=>Some (strcasecmp_first_after s0 false s)
  | 0x75f86=>Some (strcasecmp_second_call s0 false s)
  | 0x75f8b=>Some (strcasecmp_second_after s0 false s)
  | 0x75f96=>Some (strcasecmp_terminal s0 s)
  | 0x75f9a=>Some (strcasecmp_first_call s0 true s)
  | 0x75f9f=>Some (strcasecmp_first_after s0 true s)
  | 0x75fa7=>Some (strcasecmp_second_call s0 true s)
  | 0x75fac=>Some (strcasecmp_second_after s0 true s)
  | 0x75fb9=>Some (strcasecmp_post s0 s)
  | _=>None end | _=>None end.
Definition strcasecmp_exit:=at_address 0x75fb9.
Lemma strcasecmp_tolower_supported:forall s0,code_supported tolower_i386 (tolower_invs s0) tolower_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold tolower_i386 in NO. unfold tolower_invs,tolower_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strcasecmp_tolower_disjoint:forall s0 a s t,tolower_i386 s a<>None ->
  strcasecmp_invs s0 ((Addr a,s)::t)=None /\ strcasecmp_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold tolower_i386,strcasecmp_invs,strcasecmp_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strcasecmp_tolower_call:forall s0 sc arg ra,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (arg,ra))) 48 sc ->arg<256 ->ra<2^32 ->
  (forall se tail,strcasecmp_frame s0 (strcasecmp_memory s0 (Some (arg,ra))) 44 se ->
    se R_EBX=sc R_EBX ->se R_EBP=sc R_EBP ->se R_ESI=sc R_ESI ->se R_EDI=sc R_EDI ->
    se R_EAX=tolower_spec arg ->nextinv' strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit true ((Addr ra,se)::tail)) ->
  forall t,nextinv strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 sc arg ra FRAME ARG RA CONT t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs tolower_i386 (tolower_invs sc)) (xp2:=tolower_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strcasecmp_linked_tolower.
    + intros a s h EX NO. exact (proj1 (strcasecmp_tolower_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply tolower_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strcasecmp_linked_tolower.
    + apply strcasecmp_tolower_supported.
    + apply strcasecmp_tolower_disjoint.
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
    assert (LOOK:strcasecmp_linked sr a=Some (1,i386_ret)) by
      (destruct RET as [EQ|EQ];subst a;reflexivity).
    assert (NOI:effinv true strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit
      ((Addr a,sr)::tl++t)=None) by (destruct RET as [EQ|EQ];subst a;reflexivity).
    eapply NIStep';[exact NOI|exact LOOK|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (tolower_spec (cdecl_arg sc))
      (exitof (a+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strcasecmp_linked) (ret:=a) (s:=sr).
      - exact LOOK.
      - exact LEAFPOST.
      - eapply CanStep;[exact LOOK|exact XS]. }
    destruct (strcasecmp_call_return s0 sc arg ra _ _ FRAME ARG RA RETURN)
      as (PC & F & BX & BP & SI & DI & AX).
    rewrite PC. apply CONT;assumption.
Qed.
Lemma strcasecmp_first_subroutine:forall s0 k terminal sc,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (strcasecmp_p s0 k,strcasecmp_first_ra terminal))) 48 sc ->
  strcasecmp_regs s0 k sc ->strcasecmp_prefix s0 k ->strcasecmp_guard s0 k terminal ->forall t,
  nextinv strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 k terminal sc F REGS PREFIX GUARD.
  apply (strcasecmp_tolower_call s0 sc (strcasecmp_p s0 k) (strcasecmp_first_ra terminal) F).
  - unfold strcasecmp_p;apply getmem_bound.
  - unfold strcasecmp_first_ra;destruct terminal;lia.
  - intros se tail RF BX BP SI DI AX. pose proof (strcasecmp_regs_transport s0 k sc se REGS BX BP SI) as RR.
    destruct terminal.
    + apply NIHere'. change (strcasecmp_first_after s0 true se).
      exists k. exact (conj RF (conj RR (conj PREFIX (conj GUARD AX)))).
    + apply NIHere'. change (strcasecmp_first_after s0 false se). exists k. exact (conj RF (conj RR (conj PREFIX (conj GUARD AX)))).
Qed.
Lemma strcasecmp_second_subroutine:forall s0 k terminal sc,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (strcasecmp_q s0 k,strcasecmp_second_ra terminal))) 48 sc ->
  strcasecmp_regs s0 k sc ->strcasecmp_prefix s0 k ->strcasecmp_guard s0 k terminal ->
  sc R_EDI=tolower_spec (strcasecmp_p s0 k) ->forall t,
  nextinv strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit true ((Addr 0x4f635,sc)::t).
Proof.
  intros s0 k terminal sc F REGS PREFIX GUARD FIRST.
  apply (strcasecmp_tolower_call s0 sc (strcasecmp_q s0 k) (strcasecmp_second_ra terminal) F).
  - unfold strcasecmp_q;apply getmem_bound.
  - unfold strcasecmp_second_ra;destruct terminal;lia.
  - intros se tail RF BX BP SI DI AX. pose proof (strcasecmp_regs_transport s0 k sc se REGS BX BP SI) as RR.
    rewrite FIRST in DI. destruct terminal.
    + apply NIHere'. change (strcasecmp_second_after s0 true se).
      exists k. exact (conj RF (conj RR (conj PREFIX (conj GUARD (conj DI AX))))).
    + apply NIHere'. change (strcasecmp_second_after s0 false se). exists k. exact (conj RF (conj RR (conj PREFIX (conj GUARD (conj DI AX))))).
Qed.
Theorem strcasecmp_correct_local:forall s0 (PRE0:strcasecmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75f40,s0)),
  satisfies_all strcasecmp_linked (strcasecmp_invs s0) strcasecmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + clear PRE0. subst s. repeat x86_step. unfold strcasecmp_frame,save4_registers. psimpl;elimstore;psimpl. repeat split;reflexivity.
    + clear PRE0. unfold strcasecmp_frame in PRE. destruct PRE as (MEM & SP & RD & WR).
      repeat x86_step. unfold strcasecmp_frame,strcasecmp_base. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0. destruct PRE as [F BX]. unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      repeat x86_step. unfold strcasecmp_cursor,strcasecmp_frame,strcasecmp_regs,strcasecmp_got. psimpl;elimstore;psimpl.
      pose proof (strcasecmp_outer_stack s0 None 4 ltac:(lia)) as PARG.
      pose proof (strcasecmp_outer_stack s0 None 8 ltac:(lia)) as QARG.
      change (getmem 32 LittleE 4 (strcasecmp_base s0) (4+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (4+s0 R_ESP)) in PARG.
      change (getmem 32 LittleE 4 (strcasecmp_base s0) (8+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP)) in QARG.
      rewrite PARG,QARG. exists 0,None. split;[repeat split;first[reflexivity|assumption]|].
      split;[unfold cdecl_arg,binary_arg2;psimpl;repeat split;first[reflexivity|assumption]|].
      unfold strcasecmp_prefix,case_equal_prefix. repeat split;intros i I;lia.
    + clear PRE0. destruct PRE as [k [last (F & REGS & PREFIX & NZ & EQ)]].
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      unfold strcasecmp_cursor,strcasecmp_frame,strcasecmp_regs. psimpl;elimstore;psimpl.
      exists (k+1),last. split;[repeat split;first[reflexivity|assumption]|]. split.
      * repeat split;first[reflexivity|assumption|f_equal;lia].
      * apply case_equal_prefix_step;[exact PREFIX|exact (proj1 NZ)|exact (proj2 NZ)|exact EQ].
    + destruct PRE as [k [last (F & REGS & PREFIX)]].
      pose proof (strcasecmp_read_p s0 last k PRE0 PREFIX) as READP.
      pose proof (strcasecmp_read_q s0 last k PRE0 PREFIX) as READQ. clear PRE0.
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      all: unfold strcasecmp_terminal,strcasecmp_advance,strcasecmp_first_call,strcasecmp_frame,strcasecmp_regs;psimpl;elimstore;psimpl.
      all: rewrite ?READP,?READQ in *;csimpl.
      * exists k,last. split;[repeat split;first[reflexivity|assumption]|]. split;[repeat split;first[reflexivity|assumption]|].
        split;[exact PREFIX|]. split;[unfold strcasecmp_stop;tauto|first[reflexivity|congruence]].
      * exists k,last. split;[repeat split;first[reflexivity|assumption]|]. split;[repeat split;first[reflexivity|assumption]|].
        split;[exact PREFIX|]. split;[unfold strcasecmp_stop;tauto|first[reflexivity|congruence]].
      * exists k,last. split;[repeat split;first[reflexivity|assumption]|]. split;[repeat split;first[reflexivity|assumption]|].
        split;[exact PREFIX|]. split;[split;assumption|congruence].
      * exists k,last. split;[unfold strcasecmp_argmem;repeat split;first[reflexivity|assumption]|].
        split;[repeat split;first[reflexivity|assumption]|]. split;[exact PREFIX|]. split;assumption.
    + clear PRE0. destruct PRE as [k [last (F & REGS & PREFIX & GUARD)]]. ISA_invseek.
      apply (strcasecmp_first_subroutine s0 k false);[| |exact PREFIX|exact GUARD].
      * unfold strcasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strcasecmp_entry_memory.
        repeat split;first[reflexivity|assumption].
      * unfold strcasecmp_regs in *. destruct REGS as (BX & BP & SI). psimpl. repeat split;first[reflexivity|assumption].
    + destruct PRE as [k (F & REGS & PREFIX & GUARD & AX)].
      pose proof (strcasecmp_read_q s0 (Some (strcasecmp_p s0 k,strcasecmp_first_ra false)) k PRE0 PREFIX) as READQ.
      pose proof (casefold_byte_bound (strcasecmp_p s0 k) ltac:(unfold strcasecmp_p;apply getmem_bound)) as FOLD. clear PRE0.
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      unfold strcasecmp_second_call,strcasecmp_frame,strcasecmp_regs,strcasecmp_argmem. psimpl;elimstore;psimpl.
      rewrite READQ. exists k. split;[repeat split;first[reflexivity|assumption]|].
      split;[repeat split;first[reflexivity|assumption]|]. split;[exact PREFIX|]. split;[exact GUARD|reflexivity].
    + clear PRE0. destruct PRE as [k (F & REGS & PREFIX & GUARD & DI)]. ISA_invseek.
      apply (strcasecmp_second_subroutine s0 k false);[| |exact PREFIX|exact GUARD|].
      * unfold strcasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strcasecmp_entry_memory.
        repeat split;first[reflexivity|assumption].
      * unfold strcasecmp_regs in *. destruct REGS as (BX & BP & SI). psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact DI.
    + destruct PRE as [k (F & REGS & PREFIX & NZ & DI & AX)].
      pose proof (strcasecmp_read_p s0 (Some (strcasecmp_q s0 k,strcasecmp_second_ra false)) k PRE0 PREFIX) as READP.
      pose proof (casefold_byte_bound (strcasecmp_p s0 k) ltac:(unfold strcasecmp_p;apply getmem_bound)) as FP.
      pose proof (casefold_byte_bound (strcasecmp_q s0 k) ltac:(unfold strcasecmp_q;apply getmem_bound)) as FQ. clear PRE0.
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      all: unfold strcasecmp_advance,strcasecmp_terminal,strcasecmp_frame,strcasecmp_regs;psimpl;elimstore;psimpl.
      all: rewrite ?READP in *;csimpl.
      * exists k,(Some (strcasecmp_q s0 k,strcasecmp_second_ra false)).
        split;[repeat split;first[reflexivity|assumption]|]. split;[repeat split;first[reflexivity|assumption]|].
        split;[exact PREFIX|]. split;[exact NZ|assumption].
      * exists k,(Some (strcasecmp_q s0 k,strcasecmp_second_ra false)).
        split;[repeat split;first[reflexivity|assumption]|]. split;[repeat split;first[reflexivity|assumption]|].
        split;[exact PREFIX|]. split;[unfold strcasecmp_stop;tauto|reflexivity].
    + clear PRE0. destruct PRE as [k [last (F & REGS & PREFIX & STOP & AX)]].
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      unfold strcasecmp_first_call,strcasecmp_frame,strcasecmp_regs,strcasecmp_argmem. psimpl;elimstore;psimpl.
      exists k,last. split;[repeat split;first[reflexivity|assumption]|].
      split;[repeat split;first[reflexivity|assumption]|]. split;[exact PREFIX|exact STOP].
    + clear PRE0. destruct PRE as [k [last (F & REGS & PREFIX & GUARD)]]. ISA_invseek.
      apply (strcasecmp_first_subroutine s0 k true);[| |exact PREFIX|exact GUARD].
      * unfold strcasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strcasecmp_entry_memory.
        repeat split;first[reflexivity|assumption].
      * unfold strcasecmp_regs in *. destruct REGS as (BX & BP & SI). psimpl. repeat split;first[reflexivity|assumption].
    + destruct PRE as [k (F & REGS & PREFIX & GUARD & AX)].
      pose proof (strcasecmp_read_q s0 (Some (strcasecmp_p s0 k,strcasecmp_first_ra true)) k PRE0 PREFIX) as READQ.
      pose proof (casefold_byte_bound (strcasecmp_p s0 k) ltac:(unfold strcasecmp_p;apply getmem_bound)) as FOLD. clear PRE0.
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold strcasecmp_regs in REGS. destruct REGS as (BX & BP & SI). repeat x86_step.
      unfold strcasecmp_second_call,strcasecmp_frame,strcasecmp_regs,strcasecmp_argmem. psimpl;elimstore;psimpl.
      rewrite READQ. exists k. split;[repeat split;first[reflexivity|assumption]|].
      split;[repeat split;first[reflexivity|assumption]|]. split;[exact PREFIX|]. split;[exact GUARD|reflexivity].
    + clear PRE0. destruct PRE as [k (F & REGS & PREFIX & GUARD & DI)]. ISA_invseek.
      apply (strcasecmp_second_subroutine s0 k true);[| |exact PREFIX|exact GUARD|].
      * unfold strcasecmp_frame in *. destruct F as (MEM & SP & RD & WR).
        psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. rewrite strcasecmp_entry_memory.
        repeat split;first[reflexivity|assumption].
      * unfold strcasecmp_regs in *. destruct REGS as (BX & BP & SI). psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact DI.
    + destruct PRE as [k (F & REGS & PREFIX & STOP & DI & AX)].
      unfold strcasecmp_frame in F. destruct F as (MEM & SP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPB.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXB.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIB.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIB.
      pose proof ((proj1 PRE0) R_EBP 32 eq_refl) as BPB. clear PRE0.
      repeat x86_step. unfold strcasecmp_post,cdecl_leaf_frame,strcasecmp_reference,strcasecmp_diff.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPB),(strcasecmp_saved_bx s0 _ BXB),(strcasecmp_saved_si s0 _ SIB),
        (strcasecmp_saved_di s0 _ DIB),(strcasecmp_saved_bp s0 _ BPB).
      exists k. split;[exact PREFIX|]. split;[exact STOP|]. split;[repeat split;first[reflexivity|assumption]|reflexivity].
Qed.
Theorem strcasecmp_correct:forall prog (EXT:strcasecmp_linked ⊆2 prog) s0 (PRE0:strcasecmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x75f40,s0)),
  satisfies_all prog (strcasecmp_invs s0) strcasecmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strcasecmp_invs,strcasecmp_linked,updateall2,updateall,
      strcasecmp_i386,pc_thunk_bx_i386,tolower_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strcasecmp_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strcasecmp_returns:forall prog (EXT:strcasecmp_linked ⊆2 prog) s0 (PRE0:strcasecmp_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x75fb9,s)=(Addr 0x75f40,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x75fb9,s)::t)) (UT:unterminated strcasecmp_exit t),
  exists value k,strcasecmp_result s0 value /\ strcasecmp_prefix s0 k /\ strcasecmp_stop s0 k /\
    cdecl_returned (strcasecmp_reference s0 k) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strcasecmp_correct prog EXT s0 PRE0 t (Addr 0x75fb9,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strcasecmp_post s0 s) in INV. destruct INV as [k (PREFIX & STOP & FRAME & VALUE)].
  assert (RETURN:cdecl_returned (strcasecmp_reference s0 k) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x75fb9) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),k. split;[rewrite VALUE;apply strcasecmp_result_at_stop;assumption|].
  split;[exact PREFIX|]. split;[exact STOP|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strcasecmp_memory s0 (Some (strcasecmp_q s0 k,0x75fac))) (s0 R_ESP))) in ADDRESS.
  pose proof (strcasecmp_outer_stack s0 (Some (strcasecmp_q s0 k,0x75fac)) 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
