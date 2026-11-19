(* wctype -- musl i386, non-leaf classification-name lookup

   SEMANTICS / SPECIFICATION
   Recognize the standard names alnum, alpha, blank, cntrl, digit, graph, lower,
   print, punct, space, upper, xdigit; descriptors are their table indices plus
   one. Every other name returns zero. Source: local Linux man-pages 6.9.1,
   /usr/share/man/man3/wctype.3.gz (paraphrased). Numeric descriptors, the fixed
   locale-independent table, and the first-byte optimization follow this ELF.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x25160, image base 0x10000, global RET 0x351d0.
   Static name table ELF 0x75360, global 0x85360, 73 exact bytes.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Name pointer: entry ESP+4; registers have declared widths. Original name
   bytes through the first NUL and the fixed static table avoid the 56-byte
   nested frame. Table bytes have the assigned ELF values. No caller string
   length, first-NUL or match witness. Actual PIC and repeated strcmp calls
   are composed; first-byte mismatches skip calls. An execution-derived list
   of comparison indices describes exact overwritten stack slots. All four
   saved registers and permissions are restored; RET pops the original address.
   Partial correctness in every containing program; no termination or concrete
   memory-access success claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_stack4 i386_deep_stack i386_calls
  i386_binary_call i386_strings i386_named_string wctype_support wctype_i386
  pc_thunk_bx_i386 strcmp_i386 strcmp_proof.
From Stdlib Require Import NArith Lia List Bool.
Import X86Notations.
Open Scope N.
Definition wctype_regs (s0:store) (j:N) (s:store):=
  s R_EBX=wctype_got /\ s R_ESI=wctype_target j /\ s R_EBP=cdecl_arg s0 /\ s R_EDI=j+1.
Definition wctype_cursor (s0:store) (s:store):=exists j calls,
  wctype_frame s0 (wctype_memory s0 calls) 28 s /\ wctype_regs s0 j s /\ j<=12 /\
  forall i,i<j ->wctype_matchb s0 i=false.
Definition wctype_advance (s0:store) (s:store):=exists j calls,
  wctype_frame s0 (wctype_memory s0 calls) 28 s /\ wctype_regs s0 j s /\ j<12 /\
  (forall i,i<j ->wctype_matchb s0 i=false) /\ wctype_matchb s0 j=false.
Definition wctype_call (s0:store) (s:store):=exists j calls,
  wctype_frame s0 (wctype_args_on s0 (wctype_memory s0 calls) j) 44 s /\ wctype_regs s0 j s /\ j<12 /\
  forall i,i<j ->wctype_matchb s0 i=false.
Definition wctype_aftercall (s0:store) (s:store):=exists j calls,
  wctype_frame s0 (wctype_memory s0 (j::calls)) 44 s /\ wctype_regs s0 j s /\ j<12 /\
  (forall i,i<j ->wctype_matchb s0 i=false) /\ (s R_EAX=0 <->wctype_matchb s0 j=true).
Definition wctype_prepop (s0 s:store):=exists calls,
  wctype_frame s0 (wctype_memory s0 calls) 28 s /\ wctype_result s0 (s R_EAX).
Definition wctype_post (s0 s:store):=exists calls,
  cdecl_leaf_frame (wctype_reference s0 calls) s /\ wctype_result s0 (s R_EAX).
Definition wctype_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x35160=>Some (s=s0)
  | 0x35169=>Some (wctype_frame s0 (save4_registers s0) 16 s /\ s R_EDI=1)
  | 0x3516e=>Some (wctype_frame s0 (wctype_base s0) 16 s /\ s R_EBX=0x3516e /\ s R_EDI=1)
  | 0x351a6=>Some (wctype_cursor s0 s)
  | 0x351a0=>Some (wctype_advance s0 s)
  | 0x351b7=>Some (wctype_call s0 s)
  | 0x351bc=>Some (wctype_aftercall s0 s)
  | 0x351c9=>Some (wctype_prepop s0 s)
  | 0x351d0=>Some (wctype_post s0 s)
  | _=>None end | _=>None end.
Definition wctype_exit:=at_address 0x351d0.
Lemma wctype_callee_supported:forall s0,code_supported strcmp_i386 (strcmp_invs s0) strcmp_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strcmp_i386 in NO. unfold strcmp_invs,strcmp_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma wctype_callee_disjoint:forall s0 a s t,strcmp_i386 s a<>None ->
  wctype_invs s0 ((Addr a,s)::t)=None /\ wctype_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strcmp_i386,wctype_invs,wctype_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma wctype_callee_call:forall s0 calls j sc,wctype_pre s0 ->j<12 ->models x86typctx sc ->
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->wctype_regs s0 j sc ->
  (forall i,i<j ->wctype_matchb s0 i=false) ->forall t,
  nextinv wctype_linked (wctype_invs s0) wctype_exit true ((Addr 0x3f400,sc)::t).
Proof.
  intros s0 calls j sc PRE0 J MDL FRAME REGS BEFORE t.
  pose proof (wctype_callee_pre s0 calls j sc PRE0 J MDL FRAME) as CPRE.
  unfold wctype_regs in REGS. destruct REGS as (BX & SI & BP & DI).
  unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strcmp_i386 (strcmp_invs sc)) (xp2:=strcmp_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply wctype_linked_strcmp.
    + intros a s h EX NO. exact (proj1 (wctype_callee_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strcmp_correct_local;[exact CPRE|]. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply wctype_linked_strcmp.
    + apply wctype_callee_supported.
    + apply wctype_callee_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strcmp_exit,at_address in POST.
    destruct (a=?0x3f43e) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strcmp_post sc sr) in POST. destruct POST as [F RESULT].
    pose proof (wctype_callee_result s0 calls j sc (sr R_EAX) PRE0 J FRAME RESULT) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned (save_si_bx_reference sc) (sr R_EAX)
      (exitof (0x3f43e+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=wctype_linked) (ret:=0x3f43e) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (wctype_call_return s0 calls j sc _ _ _ FRAME SI BX RETURN)
      as (PC & RF & RSI & RBX & RBP & RDI & AX).
    rewrite PC. apply NIHere'. change (wctype_aftercall s0 (reset_temps sr s2)).
    exists j,calls. split;[exact RF|]. split.
    + unfold wctype_regs. rewrite RBP,RDI,BP,DI. repeat split;assumption.
    + split;[exact J|]. split;[exact BEFORE|]. rewrite AX. exact ORIGINAL.
Qed.
Theorem wctype_correct_local:forall s0 (PRE0:wctype_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x35160,s0)),
  satisfies_all wctype_linked (wctype_invs s0) wctype_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x35160,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply wctype_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step.
      unfold wctype_frame,save4_registers. psimpl;elimstore;psimpl. repeat split;reflexivity.
    + clear PRE0 MDL. destruct PRE as [F DI]. unfold wctype_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold wctype_frame,wctype_base. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption|lia].
    + clear PRE0 MDL. destruct PRE as [F [BX DI]]. unfold wctype_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold wctype_cursor,wctype_frame,wctype_regs,wctype_got,wctype_target,wctype_table. psimpl;elimstore;psimpl.
      pose proof (wctype_outer_stack s0 nil 4 ltac:(lia)) as ARG.
      change (getmem 32 LittleE 4 (wctype_base s0) (4+s0 R_ESP)=
        getmem 32 LittleE 4 (s0 V_MEM32) (4+s0 R_ESP)) in ARG.
      rewrite ARG. exists 0,nil. split;[repeat split;first[reflexivity|assumption|lia]|].
      split;[unfold cdecl_arg;repeat split;first[reflexivity|assumption|lia]|]. split;[lia|]. intros i I;lia.
    + destruct PRE as [j [calls (F & REGS & J & BEFORE & MISS)]]. clear PRE0 MDL.
      unfold wctype_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold wctype_regs in REGS. destruct REGS as (BX & SI & BP & DI).
      assert (TB:wctype_target (j+1)<2^32) by (unfold wctype_target,wctype_table;lia).
      repeat x86_step. unfold wctype_cursor,wctype_frame,wctype_regs. psimpl;elimstore;psimpl.
      exists (j+1),calls. split;[repeat split;first[reflexivity|assumption|lia]|]. split.
      * unfold wctype_target,wctype_table in *. repeat split;try assumption;
          rewrite N.mod_small by lia;lia.
      * split;[lia|]. apply wctype_skip_step;assumption.
    + destruct PRE as [j [calls (F & REGS & LIMIT & BEFORE)]].
      pose proof (wctype_ro_read s0 calls (6*j) PRE0 ltac:(lia)) as READQ.
      change (getmem 32 LittleE 1 (wctype_memory s0 calls) (wctype_target j)=wctype_static (6*j)) in READQ.
      pose proof (wctype_input_read s0 calls 0 PRE0 ltac:(intros i I;lia)) as READP.
      rewrite N.add_0_r in READP. clear PRE0 MDL.
      unfold wctype_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold wctype_regs in REGS. destruct REGS as (BX & SI & BP & DI).
      repeat x86_step.
      all: unfold wctype_prepop,wctype_advance,wctype_call,wctype_frame,wctype_regs;psimpl;elimstore;psimpl.
      all: rewrite ?READQ,?READP in *;csimpl.
      * assert (EQ:j=12).
        { destruct (N.eq_dec j 12);[assumption|]. exfalso. apply (wctype_table_first_nonzero j ltac:(lia));assumption. }
        subst j. exists calls. split;[repeat split;first[reflexivity|assumption|lia]|]. right. split;[reflexivity|exact BEFORE].
      * assert (J:j<12) by (destruct (N.eq_dec j 12);[subst j;vm_compute in BC;contradiction|lia]).
        exists j,calls. split;[repeat split;first[reflexivity|assumption|lia]|].
        split;[repeat split;first[reflexivity|assumption|lia]|]. split;assumption.
      * assert (J:j<12) by (destruct (N.eq_dec j 12);[subst j;vm_compute in BC;contradiction|lia]).
        exists j,calls. split;[repeat split;first[reflexivity|assumption|lia]|].
        split;[repeat split;first[reflexivity|assumption|lia]|]. split;[exact J|]. split;[exact BEFORE|].
        destruct (wctype_matchb s0 j) eqn:M;[|reflexivity].
        pose proof (wctype_match_first s0 j M) as FIRST. unfold wctype_letter in FIRST. rewrite N.add_0_r in FIRST. contradiction.
    + destruct PRE as [j [calls (F & REGS & J & BEFORE)]]. ISA_invseek.
      eapply models_after_steps with (t1:=nil);[exact MDL|apply wctype_linked_welltyped|].
      intro CMDL. apply (wctype_callee_call s0 calls j);[exact PRE0|exact J|exact CMDL| | |exact BEFORE].
      * unfold wctype_frame in *. destruct F as (MEM & SP & RD & WR).
        unfold wctype_entry_on. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption|lia].
      * unfold wctype_regs in *. destruct REGS as (BX & SI & BP & DI). psimpl. repeat split;first[reflexivity|assumption|lia].
    + clear PRE0 MDL. destruct PRE as [j [calls (F & REGS & J & BEFORE & RESULT)]].
      unfold wctype_frame in F. destruct F as (MEM & SP & RD & WR).
      unfold wctype_regs in REGS. destruct REGS as (BX & SI & BP & DI).
      repeat x86_step.
      all: unfold wctype_advance,wctype_prepop,wctype_frame,wctype_regs;psimpl;elimstore;psimpl;csimpl.
      * exists (j::calls). split;[repeat split;first[reflexivity|assumption|lia]|].
        left. exists j. split;[exact J|]. split;[lia|]. split;[apply RESULT;assumption|exact BEFORE].
      * exists j,(j::calls). split;[repeat split;first[reflexivity|assumption|lia]|].
        split;[repeat split;first[reflexivity|assumption|lia]|]. split;[exact J|]. split;[exact BEFORE|].
        destruct (wctype_matchb s0 j) eqn:M;[|reflexivity]. pose proof (proj2 RESULT eq_refl). contradiction.
    + destruct PRE as [calls [F RESULT]]. unfold wctype_frame in F. destruct F as (MEM & SP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIBOUND.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIBOUND.
      pose proof ((proj1 PRE0) R_EBP 32 eq_refl) as BPBOUND. clear PRE0 MDL.
      repeat x86_step. unfold wctype_post,cdecl_leaf_frame,wctype_reference. psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(wctype_saved_bx s0 calls BXBOUND),(wctype_saved_si s0 calls SIBOUND),
        (wctype_saved_di s0 calls DIBOUND),(wctype_saved_bp s0 calls BPBOUND).
      exists calls. split;[repeat split;first[reflexivity|assumption|lia]|exact RESULT].
Qed.
Theorem wctype_correct:forall prog (EXT:wctype_linked ⊆2 prog) s0 (PRE0:wctype_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x35160,s0)),
  satisfies_all prog (wctype_invs s0) wctype_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wctype_invs,wctype_linked,updateall2,updateall,
      wctype_i386,pc_thunk_bx_i386,strcmp_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wctype_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wctype_returns:forall prog (EXT:wctype_linked ⊆2 prog) s0 (PRE0:wctype_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x351d0,s)=(Addr 0x35160,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x351d0,s)::t)) (UT:unterminated wctype_exit t),
  exists value calls,wctype_result s0 value /\ cdecl_returned (wctype_reference s0 calls) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wctype_correct prog EXT s0 PRE0 t (Addr 0x351d0,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wctype_post s0 s) in INV. destruct INV as [calls [FRAME RESULT]].
  assert (RETURN:cdecl_returned (wctype_reference s0 calls) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x351d0) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX),calls. split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (wctype_memory s0 calls) (s0 R_ESP))) in ADDRESS.
  pose proof (wctype_outer_stack s0 calls 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
