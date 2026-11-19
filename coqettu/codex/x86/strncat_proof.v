(* strncat -- musl i386, strlen composition and bounded append

   SEMANTICS / SPECIFICATION
   Append up to count nonzero source bytes to the destination's first NUL,
   always write a terminating NUL, and return the original destination pointer.
   Both lengths are supplied by execution. Source: local Linux man-pages6.9.1,
   strncat(3), paraphrased. Exact memory also includes the real stack writes.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF0x2f560/global0x3f560, RET0x3f5bb, image base0x10000.
   Ghidra12.0 PUBLIC frozen strict typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Destination/source/count at entry ESP+4/+8/+12. Declared register widths;
   destination through first NUL avoids the32-byte call frame. For every
   reachable source prefix below count, destination writes avoid the full
   stack/argument window; source reads avoid earlier destination writes and
   call-frame writes. No caller lengths, stop witnesses or artificial count
   bound. Count0 admits a NULL source. Exact memory, original destination
   prefix/source copy/NUL, restored saved registers, permissions and original RA.
   Partial correctness in all containing programs; no termination/access claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_calls i386_unary_call i386_binary_call i386_ternary_call
  i386_strings i386_byte_copy i386_search_arith strncat_support strncat_i386 strlen_i386 strlen_proof pc_thunk_bx_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strncat_loop (s0:store) (d k:N) (s:store):=
  strncat_frame s0 (strncat_memory s0 d k) 12 s /\
  s R_ESI=strncat_p s0 /\ s R_EDI=(strncat_q s0+k) mod 2^32 /\
  s R_EAX=(strncat_p s0+d+k) mod 2^32 /\ s R_ECX=(strncat_p s0+d+strncat_count s0) mod 2^32 /\
  first_nul (s0 V_MEM32) (strncat_p s0) d /\ k<=strncat_count s0 /\ nonzero_prefix (s0 V_MEM32) (strncat_q s0) k.
Definition strncat_write (s0 s:store):=exists d k,strncat_loop s0 d k s /\ k<strncat_count s0 /\
  s R_EDX=getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k) /\ getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k)<>0.
Definition strncat_post (s0 s:store):=exists d k,strncat_outcome s0 d k /\
  cdecl_leaf_frame (strncat_reference s0 d k) s /\ s R_EAX=strncat_p s0.
Definition strncat_invs (s0:store) (t:trace):option Prop:=match t with (Addr a,s)::_=>match a with
  | 0x3f560=>Some (s=s0)
  | 0x3f563=>Some (strncat_frame s0 (strncat_m3 s0) 12 s /\ s R_EDI=s0 R_EDI)
  | 0x3f567=>Some (strncat_frame s0 (strncat_m3 s0) 12 s /\ s R_ESI=strncat_p s0 /\ s R_EDI=s0 R_EDI)
  | 0x3f56c=>Some (strncat_frame s0 (strncat_m4 s0) 12 s /\ s R_EBX=0x3f56c /\ s R_ESI=strncat_p s0 /\ s R_EDI=s0 R_EDI)
  | 0x3f57a=>Some (strncat_frame s0 (strncat_m5 s0) 28 s /\ s R_EBX=strncat_got /\ s R_ESI=strncat_p s0 /\ s R_EDI=strncat_q s0)
  | 0x3f57f=>Some (strncat_frame s0 (strncat_m6 s0) 28 s /\ s R_EBX=strncat_got /\ s R_ESI=strncat_p s0 /\ s R_EDI=strncat_q s0 /\
      first_nul (s0 V_MEM32) (strncat_p s0) (s R_EAX))
  | 0x3f5a8=>Some (exists d k,strncat_loop s0 d k s)
  | 0x3f5ac=>Some (exists d k,strncat_loop s0 d k s /\ k<strncat_count s0)
  | 0x3f5a0=>Some (strncat_write s0 s)
  | 0x3f5b3=>Some (exists d k,strncat_loop s0 d k s /\ (k=strncat_count s0 \/ getmem 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k)=0))
  | 0x3f5b8=>Some (exists d k,strncat_frame s0 (strncat_endmem s0 d k) 12 s /\ s R_EAX=strncat_p s0 /\ strncat_outcome s0 d k)
  | 0x3f5bb=>Some (strncat_post s0 s)
  | _=>None end | _=>None end.
Definition strncat_exit:=at_address 0x3f5bb.
Lemma strncat_strlen_supported:forall s0,code_supported strlen_i386 (strlen_invs s0) strlen_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strlen_i386 in NO. unfold strlen_invs,strlen_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strncat_strlen_disjoint:forall s0 a s t,strlen_i386 s a<>None ->
  strncat_invs s0 ((Addr a,s)::t)=None /\ strncat_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strlen_i386,strncat_invs,strncat_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strncat_strlen_call:forall s0 sc,strncat_pre s0 ->strncat_frame s0 (strncat_m6 s0) 32 sc ->
  sc R_EBX=strncat_got ->sc R_ESI=strncat_p s0 ->sc R_EDI=strncat_q s0 ->forall t,
  nextinv strncat_linked (strncat_invs s0) strncat_exit true ((Addr 0x3f500,sc)::t).
Proof.
  intros s0 sc PRE FRAME BX SI DI t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strlen_i386 (strlen_invs sc)) (xp2:=strlen_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strncat_linked_strlen.
    + intros a s h EX NO. exact (proj1 (strncat_strlen_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strlen_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strncat_linked_strlen.
    + apply strncat_strlen_supported.
    + apply strncat_strlen_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strlen_exit,at_address in POST.
    destruct (a=?0x3f54c) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strlen_post sc sr) in POST. destruct POST as [F [d [AX FIRST]]].
    rewrite (strncat_callee_arg s0 sc FRAME),(proj1 FRAME) in FIRST.
    pose proof (strncat_first_back s0 d PRE FIRST) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (0x3f54c+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strncat_linked) (ret:=0x3f54c) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strncat_call_return s0 sc _ _ _ FRAME BX SI DI RETURN) as (PC & RF & B & S & D & VALUE).
    rewrite PC. apply NIHere'. change (strncat_frame s0 (strncat_m6 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=strncat_got /\ (reset_temps sr s2) R_ESI=strncat_p s0 /\
      (reset_temps sr s2) R_EDI=strncat_q s0 /\ first_nul (s0 V_MEM32) (strncat_p s0) ((reset_temps sr s2) R_EAX)).
    rewrite VALUE,AX. exact (conj RF (conj B (conj S (conj D ORIGINAL)))).
Qed.
Theorem strncat_correct_local:forall s0 (PRE0:strncat_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x3f560,s0)),satisfies_all strncat_linked (strncat_invs s0) strncat_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    assert (START:startof t1 (Addr a,s)=(Addr 0x3f560,s0)).
    { rewrite <- (startof_prefix _ _ _ _ _ SPL). exact ENTRY. }
    eapply models_at_invariant;[exact (proj1 PRE0)|apply strncat_linked_welltyped|exact START|].
    intro MDL. clear - PRE PRE0 MDL. destruct_inv 32 PRE.
    + clear PRE0 MDL. subst s. repeat x86_step. unfold strncat_frame,strncat_m3,strncat_m2,strncat_m1.
      psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption|tauto].
    + clear PRE0 MDL. destruct PRE as [F DI]. unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold strncat_frame,strncat_p. psimpl;elimstore;psimpl.
      rewrite strncat_m3_word by lia. unfold cdecl_arg. repeat split;first[reflexivity|assumption|tauto].
    + clear PRE0 MDL. destruct PRE as (F & SI & DI). unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold strncat_frame,strncat_m4. psimpl;elimstore;psimpl. repeat split;first[reflexivity|assumption|tauto].
    + clear PRE0 MDL. destruct PRE as (F & BX & SI & DI). unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold strncat_frame,strncat_m5,strncat_got. psimpl;elimstore;psimpl.
      rewrite strncat_m4_word by lia. unfold strncat_q,binary_arg2. repeat split;first[reflexivity|assumption|tauto].
    + clear MDL. destruct PRE as (F & BX & SI & DI). ISA_invseek. apply strncat_strlen_call;[exact PRE0| | | |].
      * unfold strncat_frame in *. destruct F as (MEM & SP & BP & RD & WR).
        unfold strncat_m6. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption|tauto].
      * psimpl;exact BX.
      * psimpl;exact SI.
      * psimpl;exact DI.
    + clear MDL. destruct PRE as (F & BX & SI & DI & FIRST). unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      pose proof (getmem_bound 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP)) as QBOUND.
      repeat x86_step. unfold strncat_loop,strncat_frame. psimpl;elimstore;psimpl.
      rewrite strncat_stack_word by lia. exists (s R_EAX),0.
      destruct FIRST as (DB & DP & DZ).
      unfold strncat_memory,copy_bytes. psimpl. unfold strncat_count,ternary_arg3,strncat_q,binary_arg2 in *.
      rewrite N.mod_small by exact QBOUND. repeat split;try reflexivity;try assumption;try tauto;try lia.
      intros i I;lia.
    + clear MDL. destruct PRE as [d [k [LOOP [K [DX NZ]]]]].
      unfold strncat_loop in LOOP. destruct LOOP as (F & SI & DI & AX & CX & FIRST & LE & PREFIX).
      pose proof FIRST as FACTS. destruct FACTS as (DB & DP & DZ).
      unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      pose proof (getmem_bound 32 LittleE 1 (s0 V_MEM32) (strncat_q s0+k)) as BYTEBOUND.
      repeat x86_step. unfold strncat_loop,strncat_frame. psimpl;elimstore;psimpl.
      rewrite ?(N.mod_small _ _ BYTEBOUND). rewrite strncat_memory_step.
      exists d,(k+1). repeat split;try reflexivity;try assumption;try tauto;try lia;try (solve [f_equal;lia]).
      apply prefix_advance1;[exact PREFIX|rewrite getmem_mod_l;exact NZ].
    + clear MDL. destruct PRE as [d [k LOOP]]. unfold strncat_loop in LOOP.
      destruct LOOP as (F & SI & DI & AX & CX & FIRST & K & PREFIX).
      pose proof FIRST as FACTS. destruct FACTS as (DB & DP & DZ).
      unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      pose proof (strncat_count_bound s0) as CBOUND. assert (KBOUND:k<2^32) by lia.
      repeat x86_step.
      all: unfold strncat_loop,strncat_frame;psimpl;elimstore;psimpl.
      * exists d,k. repeat split;try reflexivity;try assumption;try tauto;try lia.
      * exists d,k. split;[repeat split;first[reflexivity|assumption]|].
        apply N.eqb_neq in BC. lia.
    + clear MDL. destruct PRE as [d [k [LOOP K]]].
      pose proof LOOP as OLD. unfold strncat_loop in LOOP.
      destruct LOOP as (F & SI & DI & AX & CX & FIRST & LE & PREFIX).
      pose proof FIRST as FACTS. destruct FACTS as (DB & DP & DZ).
      pose proof (strncat_source_byte s0 d k PRE0 FIRST K PREFIX) as READ.
      unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step.
      all: unfold strncat_write,strncat_loop,strncat_frame;psimpl;elimstore;psimpl;rewrite READ in *.
      * exists d,k. split;[repeat split;first[reflexivity|assumption]|]. right. apply N.eqb_eq in BC. lia.
      * apply N.eqb_neq in BC. exists d,k. split;[repeat split;first[reflexivity|assumption]|]. repeat split;first[assumption|congruence].
    + clear MDL. destruct PRE as [d [k [LOOP STOP]]]. unfold strncat_loop in LOOP.
      destruct LOOP as (F & SI & DI & AX & CX & FIRST & K & PREFIX).
      pose proof FIRST as FACTS. destruct FACTS as (DB & DP & DZ).
      unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      repeat x86_step. unfold strncat_frame,strncat_endmem,copy_terminated. psimpl;elimstore;psimpl.
      exists d,k. split;[repeat split;first[reflexivity|assumption]|]. split;[reflexivity|].
      exact (conj FIRST (conj K (conj PREFIX STOP))).
    + clear MDL. destruct PRE as [d [k [F [AX OUT]]]]. unfold strncat_frame in F. destruct F as (MEM & SP & BP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIBOUND.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIBOUND.
      repeat x86_step. unfold strncat_post,cdecl_leaf_frame,strncat_reference. psimpl;elimstore;psimpl.
      rewrite !strncat_endmem_stack by (first[exact PRE0|exact OUT|lia]).
      rewrite strncat_load_bx,strncat_load_si,strncat_load_di by assumption.
      rewrite N.mod_small by exact SPBOUND. exists d,k. split;[exact OUT|]. split;[repeat split;first[reflexivity|assumption]|exact AX].
Qed.
Theorem strncat_correct:forall prog (EXT:strncat_linked ⊆2 prog) s0 (PRE0:strncat_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x3f560,s0)),satisfies_all prog (strncat_invs s0) strncat_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strncat_invs,strncat_linked,updateall2,updateall,strncat_i386,pc_thunk_bx_i386,strlen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strncat_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strncat_returns:forall prog (EXT:strncat_linked ⊆2 prog) s0 (PRE0:strncat_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x3f5bb,s)=(Addr 0x3f560,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x3f5bb,s)::t)) (UT:unterminated strncat_exit t),
  exists d k,strncat_outcome s0 d k /\ strncat_contents s0 d k (s' V_MEM32) /\
    cdecl_returned (strncat_reference s0 d k) (strncat_p s0) x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strncat_correct prog EXT s0 PRE0 t (Addr 0x3f5bb,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strncat_post s0 s) in INV. destruct INV as [d [k [OUT [FRAME AX]]]].
  assert (RETURN:cdecl_returned (strncat_reference s0 d k) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x3f5bb) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  rewrite AX in RETURN. exists d,k. split;[exact OUT|]. split.
  - rewrite (proj1 (proj2 (proj2 (proj2 RETURN)))). change (strncat_contents s0 d k (strncat_endmem s0 d k)).
    apply strncat_contents_endmem;assumption.
  - split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
    change (x=Addr (getmem 32 LittleE 4 (strncat_endmem s0 d k) (s0 R_ESP))) in ADDRESS.
    rewrite strncat_return_address in ADDRESS by assumption. exact ADDRESS.
Qed.
