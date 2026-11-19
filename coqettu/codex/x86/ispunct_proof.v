(* ispunct -- musl i386, non-leaf ASCII punctuation classifier

   SEMANTICS / SPECIFICATION
   Return exactly one for a graphical ASCII character that is neither a letter
   nor a decimal digit, and zero otherwise. Predicate source: local Linux
   man-pages 6.9.1, /usr/share/man/man3/isalpha.3.gz (paraphrased).
   The conditional CALL to isalnum is proved using its existing contract.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x3effc; Ghidra image base 0x10000; global RET 0x4f01d.
   Ghidra 12.0 PUBLIC, frozen strict global typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   The character word is at entry ESP+4. Registers have declared widths; every
   character bit pattern is accepted. EAX is the zero/one result. Exact memory
   includes two stack-word writes outside the graphical range and four inside.
   Callee-saved registers, permissions and original return address are restored;
   RET adds four to ESP. Contracts hold in every containing program with caller,
   PIC thunk and isalnum code. Partial correctness only: termination and concrete
   memory-access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_ascii i386_bits i386_common i386_stack i386_deep_stack i386_calls i386_unary_call
  ispunct_support ispunct_i386 pc_thunk_bx_i386 isalnum_i386 isalnum_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ispunct_spec (c:N):N:=
  if ispunct_graph c && negb (ascii_alpha c || ascii_digit c) then 1 else 0.
Lemma ispunct_graph_test:forall c,c<2^32 ->
  N.lor (if msub 32 c 33 <? 93 then 1 else 0) (if c=?126 then 1 else 0)=
  if ispunct_graph c then 1 else 0.
Proof. intros. apply (classify_interval c 33 126);lia. Qed.
Lemma ispunct_nongraph:forall c,ispunct_graph c=false ->ispunct_spec c=0.
Proof. intros c G. unfold ispunct_spec. rewrite G. reflexivity. Qed.
Lemma ispunct_graph_result:forall c,ispunct_graph c=true ->
  (if isalnum_spec c=?0 then 1 else 0)=ispunct_spec c.
Proof.
  intros c G. unfold ispunct_spec,isalnum_spec. rewrite G.
  destruct (ascii_alpha c || ascii_digit c);reflexivity.
Qed.
Definition ispunct_post (s0 s:store):=
  cdecl_leaf_post (ispunct_reference s0) (ispunct_spec (cdecl_arg s0)) s.
Definition ispunct_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ => match a with
  | 0x4effc=>Some (s=s0)
  | 0x4efff=>Some (ispunct_frame s0 (ispunct_m1 s0) 4 s /\ s R_EAX=0)
  | 0x4f004=>Some (ispunct_frame s0 (ispunct_m2 s0) 4 s /\ s R_EBX=0x4f004 /\ s R_EAX=0)
  | 0x4f022=>Some (ispunct_frame s0 (ispunct_m3 s0) 28 s /\ s R_EBX=ispunct_got /\
      ispunct_graph (cdecl_arg s0)=true)
  | 0x4f027=>Some (ispunct_frame s0 (ispunct_m4 s0) 28 s /\ s R_EBX=ispunct_got /\
      s R_EAX=isalnum_spec (cdecl_arg s0) /\ ispunct_graph (cdecl_arg s0)=true)
  | 0x4f019=>Some (ispunct_frame s0 (ispunct_memory s0) 12 s /\ s R_EAX=ispunct_spec (cdecl_arg s0))
  | 0x4f01d=>Some (ispunct_post s0 s)
  | _=>None end | _=>None end.
Definition ispunct_exit:=at_address 0x4f01d.

Lemma isalnum_code_supported:forall s0,code_supported isalnum_i386 (isalnum_invs s0) isalnum_exit.
Proof. intro s0. apply unary_leaf_supported;intros;discriminate. Qed.
Lemma ispunct_isalnum_disjoint:forall s0 a s t,isalnum_i386 s a<>None ->
  ispunct_invs s0 ((Addr a,s)::t)=None /\ ispunct_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold isalnum_i386,ispunct_invs,ispunct_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma ispunct_call_return:forall s0 sc x se,
  ispunct_frame s0 (ispunct_m4 s0) 32 sc ->sc R_EBX=ispunct_got ->
  cdecl_returned sc (isalnum_spec (cdecl_arg sc)) x se ->
  x=Addr 0x4f027 /\ ispunct_frame s0 (ispunct_m4 s0) 28 se /\
  se R_EBX=ispunct_got /\ se R_EAX=isalnum_spec (cdecl_arg s0).
Proof. intros. exact (unary_call_return s0 0x4f004 0x4f027 ispunct_got isalnum_spec sc x se H H0 H1). Qed.
Lemma ispunct_isalnum_call:forall s0 sc,
  ispunct_frame s0 (ispunct_m4 s0) 32 sc ->sc R_EBX=ispunct_got ->
  ispunct_graph (cdecl_arg s0)=true ->forall t,
  nextinv ispunct_linked (ispunct_invs s0) ispunct_exit true ((Addr 0x4ee61,sc)::t).
Proof.
  intros s0 sc FRAME BX GRAPH t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs isalnum_i386 (isalnum_invs sc)) (xp2:=isalnum_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply ispunct_linked_isalnum.
    + intros a s h EX NO. exact (proj1 (isalnum_code_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply isalnum_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply ispunct_linked_isalnum.
    + apply isalnum_code_supported.
    + apply ispunct_isalnum_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,isalnum_exit,at_address in POST.
    destruct (a=?0x4ee84) eqn:EXIT;[|contradiction].
    apply N.eqb_eq in EXIT. subst a.
    change (cdecl_leaf_post sc (isalnum_spec (cdecl_arg sc)) sr) in POST.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (isalnum_spec (cdecl_arg sc))
      (exitof (0x4ee84+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=ispunct_linked) (ret:=0x4ee84) (s:=sr).
      - reflexivity.
      - exact POST.
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (ispunct_call_return s0 sc _ _ FRAME BX RETURN) as (PC & F & B & R).
    rewrite PC. apply NIHere'. change (ispunct_frame s0 (ispunct_m4 s0) 28 (reset_temps sr s2) /\
      (reset_temps sr s2) R_EBX=ispunct_got /\ (reset_temps sr s2) R_EAX=isalnum_spec (cdecl_arg s0) /\ ispunct_graph (cdecl_arg s0)=true).
    exact (conj F (conj B (conj R GRAPH))).
Qed.

Theorem ispunct_correct_local:forall s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4effc,s0)),
  satisfies_all ispunct_linked (ispunct_invs s0) ispunct_exit (xs::t).
Proof.
  intros s0 MDL0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL0.
    destruct_inv 32 PRE.
    + clear MDL0. subst s. repeat x86_step.
      unfold ispunct_frame,unary_frame,ispunct_m1,unary_m1,save_ebx_memory. psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F AX]. unfold ispunct_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold ispunct_frame,unary_frame,ispunct_m2,unary_m2,ispunct_m1,unary_m1. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F [BX AX]]. unfold ispunct_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold ispunct_frame,unary_frame,ispunct_m3,unary_m3,ispunct_got;psimpl;elimstore;psimpl.
      all: rewrite ispunct_m2_stack in * by lia.
      all: fold (cdecl_arg s0) in *.
      all: rewrite (ispunct_graph_test (cdecl_arg s0) ltac:(unfold cdecl_arg;apply getmem_bound)) in BC.
      all: destruct (ispunct_graph (cdecl_arg s0)) eqn:GRAPH;cbn in BC;try discriminate.
      * unfold ispunct_memory. rewrite GRAPH. repeat split;first[reflexivity|assumption|rewrite AX;symmetry;apply ispunct_nongraph;exact GRAPH].
      * repeat split;first[reflexivity|assumption].
    + destruct PRE as [F AX]. unfold ispunct_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      pose proof (MDL0 R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL0 R_EBX 32 eq_refl) as BXBOUND. clear MDL0.
      repeat x86_step. unfold ispunct_post,cdecl_leaf_post,cdecl_leaf_frame,ispunct_reference.
      psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(ispunct_saved_bx s0 BXBOUND).
      repeat split;first[reflexivity|assumption].
    + clear MDL0. destruct PRE as [F [BX GRAPH]]. ISA_invseek. apply ispunct_isalnum_call.
      * unfold ispunct_frame,unary_frame in *. destruct F as (MEM & SP & SI & DI & BP & RD & WR).
        unfold ispunct_m4,unary_memory. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption].
      * psimpl. exact BX.
      * exact GRAPH.
    + clear MDL0. destruct PRE as [F [BX [AX GRAPH]]]. unfold ispunct_frame,unary_frame in F.
      destruct F as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold ispunct_frame,unary_frame,ispunct_memory. psimpl;elimstore;psimpl.
      rewrite GRAPH. repeat split;try reflexivity;try assumption.
      apply ispunct_graph_result;exact GRAPH.
Qed.

Theorem ispunct_correct:forall prog (EXT:ispunct_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x4effc,s0)),
  satisfies_all prog (ispunct_invs s0) ispunct_exit (xs::t).
Proof.
  intros prog EXT s0 MDL0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold ispunct_invs,ispunct_linked,updateall2,updateall,
      ispunct_i386,pc_thunk_bx_i386,isalnum_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply ispunct_correct_local;[exact MDL0|]. rewrite START. exact ENTRY.
Qed.

Theorem ispunct_returns:forall prog (EXT:ispunct_linked ⊆2 prog) s0 (MDL0:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x4f01d,s)=(Addr 0x4effc,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x4f01d,s)::t)) (UT:unterminated ispunct_exit t),
  cdecl_returned (ispunct_reference s0) (ispunct_spec (cdecl_arg s0)) x s' /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL0 t s x s' ENTRY XP UT.
  pose proof (ispunct_correct prog EXT s0 MDL0 t (Addr 0x4f01d,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (ispunct_post s0 s) in INV.
  assert (RETURN:cdecl_returned (ispunct_reference s0) (ispunct_spec (cdecl_arg s0)) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x4f01d) (s:=s).
    - apply EXT. reflexivity.
    - exact INV.
    - exact (exec_prog_final _ _ _ _ XP). }
  split;[exact RETURN|]. pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (ispunct_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (ispunct_outer_stack s0 0 ltac:(lia)) as STACK. rewrite N.add_0_l in STACK.
  rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
