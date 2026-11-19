(* strchrnul -- musl i386, optimized non-leaf byte search

   SEMANTICS / SPECIFICATION
   Return the first occurrence of the int argument converted to unsigned char,
   or the first NUL pointer if absent. Verify byte alignment, combined word
   zero/XOR masks, byte tail, and the zero-needle call to strlen.
   Source: local Linux man-pages 6.9.1, /usr/share/man/man3/strchrnul.3.gz
   (paraphrased). No input string length or stop/match witness is assumed.

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x21400; image base 0x10000; global RET 0x31453.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer and int argument: entry ESP+4 and ESP+8, with declared register widths.
   Every four-byte read starting through the first NUL avoids the 48-byte
   nested-call frame. This protects word reads as well as byte reads; no
   pointer alignment, terminator witness or arbitrary length bound is imposed.
   Every int representation is accepted. The exact memory snapshot records
   five effective stack-word writes for nonzero needles and seven for zero;
   the extra argument re-store is proved idempotent. All four saved registers,
   permissions and original return address are restored; RET adds four.
   Partial correctness in every containing program with caller, PIC thunk
   and strlen. Termination and concrete access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_calls i386_strings
  i386_byte_search i386_search_arith i386_binary_call strchrnul_support
  strchrnul_i386 pc_thunk_bx_i386 strlen_i386 strlen_proof.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strchrnul_cursor (s0 s:store):=
  strchrnul_frame s0 (strchrnul_m2 s0) 28 s /\ s R_ECX=strchrnul_char s0 /\ strchrnul_char s0<>0 /\
  exists k,s R_EDX=(cdecl_arg s0+k) mod 2^32 /\ strchrnul_prefix s0 k.
Definition strchrnul_words (s0 s:store):=
  strchrnul_frame s0 (strchrnul_m2 s0) 28 s /\ s R_ECX=strchrnul_char s0 /\ strchrnul_char s0<>0 /\
  s R_EBX=repeated_byte32 (strchrnul_char s0) /\
  exists k,s R_EDX=(cdecl_arg s0+k) mod 2^32 /\ strchrnul_prefix s0 k.
Definition strchrnul_post (s0 s:store):=
  cdecl_leaf_frame (strchrnul_reference s0) s /\ strchrnul_result s0 (s R_EAX).
Definition strchrnul_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_=>match a with
  | 0x31400=>Some (s=s0)
  | 0x31404=>Some (strchrnul_frame s0 (strchrnul_m1 s0) 16 s)
  | 0x31409=>Some (strchrnul_frame s0 (strchrnul_m2 s0) 16 s /\ s R_EBX=0x31409)
  | 0x3141f=>Some (strchrnul_cursor s0 s)
  | 0x31438=>Some (strchrnul_frame s0 (strchrnul_m3 s0) 44 s /\ s R_EDX=cdecl_arg s0 /\ strchrnul_char s0=0)
  | 0x3143c=>Some (strchrnul_frame s0 (strchrnul_m3 s0) 44 s /\ strchrnul_char s0=0)
  | 0x31441=>Some (strchrnul_frame s0 (strchrnul_m4 s0) 44 s /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) (s R_EAX) /\ strchrnul_char s0=0)
  | 0x3144a=>Some (strchrnul_frame s0 (strchrnul_memory s0) 28 s /\ strchrnul_result s0 (s R_EDX))
  | 0x31453=>Some (strchrnul_post s0 s)
  | 0x31454=>Some (strchrnul_cursor s0 s)
  | 0x31480=>Some (strchrnul_words s0 s)
  | 0x314b3=>Some (strchrnul_cursor s0 s)
  | _=>None end | _=>None end.
Definition strchrnul_exit:=at_address 0x31453.

Lemma strchrnul_strlen_supported:forall s0,code_supported strlen_i386 (strlen_invs s0) strlen_exit.
Proof.
  intros s0 [|[[a|i] s] t] NO;try (split;reflexivity).
  unfold strlen_i386 in NO. unfold strlen_invs,strlen_exit,at_address.
  destruct a as [|a];[split;reflexivity|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try discriminate).
Qed.
Lemma strchrnul_strlen_disjoint:forall s0 a s t,strlen_i386 s a<>None ->
  strchrnul_invs s0 ((Addr a,s)::t)=None /\ strchrnul_exit ((Addr a,s)::t)=false.
Proof.
  intros s0 a s t CODE. unfold strlen_i386,strchrnul_invs,strchrnul_exit,at_address in *.
  destruct a as [|a];[contradiction|].
  repeat (destruct a as [a|a|];cbn in *;try (split;reflexivity);try contradiction).
Qed.
Lemma strchrnul_strlen_call:forall s0 sc,strchrnul_pre s0 ->
  strchrnul_frame s0 (strchrnul_m4 s0) 48 sc ->strchrnul_char s0=0 ->forall t,
  nextinv strchrnul_linked (strchrnul_invs s0) strchrnul_exit true ((Addr 0x3f500,sc)::t).
Proof.
  intros s0 sc PRE FRAME ZERO t. unfold nextinv. intro XP0.
  eapply exec_subroutine with (Invs2:=closed_invs strlen_i386 (strlen_invs sc)) (xp2:=strlen_exit).
  - intros tl xs START. eapply satisfies_all_closed_pmono.
    + apply strchrnul_linked_strlen.
    + intros a s h EX NO. exact (proj1 (strchrnul_strlen_supported sc ((Addr a,s)::h) NO)).
    + intros xs' tl' EQ. apply strlen_correct_local. rewrite EQ. exact START.
  - apply may_call_closed.
    + apply strchrnul_linked_strlen.
    + apply strchrnul_strlen_supported.
    + apply strchrnul_strlen_disjoint.
    + intros [[a|i] st] tl;reflexivity.
    + intros [[a|i] st] tl;reflexivity.
  - intros a sr tl START XP UT POST.
    unfold get_postcondition,strlen_exit,at_address in POST.
    destruct (a=?0x3f54c) eqn:EXIT;[|contradiction]. apply N.eqb_eq in EXIT. subst a.
    change (strlen_post sc sr) in POST. destruct POST as [F [n [AX FIRST]]].
    pose proof (strchrnul_first_transport s0 sc n PRE FRAME FIRST) as ORIGINAL.
    eapply NIStep';[reflexivity|reflexivity|]. intros c2 s2 x XS.
    assert (RETURN:cdecl_returned sc (sr R_EAX) (exitof (0x3f54c+1) x) (reset_temps sr s2)).
    { eapply cdecl_ret_step with (p:=strchrnul_linked) (ret:=0x3f54c) (s:=sr).
      - reflexivity.
      - exact (conj eq_refl F).
      - eapply CanStep;[reflexivity|exact XS]. }
    destruct (strchrnul_call_return s0 sc (sr R_EAX) _ _ FRAME RETURN) as (PC & RF & VALUE).
    rewrite PC. apply NIHere'. change (strchrnul_frame s0 (strchrnul_m4 s0) 44 (reset_temps sr s2) /\
      first_nul (s0 V_MEM32) (cdecl_arg s0) ((reset_temps sr s2) R_EAX) /\ strchrnul_char s0=0).
    rewrite VALUE,AX. exact (conj RF (conj ORIGINAL ZERO)).
Qed.

Theorem strchrnul_correct_local:forall s0 (PRE0:strchrnul_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x31400,s0)),
  satisfies_all strchrnul_linked (strchrnul_invs s0) strchrnul_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + clear PRE0. subst s. repeat x86_step.
      unfold strchrnul_frame,strchrnul_m1,save4_registers. psimpl. repeat split;reflexivity.
    + clear PRE0. unfold strchrnul_frame in PRE. destruct PRE as (MEM & SP & RD & WR).
      repeat x86_step. unfold strchrnul_frame,strchrnul_m2. psimpl;elimstore;psimpl.
      repeat split;first[reflexivity|assumption].
    + clear PRE0. destruct PRE as [F BX]. unfold strchrnul_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      all: unfold strchrnul_cursor,strchrnul_frame,strchrnul_m3,strchrnul_got;psimpl;elimstore;psimpl.
      all: rewrite ?strchrnul_m2_char,?strchrnul_m2_stack in * by lia;csimpl.
      * repeat split;first[reflexivity|assumption].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[reflexivity|]. split;[assumption|].
        exists 0. unfold cdecl_arg. psimpl. split;[reflexivity|]. split;intros i I;clear - I;lia.
    + destruct PRE as [F [CX [NONZERO [k [DX PREFIX]]]]].
      pose proof (strchrnul_read_byte s0 false k PRE0 (proj1 PREFIX)) as READ. clear PRE0.
      change (getmem 32 LittleE 1 (strchrnul_m2 s0) (cdecl_arg s0+k)=
        getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)) in READ.
      pose proof (strchrnul_char_bound s0) as CHAR.
      unfold strchrnul_frame in F. destruct F as (MEM & SP & RD & WR). repeat x86_step.
      all: unfold strchrnul_cursor,strchrnul_frame;psimpl;elimstore;psimpl.
      all: rewrite ?READ in *;csimpl.
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
        split;[exact NONZERO|]. exists k. split;[first[reflexivity|exact DX]|exact PREFIX].
      * unfold strchrnul_memory,strchrnul_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. apply strchrnul_found;[exact PREFIX|left;assumption].
      * unfold strchrnul_memory,strchrnul_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. apply strchrnul_found;[exact PREFIX|right;assumption].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
        split;[exact NONZERO|]. exists (k+1). split.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- apply strchrnul_prefix_step1;assumption.
    + clear PRE0. destruct PRE as [F [DX ZERO]]. unfold strchrnul_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold strchrnul_frame. psimpl;elimstore;psimpl. rewrite strchrnul_resave_arg.
      repeat split;first[reflexivity|assumption].
    + destruct PRE as [F ZERO]. ISA_invseek. apply strchrnul_strlen_call;[exact PRE0| |exact ZERO].
      unfold strchrnul_frame in *. destruct F as (MEM & SP & RD & WR).
      unfold strchrnul_m4. psimpl;elimstore;psimpl. rewrite MEM,SP. psimpl. repeat split;first[reflexivity|assumption].
    + clear PRE0. destruct PRE as [F [FIRST ZERO]]. unfold strchrnul_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold strchrnul_frame,strchrnul_memory,strchrnul_snapshot. psimpl;elimstore;psimpl.
      pose proof (strchrnul_snapshot_stack s0 true 4 ltac:(lia)) as STACK.
      change (getmem 32 LittleE 4 (strchrnul_m4 s0) (4+s0 R_ESP)=
        getmem 32 LittleE 4 (s0 V_MEM32) (4+s0 R_ESP)) in STACK.
      rewrite STACK. rewrite ZERO. cbn [N.eqb].
      split;[repeat split;first[reflexivity|assumption]|]. fold (cdecl_arg s0).
      apply strchrnul_zero_result;assumption.
    + destruct PRE as [F RESULT]. unfold strchrnul_frame in F. destruct F as (MEM & SP & RD & WR).
      pose proof ((proj1 PRE0) R_ESP 32 eq_refl) as SPBOUND.
      pose proof ((proj1 PRE0) R_EBX 32 eq_refl) as BXBOUND.
      pose proof ((proj1 PRE0) R_ESI 32 eq_refl) as SIBOUND.
      pose proof ((proj1 PRE0) R_EDI 32 eq_refl) as DIBOUND.
      pose proof ((proj1 PRE0) R_EBP 32 eq_refl) as BPBOUND. clear PRE0.
      repeat x86_step. unfold strchrnul_post,cdecl_leaf_frame,strchrnul_reference. psimpl;elimstore;psimpl.
      rewrite (N.mod_small _ _ SPBOUND),(strchrnul_saved_bx s0 BXBOUND),(strchrnul_saved_si s0 SIBOUND),
        (strchrnul_saved_di s0 DIBOUND),(strchrnul_saved_bp s0 BPBOUND).
      split;[repeat split;first[reflexivity|assumption]|exact RESULT].
    + clear PRE0. destruct PRE as [F [CX [NONZERO [k [DX PREFIX]]]]].
      pose proof (strchrnul_char_bound s0) as CHAR. unfold strchrnul_frame in F.
      destruct F as (MEM & SP & RD & WR). repeat x86_step.
      unfold strchrnul_words,strchrnul_frame. psimpl;elimstore;psimpl.
      split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
      split;[exact NONZERO|]. split;[apply search_repeated_signed_product;exact CHAR|]. exists k. split;[first[reflexivity|assumption]|exact PREFIX].
    + destruct PRE as (F & CX & NONZERO & BX & k & DX & PREFIX).
      pose proof (strchrnul_read_word s0 false k PRE0 (proj1 PREFIX)) as READ. clear PRE0.
      change (getmem 32 LittleE 4 (strchrnul_m2 s0) (cdecl_arg s0+k)=
        getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k)) in READ.
      pose proof (strchrnul_char_bound s0) as CHAR.
      unfold strchrnul_frame in F. destruct F as (MEM & SP & RD & WR). repeat x86_step.
      all: unfold strchrnul_words,strchrnul_cursor,strchrnul_frame;psimpl;elimstore;psimpl.
      all: rewrite READ in *;csimpl.
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
        split;[exact NONZERO|]. split;[first[reflexivity|assumption]|]. exists (k+4). split.
        -- replace (4+cdecl_arg s0+k) with (cdecl_arg s0+(k+4))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- apply strchrnul_prefix_step4;[exact PREFIX| |];apply strchrnul_mask_parts in BC;tauto.
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
        split;[exact NONZERO|]. exists k. split;[first[reflexivity|assumption]|exact PREFIX].
    + destruct PRE as [F [CX [NONZERO [k [DX PREFIX]]]]].
      pose proof (strchrnul_read_byte s0 false k PRE0 (proj1 PREFIX)) as READ. clear PRE0.
      change (getmem 32 LittleE 1 (strchrnul_m2 s0) (cdecl_arg s0+k)=
        getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)) in READ.
      pose proof (strchrnul_char_bound s0) as CHAR.
      unfold strchrnul_frame in F. destruct F as (MEM & SP & RD & WR). repeat x86_step.
      all: unfold strchrnul_cursor,strchrnul_frame;psimpl;elimstore;psimpl;rewrite READ in *;csimpl.
      * unfold strchrnul_memory,strchrnul_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. apply strchrnul_found;[exact PREFIX|left;assumption].
      * unfold strchrnul_memory,strchrnul_snapshot. rewrite (proj2 (N.eqb_neq _ _) NONZERO).
        split;[repeat split;first[reflexivity|assumption]|]. apply strchrnul_found;[exact PREFIX|right;assumption].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|assumption]|].
        split;[exact NONZERO|]. exists (k+1). split.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- apply strchrnul_prefix_step1;assumption.
Qed.

Theorem strchrnul_correct:forall prog (EXT:strchrnul_linked ⊆2 prog) s0 (PRE0:strchrnul_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x31400,s0)),
  satisfies_all prog (strchrnul_invs s0) strchrnul_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold strchrnul_invs,strchrnul_linked,updateall2,updateall,
      strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply strchrnul_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.
Theorem strchrnul_returns:forall prog (EXT:strchrnul_linked ⊆2 prog) s0 (PRE0:strchrnul_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x31453,s)=(Addr 0x31400,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x31453,s)::t)) (UT:unterminated strchrnul_exit t),
  exists value,strchrnul_result s0 value /\ cdecl_returned (strchrnul_reference s0) value x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strchrnul_correct prog EXT s0 PRE0 t (Addr 0x31453,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strchrnul_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN:cdecl_returned (strchrnul_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x31453) (s:=s).
    - apply EXT. reflexivity.
    - exact (conj eq_refl FRAME).
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (strchrnul_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (strchrnul_snapshot_stack s0 (strchrnul_char s0=?0) 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. unfold strchrnul_memory in ADDRESS. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
