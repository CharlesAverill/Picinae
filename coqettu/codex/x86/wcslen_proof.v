(* wcslen -- musl i386, unbounded wide-character scan

   SEMANTICS / SPECIFICATION
   Scan four-byte wchar_t values to the first zero and return their count.
   Source: /usr/share/man/man3/wcslen.3.gz, Linux man-pages 6.9.1
   (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x37c10; Ghidra image base 0x10000; global RET 0x47c2e.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Input pointer: entry stack word ESP+4. No length/terminator witness is
   assumed. The result identifies the first zero in the four-byte address
   orbit (period 2^30). The binary computes SAR32(4*k,2); this equals k for
   k<2^29, where the signed pointer difference is representable. The exact
   machine result is specified for longer scans too, without a caller bound.
   Memory, saved registers and access permissions are unchanged; RET pops
   the original return address and adds four to entry ESP.
   Scope: partial correctness in every containing program. Addresses wrap
   modulo 2^32; termination and concrete access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_wstrlen wcslen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcslen_result (s0:store) (result:N) := exists k,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) k /\ result=wide_length32 k.
Definition wcslen_cursor (s0 s:store) := cdecl_leaf_frame s0 s /\ exists k,
  s R_EDX=cdecl_arg s0 /\ s R_EAX=(cdecl_arg s0+4*k) mod 2^32 /\
  wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k.
Definition wcslen_post (s0 s:store) := cdecl_leaf_frame s0 s /\ wcslen_result s0 (s R_EAX).
Definition wcslen_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x47c10=>Some (s=s0)
  | 0x47c23=>Some (wcslen_cursor s0 s)
  | 0x47c2e=>Some (wcslen_post s0 s)
  | _=>None end | _=>None end.
Definition wcslen_exit := at_address 0x47c2e.

Theorem wcslen_correct_local : forall s0 t xs (ENTRY:startof t xs=(Addr 0x47c10,s0)),
  satisfies_all wcslen_i386 (wcslen_invs s0) wcslen_exit (xs::t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step. unfold wcslen_cursor,cdecl_leaf_frame. psimpl.
      split;[repeat split;reflexivity|]. exists 0. unfold cdecl_arg. psimpl.
      repeat split;try reflexivity. intros i I. clear - I;lia.
    + destruct PRE as [FRAME [k [DX [AX PREFIX]]]]. unfold cdecl_leaf_frame in FRAME.
      destruct FRAME as (MEM & SP & BX & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold wcslen_cursor,wcslen_post,cdecl_leaf_frame;psimpl;elimstore;psimpl.
      all: split;[repeat split;first[reflexivity|assumption]|].
      all: csimpl.
      * exists (k mod 2^30). split.
        -- apply wide_prefix_stop;[exact PREFIX|rewrite getmem_mod_l;assumption].
        -- rewrite wide_length32_reduce. unfold wide_length32. reflexivity.
      * exists (k+1). repeat split;try reflexivity;try assumption.
        -- replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- apply wide_prefix_advance;[exact PREFIX|rewrite getmem_mod_l;assumption].
Qed.

Theorem wcslen_correct : forall prog (EXT:wcslen_i386 ⊆2 prog) s0 t xs
  (ENTRY:startof t xs=(Addr 0x47c10,s0)),
  satisfies_all prog (wcslen_invs s0) wcslen_exit (xs::t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold wcslen_invs,wcslen_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply wcslen_correct_local. rewrite START. exact ENTRY.
Qed.

Theorem wcslen_returns : forall prog (EXT:wcslen_i386 ⊆2 prog) s0 t s x s'
  (ENTRY:startof t (Addr 0x47c2e,s)=(Addr 0x47c10,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x47c2e,s)::t)) (UT:unterminated wcslen_exit t),
  exists result,wcslen_result s0 result /\ cdecl_returned s0 result x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  pose proof (wcslen_correct prog EXT s0 t (Addr 0x47c2e,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcslen_post s0 s) in INV. destruct INV as [FRAME RESULT].
  exists (s R_EAX). split;[exact RESULT|].
  eapply cdecl_ret_step with (p:=prog) (ret:=0x47c2e) (s:=s).
  - apply EXT. reflexivity.
  - split;[reflexivity|exact FRAME].
  - exact (exec_prog_final _ _ _ _ XP).
Qed.

Corollary wcslen_result_small : forall s0 result k,
  wcslen_result s0 result -> wide_first_nul (s0 V_MEM32) (cdecl_arg s0) k ->
  k<2^29 -> result=k.
Proof.
  intros s0 result k [j [FIRST VALUE]] EXPECT K.
  pose proof (wide_first_nul_unique _ _ _ _ FIRST EXPECT) as EQ. subst j.
  rewrite VALUE. apply wide_length32_small;exact K.
Qed.
