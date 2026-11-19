(* llabs -- musl i386, two-word absolute value

   SEMANTICS
   ---------
   Save EBX, derive a sign mask from the high word, complement both words for
   negative inputs, and subtract the mask with a borrow into the high word.
   Restore EBX and return the 64-bit representation in EDX:EAX.

   SPECIFICATION (abs(3), Linux man-pages 6.9.1, 2024-05-02)
   -----------------------------------------------------
     #include <stdlib.h>
     long long llabs(long long j);
   Return the absolute value when it is representable as long long.
   Source: /usr/share/man/man3/abs.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: llabs, ELF VA 0x65291; global entry 0x75291, RET 0x752aa.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  Low and high argument words at entry ESP+4 and ESP+8. Architectural
           registers have their declared widths.
   Output: EDX:EAX is the input representation if its sign bit is clear, or its
           64-bit two's-complement negation otherwise. Only the EBX save slot
           below ESP changes. Callee-saved registers and access permissions
           are restored; RET pops the original address and advances ESP by 4.
   Scope:  Partial correctness for every 64-bit representation. INT64_MIN
           returns the same bit pattern; the C mathematical contract excludes
           that unrepresentable magnitude. No caller-supplied sign witness.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits i386_stack i386_abs64 llabs_i386.
From Stdlib Require Import NArith ZArith Lia.
Import X86Notations.
Open Scope N.
Definition llabs_high (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition llabs_prepop (s0 s:store) := ebx_save_frame s0 s /\
  s R_EAX=abs64_low (cdecl_arg s0) (llabs_high s0) /\
  s R_EDX=abs64_high (cdecl_arg s0) (llabs_high s0).
Definition llabs_post (s0 s:store) :=
  cdecl_leaf_post (save_ebx_reference s0) (abs64_low (cdecl_arg s0) (llabs_high s0)) s /\
  s R_EDX=abs64_high (cdecl_arg s0) (llabs_high s0).
Definition llabs_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x75291 => Some (s=s0)
  | 0x75292 => Some (ebx_save_frame s0 s)
  | 0x752a9 => Some (llabs_prepop s0 s)
  | 0x752aa => Some (llabs_post s0 s)
  | _ => None end | _ => None end.
Definition llabs_exit := at_address 0x752aa.
Theorem llabs_nwc : forall s1 s2,llabs_i386 s1=llabs_i386 s2.
Proof. reflexivity. Qed.
Theorem llabs_correct_local : forall s0 (MDL:models x86typctx s0) t xs
  (ENTRY:startof t xs=(Addr 0x75291,s0)),
  satisfies_all llabs_i386 (llabs_invs s0) llabs_exit (xs::t).
Proof.
  intros s0 MDL t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL. destruct_inv 32 PRE.
    + subst s. repeat x86_step. unfold ebx_save_frame,save_ebx_memory. psimpl.
      repeat split; reflexivity.
    + unfold ebx_save_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold llabs_prepop,ebx_save_frame. psimpl.
      rewrite ?MEM, ?SP, ?SI, ?DI, ?BP, ?RD, ?WR. psimpl.
      rewrite ?(save_ebx_stack_word s0 4 ltac:(lia)), ?(save_ebx_stack_word s0 8 ltac:(lia)).
      fold (cdecl_arg s0) (llabs_high s0).
      split; [repeat split; reflexivity|].
      assert (L:cdecl_arg s0<2^32) by (unfold cdecl_arg; apply getmem_bound).
      assert (H:llabs_high s0<2^32) by (unfold llabs_high; apply getmem_bound).
      replace (N.land 31 31) with 31 by reflexivity.
      rewrite (ashiftr31_mask _ H). exact (abs64_branchless _ _ L H).
    + destruct PRE as (FRAME & AX & DX). unfold ebx_save_frame in FRAME.
      destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR). repeat x86_step.
      unfold llabs_post,cdecl_leaf_post,cdecl_leaf_frame,save_ebx_reference. psimpl.
      rewrite ?MEM, ?SP, ?AX, ?DX, ?SI, ?DI, ?BP, ?RD, ?WR. psimpl.
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      rewrite ?(N.mod_small _ _ SPBOUND), (saved_ebx_load s0 BXBOUND).
      repeat split; reflexivity.
Qed.

Theorem llabs_spec_signed : forall s0,
  cdecl_arg s0+4294967296*llabs_high s0<>2^63 ->
  toZ 64 (abs64_value (cdecl_arg s0) (llabs_high s0)) =
  Z.abs (toZ 64 (cdecl_arg s0+4294967296*llabs_high s0)).
Proof.
  intros s0 MIN. apply abs64_value_signed;
    [unfold cdecl_arg; apply getmem_bound|unfold llabs_high; apply getmem_bound|exact MIN].
Qed.
Theorem llabs_correct : forall prog (EXT:llabs_i386 ⊆2 prog) s0
  (MDL:models x86typctx s0) t xs (ENTRY:startof t xs=(Addr 0x75291,s0)),
  satisfies_all prog (llabs_invs s0) llabs_exit (xs::t).
Proof.
  intros prog EXT s0 MDL t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold llabs_invs,llabs_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply llabs_correct_local; [exact MDL|]. rewrite START. exact ENTRY.
Qed.
Theorem llabs_returns : forall prog (EXT:llabs_i386 ⊆2 prog) s0
  (MDL:models x86typctx s0) t s x s'
  (ENTRY:startof t (Addr 0x752aa,s)=(Addr 0x75291,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x752aa,s)::t)) (UT:unterminated llabs_exit t),
  cdecl_returned (save_ebx_reference s0) (abs64_low (cdecl_arg s0) (llabs_high s0)) x s' /\
  s' R_EDX=abs64_high (cdecl_arg s0) (llabs_high s0) /\
  s' R_EAX+4294967296*s' R_EDX=abs64_value (cdecl_arg s0) (llabs_high s0) /\
  x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL t s x s' ENTRY XP UT.
  pose proof (llabs_correct prog EXT s0 MDL t (Addr 0x752aa,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (llabs_post s0 s) in INV. destruct INV as [POST HIGH].
  assert (LOOK:prog s 0x752aa=Some (1,i386_ret)) by (apply EXT; reflexivity).
  pose proof (exec_prog_final _ _ _ _ XP) as STEP.
  pose proof (cdecl_ret_step prog 0x752aa _ _ s x s' LOOK POST STEP) as RETURN.
  pose proof (cdecl_ret_preserves_edx prog 0x752aa s x s' LOOK STEP) as DX.
  rewrite HIGH in DX. split; [exact RETURN|]. split; [exact DX|]. split.
  - rewrite (proj1 (proj2 RETURN)), DX. apply abs64_pair_value;
      [unfold cdecl_arg; apply getmem_bound|unfold llabs_high; apply getmem_bound].
  - pose proof (proj1 RETURN) as ADDRESS.
    change (x=Addr (getmem 32 LittleE 4 (save_ebx_memory s0) (s0 R_ESP))) in ADDRESS.
    pose proof (save_ebx_stack_word s0 0 ltac:(lia)) as STACK.
    rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
