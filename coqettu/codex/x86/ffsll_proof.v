(* ffsll -- musl i386, two 32-bit BSF scans

   SEMANTICS
   ---------
   Return zero for an all-zero long long representation. Search its low word
   first; if that word is zero, search the high word and add 32. Number the
   resulting bit position from one. Save and restore EBX on the stack.

   SPECIFICATION (ffs(3), Linux man-pages 6.9.1, 2024-05-02)
   -----------------------------------------------------
     #include <strings.h>
     int ffsll(long long i);
   Return the first set-bit position, starting at one, or zero for input zero.
   Source: /usr/share/man/man3/ffs.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: ffsll, ELF VA 0x53bb4; Ghidra image base 0x10000,
           global entry 0x63bb4, RET 0x63bd4.
   Lifter: Ghidra 12.0 PUBLIC + Codex-local pcode2coq_codex.py and the pinned
           lifter snapshot in ../lifter_base. Strict global lift; exact BSF32
           p-code graphs use 32 guarded iterations, checked in i386_bsf.v.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The 64-bit representation occupies entry ESP+4 through ESP+11,
           low word first. Architectural values have their declared widths.
   Output: EAX is zero, or one plus the first set-bit index below 64.
           EBX, ESI, EDI, EBP and access permissions are restored/preserved.
           Memory changes only by saving entry EBX in the word below ESP.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness for all 64-bit inputs; no bit-index witness.
           On a zero low word, its BSF destination is ignored before the
           high-word scan. No property depends on that undefined CPU value.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_stack i386_bsf ffsll_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ffsll_high (s0 : store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition ffsll_arg (s0 : store) := getmem 32 LittleE 8 (s0 V_MEM32) (4+s0 R_ESP).

Lemma ffsll_arg_split : forall s0,
  ffsll_arg s0 = N.lor (N.shiftl (ffsll_high s0) 32) (cdecl_arg s0).
Proof.
  intros s0. unfold ffsll_arg, ffsll_high, cdecl_arg.
  change (getmem 32 LittleE (4+4) (s0 V_MEM32) (4+s0 R_ESP) =
    N.lor (N.shiftl (getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP)) 32)
      (getmem 32 LittleE 4 (s0 V_MEM32) (4+s0 R_ESP))).
  rewrite getmem_split. cbn [cbits].
  replace (4+s0 R_ESP+4) with (8+s0 R_ESP)
    by (set (sp := s0 R_ESP); clearbody sp; clear - sp; lia).
  reflexivity.
Qed.

Definition ffsll_ready_low (s0 s : store) :=
  ebx_save_frame s0 s /\ s R_EBX=cdecl_arg s0 /\ s R_ECX=ffsll_high s0 /\
    N.lor (cdecl_arg s0) (ffsll_high s0)<>0.
Definition ffsll_ready_high (s0 s : store) :=
  ebx_save_frame s0 s /\ cdecl_arg s0=0 /\ s R_ECX=ffsll_high s0 /\ ffsll_high s0<>0.
Definition ffsll_preinc (s0 s : store) :=
  ebx_save_frame s0 s /\ exists k, first_set64 (ffsll_arg s0) k /\ s R_EDX=k.
Definition ffsll_join (s0 s : store) :=
  ebx_save_frame s0 s /\ ffs_result64 (ffsll_arg s0) (s R_EDX).
Definition ffsll_post (s0 s : store) :=
  cdecl_leaf_frame (save_ebx_reference s0) s /\ ffs_result64 (ffsll_arg s0) (s R_EAX).

Definition ffsll_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x63bb4 => Some (s=s0 /\ models x86typctx s0)
  | 0x63bb5 => Some (ebx_save_frame s0 s)
  | 0x63bc3 => Some (ffsll_ready_low s0 s)
  | 0x63bc8 => Some (ffsll_ready_high s0 s)
  | 0x63bce => Some (ffsll_preinc s0 s)
  | 0x63bd1 => Some (ffsll_join s0 s)
  | 0x63bd4 => Some (ffsll_post s0 s)
  | _ => None end | _ => None end.
Definition ffsll_exit := at_address 0x63bd4.

Theorem ffsll_nwc : forall s1 s2, ffsll_i386 s1=ffsll_i386 s2.
Proof. reflexivity. Qed.

Theorem ffsll_correct_local :
  forall s0 (MDL : models x86typctx s0) t xs
    (ENTRY : startof t xs=(Addr 0x63bb4,s0)),
  satisfies_all ffsll_i386 (ffsll_invs s0) ffsll_exit (xs::t).
Proof.
  intros s0 MDL t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. split; [reflexivity|exact MDL].
  - intros t1 a s t2 UT SPL PRE. clear - PRE MDL.
    destruct_inv 32 PRE.
    + destruct PRE as [EQ _]. subst s. repeat x86_step.
      unfold ebx_save_frame, save_ebx_memory. psimpl. repeat split; reflexivity.
    + unfold ebx_save_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      all: unfold ffsll_ready_low, ffsll_join, ebx_save_frame; psimpl.
      all: rewrite ?MEM, ?SP in *; psimpl.
      all: rewrite (save_ebx_stack_word s0 4 ltac:(lia)) in BC.
      all: rewrite (save_ebx_stack_word s0 8 ltac:(lia)) in BC.
      all: rewrite ?(save_ebx_stack_word s0 4 ltac:(lia)),
        ?(save_ebx_stack_word s0 8 ltac:(lia)).
      all: fold (cdecl_arg s0) (ffsll_high s0) in *.
      all: elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: csimpl.
      * left. split; [|reflexivity].
        match goal with ZERO : N.lor (cdecl_arg s0) (ffsll_high s0)=0 |- _ =>
          apply N.lor_eq_0_iff in ZERO; destruct ZERO as [LO HI]
        end.
        rewrite ffsll_arg_split, LO, HI. reflexivity.
      * repeat split; first [reflexivity|assumption].
    + destruct PRE as (FRAME & BX & CX & NONZERO).
      eapply NIStep; [reflexivity|reflexivity|]. intros c1 s1 x XS.
      change (exec_stmt x86typctx s (bsf32_stmt R_EBX R_EDX) c1 s1 x) in XS.
      assert (B : s R_EBX < 2^32) by (rewrite BX; unfold cdecl_arg; apply getmem_bound).
      destruct (bsf32_machine_effect R_EBX R_EDX s c1 s1 x eq_refl eq_refl B XS)
        as (NO & k & SPEC & STATE).
      subst x. rewrite BX in SPEC, STATE.
      destruct SPEC as [[ZERO K]|FIRST].
      * subst k. assert (HI : ffsll_high s0<>0).
        { rewrite ZERO, N.lor_0_l in NONZERO. exact NONZERO. }
        rewrite ZERO in STATE. rewrite STATE. repeat x86_step.
        all: try (cbn in BC; discriminate).
        all: unfold ffsll_ready_high, ebx_save_frame in *; psimpl; elimstore; psimpl; csimpl.
        split; [exact FRAME|].
        repeat split; first [exact ZERO|exact HI|exact CX|reflexivity].
      * assert (LO : cdecl_arg s0<>0) by (exact (first_set_nonzero 32 _ _ FIRST)).
        rewrite (proj2 (N.eqb_neq _ _) LO) in STATE. rewrite STATE. repeat x86_step.
        all: try (cbn in BC; discriminate).
        all: unfold ffsll_preinc, ebx_save_frame in *; psimpl; elimstore; psimpl; csimpl.
        split; [exact FRAME|]. exists k. split.
        -- rewrite ffsll_arg_split. apply first_set64_low. exact FIRST.
        -- reflexivity.
    + destruct PRE as (FRAME & ZERO & CX & NONZERO).
      eapply NIStep; [reflexivity|reflexivity|]. intros c1 s1 x XS.
      change (exec_stmt x86typctx s (bsf32_stmt R_ECX R_EDX) c1 s1 x) in XS.
      assert (B : s R_ECX < 2^32) by (rewrite CX; unfold ffsll_high; apply getmem_bound).
      destruct (bsf32_machine_effect R_ECX R_EDX s c1 s1 x eq_refl eq_refl B XS)
        as (NO & k & SPEC & STATE).
      subst x. rewrite CX in SPEC, STATE.
      destruct SPEC as [[Z _]|FIRST]; [contradiction|].
      rewrite STATE. repeat x86_step.
      unfold ffsll_preinc, ebx_save_frame in *; psimpl; elimstore; psimpl; csimpl.
      split; [exact FRAME|]. exists (32+k). split.
      * rewrite ffsll_arg_split, ZERO, N.lor_0_r. apply first_set64_high. exact FIRST.
      * apply N.mod_small. pose proof (proj1 FIRST) as K. clear - K. lia.
    + destruct PRE as (FRAME & k & FIRST & DX). repeat x86_step.
      unfold ffsll_join, ebx_save_frame in *; psimpl; elimstore; psimpl.
      split; [exact FRAME|].
      right. exists k. split; [exact FIRST|]. apply bsf_increment64_small. exact (proj1 FIRST).
    + destruct PRE as [FRAME RESULT]. unfold ebx_save_frame in FRAME.
      destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR). repeat x86_step.
      unfold ffsll_post, cdecl_leaf_frame, save_ebx_reference. psimpl.
      rewrite ?MEM, ?SP, ?SI, ?DI, ?BP, ?RD, ?WR. psimpl.
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      split; [|exact RESULT].
      rewrite ?(N.mod_small _ _ SPBOUND), (saved_ebx_load s0 BXBOUND).
      repeat split; first [reflexivity|assumption].
Qed.

Theorem ffsll_correct :
  forall prog (EXT : ffsll_i386 ⊆2 prog) s0 (MDL : models x86typctx s0) t xs
    (ENTRY : startof t xs=(Addr 0x63bb4,s0)),
  satisfies_all prog (ffsll_invs s0) ffsll_exit (xs::t).
Proof.
  intros prog EXT s0 MDL t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold ffsll_invs, ffsll_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply ffsll_correct_local; [exact MDL|]. rewrite START. exact ENTRY.
Qed.

Theorem ffsll_returns :
  forall prog (EXT : ffsll_i386 ⊆2 prog) s0 (MDL : models x86typctx s0) t s x s'
    (ENTRY : startof t (Addr 0x63bd4,s)=(Addr 0x63bb4,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x63bd4,s)::t))
    (UT : unterminated ffsll_exit t),
  exists result, ffs_result64 (ffsll_arg s0) result /\
    cdecl_returned (save_ebx_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 MDL t s x s' ENTRY XP UT.
  pose proof (ffsll_correct prog EXT s0 MDL t (Addr 0x63bd4,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (ffsll_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_ebx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x63bd4) (s:=s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (save_ebx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_ebx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
