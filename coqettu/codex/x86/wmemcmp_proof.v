(* wmemcmp -- musl i386, wide-character comparison with an EBX stack save

   SEMANTICS
   ---------
   Compare at most n signed wide characters, stopping at the first differing pair.
   Return -1 or +1 according to signed ordering of that pair, or zero when all n pairs agree.
   Save EBX in the four bytes below entry ESP and restore it before RET.

   SPECIFICATION (wmemcmp(3), Linux man-pages 6.9.1, local manual)
   ----------------------------------------------------------
     #include <wchar.h>
     int wmemcmp(const wchar_t *s1, const wchar_t *s2, size_t n);
   Return zero for equal n-element arrays; otherwise return a value whose sign
   is the sign of the signed ordering of the first unequal wide-character pair.
   Source: /usr/share/man/man3/wmemcmp.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: wmemcmp, ELF VA 0x2fc60; Ghidra image base 0x10000,
           global entry 0x3fc60, RET 0x3fca7.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  s1, s2, n are entry stack words at ESP+4, ESP+8, ESP+12.
           Architectural registers have their declared widths. Both compared
           regions are disjoint from the four-byte callee stack-save slot.
   Output: EAX is zero, -1 or +1 according to the signed order at the first
           mismatch. EBX, ESI, EDI and EBP are restored. Memory changes only
           by saving entry EBX below entry ESP; those bytes remain saved.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness for every 32-bit n, including zero. No match
           witness, alignment or arbitrary size bound is required. Addresses
           wrap modulo 2^32. Termination and successful accesses are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack i386_compare i386_signed wmemcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wmemcmp_arg2 (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wmemcmp_count (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).

Definition wmemcmp_pre (s0 : store) : Prop :=
  models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (cdecl_arg s0) (4*wmemcmp_count s0) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (wmemcmp_arg2 s0) (4*wmemcmp_count s0).


Definition wmemcmp_cursor (s0 s : store) : Prop :=
  ebx_save_frame s0 s /\ exists k, k <= wmemcmp_count s0 /\
  s R_EAX = wmemcmp_count s0-k /\
  s R_ECX = (cdecl_arg s0+4*k) mod 2^32 /\
  s R_EDX = (wmemcmp_arg2 s0+4*k) mod 2^32 /\
  wide_equal_prefix (save_ebx_memory s0) (cdecl_arg s0) (wmemcmp_arg2 s0) k.

Definition wmemcmp_prepop (s0 s : store) : Prop :=
  ebx_save_frame s0 s /\ wide_compare_result (save_ebx_memory s0)
    (cdecl_arg s0) (wmemcmp_arg2 s0) (wmemcmp_count s0) (s R_EAX).

Definition wmemcmp_post (s0 s : store) : Prop :=
  cdecl_leaf_frame (save_ebx_reference s0) s /\ wide_compare_result (s0 V_MEM32)
    (cdecl_arg s0) (wmemcmp_arg2 s0) (wmemcmp_count s0) (s R_EAX).

Definition wmemcmp_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x3fc60 => Some (s=s0 /\ wmemcmp_pre s0)
  | 0x3fc61 => Some (ebx_save_frame s0 s)
  | 0x3fc89 => Some (wmemcmp_cursor s0 s)
  | 0x3fca6 => Some (wmemcmp_prepop s0 s)
  | 0x3fca7 => Some (wmemcmp_post s0 s)
  | _ => None end | _ => None end.
Definition wmemcmp_exit := at_address 0x3fca7.

Theorem wmemcmp_nwc : forall s1 s2, wmemcmp_i386 s1 = wmemcmp_i386 s2.
Proof. reflexivity. Qed.

Theorem wmemcmp_correct_local :
  forall s0 (PRE0 : wmemcmp_pre s0) t xs
    (ENTRY : startof t xs = (Addr 0x3fc60,s0)),
  satisfies_all wmemcmp_i386 (wmemcmp_invs s0) wmemcmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. split; [reflexivity|exact PRE0].
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0.
    destruct_inv 32 PRE.
    + destruct PRE as [EQ CONTRACT]. subst s. repeat x86_step.
      unfold ebx_save_frame, save_ebx_memory. psimpl.
      repeat split; reflexivity.
    + unfold ebx_save_frame in PRE.
      destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step.
      unfold wmemcmp_cursor, ebx_save_frame. psimpl; elimstore; psimpl.
      split; [repeat split; first [reflexivity|assumption]|].
      exists 0. unfold wmemcmp_count, wmemcmp_arg2, cdecl_arg. psimpl.
      repeat split.
      * apply N.le_0_l.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * intros i I. clear - I. lia.
    + unfold wmemcmp_cursor, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) &
        k & K & AX & CX & DX & PREFIX).
      repeat x86_step.
      all: unfold wmemcmp_cursor, wmemcmp_prepop, ebx_save_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: repeat rewrite getmem_mod_l in *.
      all: fold (sub_overflow32
        (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
        (getmem 32 LittleE 4 (save_ebx_memory s0) (wmemcmp_arg2 s0+4*k))) in *.
      all: try rewrite (sub_flags_signed_compare
        (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
        (getmem 32 LittleE 4 (save_ebx_memory s0) (wmemcmp_arg2 s0+4*k))
        (getmem_bound _ _ _ _ _) (getmem_bound _ _ _ _ _)) in *.
      all: rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in *.
      all: csimpl.
      * left. split; [reflexivity|].
        assert (EQ : k = wmemcmp_count s0).
        { match goal with ZERO : wmemcmp_count s0-k = 0 |- _ =>
            set (n := wmemcmp_count s0) in *; clearbody n;
            clear - K ZERO; lia end. }
        rewrite <- EQ. exact PREFIX.
      * assert (LT : k < wmemcmp_count s0).
        { match goal with NONZERO : wmemcmp_count s0-k <> 0 |- _ =>
            set (n := wmemcmp_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        exists (k+1). repeat split; try reflexivity.
        -- set (n := wmemcmp_count s0) in *; clearbody n; clear - LT; lia.
        -- apply remaining_decrement; [unfold wmemcmp_count; apply getmem_bound|exact LT].
        -- replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- replace (4+wmemcmp_arg2 s0+4*k) with (wmemcmp_arg2 s0+4*(k+1))
             by (set (p := wmemcmp_arg2 s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (wide_equal_prefix_advance (save_ebx_memory s0)
             (cdecl_arg s0) (wmemcmp_arg2 s0) k PREFIX). assumption.
      * right. exists k.
        assert (LT : k < wmemcmp_count s0).
        { match goal with NONZERO : wmemcmp_count s0-k <> 0 |- _ =>
            set (n := wmemcmp_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        repeat split; try exact LT; try exact PREFIX; try assumption.
        unfold wide_order.
        fold (slt 32 (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
          (getmem 32 LittleE 4 (save_ebx_memory s0) (wmemcmp_arg2 s0+4*k))).
        rewrite BC1. reflexivity.
      * right. exists k.
        assert (LT : k < wmemcmp_count s0).
        { match goal with NONZERO : wmemcmp_count s0-k <> 0 |- _ =>
            set (n := wmemcmp_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        repeat split; try exact LT; try exact PREFIX; try assumption.
        unfold wide_order.
        fold (slt 32 (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
          (getmem 32 LittleE 4 (save_ebx_memory s0) (wmemcmp_arg2 s0+4*k))).
        apply Bool.negb_true_iff in BC1.
        rewrite BC1, (proj2 (N.eqb_neq _ _) BC0). reflexivity.
    + unfold wmemcmp_prepop, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) & RESULT).
      repeat x86_step.
      unfold wmemcmp_post, cdecl_leaf_frame, save_ebx_reference.
      psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & NOP & NOQ).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      split.
      * rewrite (N.mod_small _ _ SPBOUND), (saved_ebx_load s0 BXBOUND).
        repeat split; first [reflexivity|assumption].
      * eapply wide_compare_result_transport with (m1 := save_ebx_memory s0).
        -- intros i I. exact (save_ebx_wide s0 _ _ i NOP I).
        -- intros i I. exact (save_ebx_wide s0 _ _ i NOQ I).
        -- exact RESULT.
Qed.

Theorem wmemcmp_correct :
  forall prog (EXT : wmemcmp_i386 ⊆2 prog) s0 (PRE0 : wmemcmp_pre s0) t xs
    (ENTRY : startof t xs = (Addr 0x3fc60,s0)),
  satisfies_all prog (wmemcmp_invs s0) wmemcmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY.
  eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO.
    unfold wmemcmp_invs, wmemcmp_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *;
      try reflexivity; try discriminate).
  - intros xs' t' START. apply wmemcmp_correct_local; [exact PRE0|].
    rewrite START. exact ENTRY.
Qed.

Theorem wmemcmp_returns :
  forall prog (EXT : wmemcmp_i386 ⊆2 prog) s0 (PRE0 : wmemcmp_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x3fca7,s) = (Addr 0x3fc60,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x3fca7,s)::t))
    (UT : unterminated wmemcmp_exit t),
  exists result,
    wide_compare_result (s0 V_MEM32) (cdecl_arg s0) (wmemcmp_arg2 s0) (wmemcmp_count s0) result /\
    cdecl_returned (save_ebx_reference s0) result x s' /\
    x = Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wmemcmp_correct prog EXT s0 PRE0 t (Addr 0x3fca7,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wmemcmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_ebx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p := prog) (ret := 0x3fca7) (s := s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x = Addr (getmem 32 LittleE 4 (save_ebx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_ebx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
