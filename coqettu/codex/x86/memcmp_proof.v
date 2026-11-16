(* memcmp -- musl i386, byte comparison with an EBX stack save

   SEMANTICS
   ---------
   Compare at most n unsigned bytes, stopping at the first differing pair.
   Return the signed difference of that pair, or zero when all n pairs agree.
   Save EBX in the four bytes below entry ESP and restore it before RET.

   SPECIFICATION (memcmp(3), Linux man-pages 6.9.1, local manual)
   ----------------------------------------------------------
     #include <string.h>
     int memcmp(const void *s1, const void *s2, size_t n);
   Return zero for equal n-byte regions; otherwise return a value whose sign
   is the sign of the difference of the first unequal unsigned-byte pair.
   Source: /usr/share/man/man3/memcmp.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: memcmp, ELF VA 0x2f1a0; Ghidra image base 0x10000,
           global entry 0x3f1a0, RET 0x3f1e1.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  s1, s2, n are entry stack words at ESP+4, ESP+8, ESP+12.
           Architectural registers have their declared widths. Both compared
           regions are disjoint from the four-byte callee stack-save slot.
   Output: EAX is zero or the exact modular byte difference at the first
           mismatch. EBX, ESI, EDI and EBP are restored. Memory changes only
           by saving entry EBX below entry ESP; those bytes remain saved.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness for every 32-bit n, including zero. No match
           witness, alignment or arbitrary size bound is required. Addresses
           wrap modulo 2^32. Termination and successful accesses are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack i386_compare memcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition memcmp_arg2 (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition memcmp_count (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).

Definition memcmp_pre (s0 : store) : Prop :=
  models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (cdecl_arg s0) (memcmp_count s0) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (memcmp_arg2 s0) (memcmp_count s0).


Definition memcmp_cursor (s0 s : store) : Prop :=
  ebx_save_frame s0 s /\ exists k, k <= memcmp_count s0 /\
  s R_EAX = memcmp_count s0-k /\
  s R_ECX = (cdecl_arg s0+k) mod 2^32 /\
  s R_EDX = (memcmp_arg2 s0+k) mod 2^32 /\
  equal_prefix (save_ebx_memory s0) (cdecl_arg s0) (memcmp_arg2 s0) k.

Definition memcmp_prepop (s0 s : store) : Prop :=
  ebx_save_frame s0 s /\ compare_result (save_ebx_memory s0)
    (cdecl_arg s0) (memcmp_arg2 s0) (memcmp_count s0) (s R_EAX).

Definition memcmp_post (s0 s : store) : Prop :=
  cdecl_leaf_frame (save_ebx_reference s0) s /\ compare_result (s0 V_MEM32)
    (cdecl_arg s0) (memcmp_arg2 s0) (memcmp_count s0) (s R_EAX).

Definition memcmp_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x3f1a0 => Some (s=s0 /\ memcmp_pre s0)
  | 0x3f1a1 => Some (ebx_save_frame s0 s)
  | 0x3f1c9 => Some (memcmp_cursor s0 s)
  | 0x3f1e0 => Some (memcmp_prepop s0 s)
  | 0x3f1e1 => Some (memcmp_post s0 s)
  | _ => None end | _ => None end.
Definition memcmp_exit := at_address 0x3f1e1.

Theorem memcmp_nwc : forall s1 s2, memcmp_i386 s1 = memcmp_i386 s2.
Proof. reflexivity. Qed.

Theorem memcmp_correct_local :
  forall s0 (PRE0 : memcmp_pre s0) t xs
    (ENTRY : startof t xs = (Addr 0x3f1a0,s0)),
  satisfies_all memcmp_i386 (memcmp_invs s0) memcmp_exit (xs::t).
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
      unfold memcmp_cursor, ebx_save_frame. psimpl; elimstore; psimpl.
      split; [repeat split; first [reflexivity|assumption]|].
      exists 0. unfold memcmp_count, memcmp_arg2, cdecl_arg. psimpl.
      repeat split.
      * apply N.le_0_l.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * intros i I. clear - I. lia.
    + unfold memcmp_cursor, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) &
        k & K & AX & CX & DX & PREFIX).
      repeat x86_step.
      all: unfold memcmp_cursor, memcmp_prepop, ebx_save_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: csimpl.
      * left. split; [reflexivity|].
        assert (EQ : k = memcmp_count s0).
        { match goal with ZERO : memcmp_count s0-k = 0 |- _ =>
            set (n := memcmp_count s0) in *; clearbody n;
            clear - K ZERO; lia end. }
        rewrite <- EQ. exact PREFIX.
      * assert (LT : k < memcmp_count s0).
        { match goal with NONZERO : memcmp_count s0-k <> 0 |- _ =>
            set (n := memcmp_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        exists (k+1). repeat split; try reflexivity.
        -- set (n := memcmp_count s0) in *; clearbody n; clear - LT; lia.
        -- apply remaining_decrement; [unfold memcmp_count; apply getmem_bound|exact LT].
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- replace (1+memcmp_arg2 s0+k) with (memcmp_arg2 s0+(k+1))
             by (set (p := memcmp_arg2 s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (equal_prefix_advance (save_ebx_memory s0)
             (cdecl_arg s0) (memcmp_arg2 s0) k PREFIX). assumption.
      * right. exists k.
        assert (LT : k < memcmp_count s0).
        { match goal with NONZERO : memcmp_count s0-k <> 0 |- _ =>
            set (n := memcmp_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        repeat split; first [exact LT | exact PREFIX | reflexivity | assumption].
    + unfold memcmp_prepop, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) & RESULT).
      repeat x86_step.
      unfold memcmp_post, cdecl_leaf_frame, save_ebx_reference.
      psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & NOP & NOQ).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      split.
      * rewrite (N.mod_small _ _ SPBOUND), (saved_ebx_load s0 BXBOUND).
        repeat split; first [reflexivity|assumption].
      * eapply compare_result_transport with (m1 := save_ebx_memory s0).
        -- intros i I. exact (save_ebx_byte s0 _ _ i NOP I).
        -- intros i I. exact (save_ebx_byte s0 _ _ i NOQ I).
        -- exact RESULT.
Qed.

Theorem memcmp_correct :
  forall prog (EXT : memcmp_i386 ⊆2 prog) s0 (PRE0 : memcmp_pre s0) t xs
    (ENTRY : startof t xs = (Addr 0x3f1a0,s0)),
  satisfies_all prog (memcmp_invs s0) memcmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY.
  eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO.
    unfold memcmp_invs, memcmp_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *;
      try reflexivity; try discriminate).
  - intros xs' t' START. apply memcmp_correct_local; [exact PRE0|].
    rewrite START. exact ENTRY.
Qed.

Theorem memcmp_returns :
  forall prog (EXT : memcmp_i386 ⊆2 prog) s0 (PRE0 : memcmp_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x3f1e1,s) = (Addr 0x3f1a0,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x3f1e1,s)::t))
    (UT : unterminated memcmp_exit t),
  exists result,
    compare_result (s0 V_MEM32) (cdecl_arg s0) (memcmp_arg2 s0) (memcmp_count s0) result /\
    cdecl_returned (save_ebx_reference s0) result x s' /\
    x = Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (memcmp_correct prog EXT s0 PRE0 t (Addr 0x3f1e1,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (memcmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_ebx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p := prog) (ret := 0x3f1e1) (s := s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x = Addr (getmem 32 LittleE 4 (save_ebx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_ebx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
