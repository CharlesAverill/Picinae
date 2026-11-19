(* wcsncmp -- musl i386, wide-character comparison with an EBX stack save

   SEMANTICS
   ---------
   Compare at most n signed wide characters, stopping at a mismatch or common NUL.
   Return -1 or +1 according to signed ordering of the first differing pair,
   or zero after a common NUL or n equal nonzero pairs.
   Save EBX in the four bytes below entry ESP and restore it before RET.

   SPECIFICATION (wcsncmp(3), Linux man-pages 6.9.1, local manual)
   ----------------------------------------------------------
     #include <wchar.h>
     int wcsncmp(const wchar_t *s1, const wchar_t *s2, size_t n);
   Compare at most n characters through the first NUL. Return zero for equal
   truncated strings; otherwise the result sign orders the first unequal pair.
   Source: /usr/share/man/man3/wcsncmp.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: wcsncmp, ELF VA 0x66861; Ghidra image base 0x10000,
           global entry 0x76861, RET 0x7689f.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global lift with generated type check.
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
   WIDE-STRING CONTRACT: Compare at most n wchar_t values, stopping at a
   common NUL or first mismatch. Earlier values are equal and nonzero.
   The result is exactly -1, 0 or +1 according to signed wchar_t ordering.
   No string length or stop witness is supplied by the caller.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack i386_compare i386_signed i386_wstringcmp wcsncmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition wcsncmp_arg2 (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wcsncmp_count (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition wcsncmp_pre (s0:store) := models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (cdecl_arg s0) (4*wcsncmp_count s0) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (wcsncmp_arg2 s0) (4*wcsncmp_count s0).
Definition wcsncmp_cursor (s0 s:store) := ebx_save_frame s0 s /\
  exists k, k<=wcsncmp_count s0 /\ s R_ECX=wcsncmp_count s0-k /\
    s R_EDX=(cdecl_arg s0+4*k) mod 2^32 /\
    s R_EAX=(wcsncmp_arg2 s0+4*k) mod 2^32 /\
    wide_string_prefix (save_ebx_memory s0) (cdecl_arg s0) (wcsncmp_arg2 s0) k.
Definition wcsncmp_tail (s0 s:store) := ebx_save_frame s0 s /\
  exists k, k<wcsncmp_count s0 /\ s R_EDX=(cdecl_arg s0+4*k) mod 2^32 /\
    s R_EAX=(wcsncmp_arg2 s0+4*k) mod 2^32 /\
    wide_string_prefix (save_ebx_memory s0) (cdecl_arg s0) (wcsncmp_arg2 s0) k /\
    (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k)=0 \/
     getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k)<>
       getmem 32 LittleE 4 (save_ebx_memory s0) (wcsncmp_arg2 s0+4*k)).
Definition wcsncmp_join (s0 s:store) := ebx_save_frame s0 s /\
  wide_bounded_string_result (save_ebx_memory s0) (cdecl_arg s0) (wcsncmp_arg2 s0)
    (wcsncmp_count s0) (s R_ECX).
Definition wcsncmp_post (s0 s:store) := cdecl_leaf_frame (save_ebx_reference s0) s /\
  wide_bounded_string_result (s0 V_MEM32) (cdecl_arg s0) (wcsncmp_arg2 s0)
    (wcsncmp_count s0) (s R_EAX).
Definition wcsncmp_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x76861 => Some (s=s0 /\ wcsncmp_pre s0)
  | 0x76862 => Some (ebx_save_frame s0 s)
  | 0x7686e => Some (wcsncmp_cursor s0 s)
  | 0x76887 => Some (wcsncmp_tail s0 s)
  | 0x7689c => Some (wcsncmp_join s0 s)
  | 0x7689f => Some (wcsncmp_post s0 s)
  | _ => None end | _ => None end.
Definition wcsncmp_exit := at_address 0x7689f.
Theorem wcsncmp_nwc : forall s1 s2, wcsncmp_i386 s1=wcsncmp_i386 s2.
Proof. reflexivity. Qed.
Theorem wcsncmp_correct_local : forall s0 (PRE0:wcsncmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x76861,s0)),
  satisfies_all wcsncmp_i386 (wcsncmp_invs s0) wcsncmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. split; [reflexivity|exact PRE0].
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + destruct PRE as [EQ CONTRACT]. subst s. repeat x86_step.
      unfold ebx_save_frame, save_ebx_memory. psimpl. repeat split; reflexivity.
    + unfold ebx_save_frame in PRE. destruct PRE as (MEM & SP & SI & DI & BP & RD & WR).
      repeat x86_step. unfold wcsncmp_cursor, ebx_save_frame. psimpl; elimstore; psimpl.
      split; [repeat split; first [reflexivity|assumption]|]. exists 0.
      unfold cdecl_arg, wcsncmp_arg2, wcsncmp_count. psimpl. repeat split.
      * apply N.le_0_l.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * apply save_ebx_stack_word. lia.
      * intros i I. clear - I. lia.
      * intros i I. clear - I. lia.
    + unfold wcsncmp_cursor, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) & k & K & CX & DX & AX & PREFIX).
      repeat x86_step.
      all: unfold wcsncmp_cursor, wcsncmp_tail, wcsncmp_join, ebx_save_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: repeat rewrite getmem_mod_l in *.
      all: csimpl.
      * left. split; [reflexivity|].
        assert (EQ:k=wcsncmp_count s0)
          by (set (n:=wcsncmp_count s0) in *; clearbody n; clear - K BC; lia).
        rewrite <- EQ. exact PREFIX.
      * assert (LT:k<wcsncmp_count s0)
          by (set (n:=wcsncmp_count s0) in *; clearbody n; clear - K BC; lia).
        exists k. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact PREFIX|]. left. assumption.
      * assert (LT:k<wcsncmp_count s0)
          by (set (n:=wcsncmp_count s0) in *; clearbody n; clear - K BC; lia).
        exists (k+1). split.
        -- set (n:=wcsncmp_count s0) in *; clearbody n; clear - LT; lia.
        -- split.
           ++ apply remaining_decrement; [unfold wcsncmp_count; apply getmem_bound|exact LT].
           ++ split.
              ** replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
                   by (set (p:=cdecl_arg s0); clearbody p; clear - p k; lia). reflexivity.
              ** split.
                 --- replace (4+wcsncmp_arg2 s0+4*k) with (wcsncmp_arg2 s0+4*(k+1))
                       by (set (q:=wcsncmp_arg2 s0); clearbody q; clear - q k; lia). reflexivity.
                 --- apply wide_string_prefix_advance; [exact PREFIX|symmetry; assumption|assumption].
      * assert (LT:k<wcsncmp_count s0)
          by (set (n:=wcsncmp_count s0) in *; clearbody n; clear - K BC; lia).
        exists k. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact PREFIX|]. right. congruence.
    + unfold wcsncmp_tail, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) & k & K & DX & AX & PREFIX & STOP).
      repeat x86_step.
      all: unfold wcsncmp_join, ebx_save_frame; psimpl; elimstore; psimpl.
      all: repeat rewrite getmem_mod_l in *.
      all: fold (sub_overflow32
        (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
        (getmem 32 LittleE 4 (save_ebx_memory s0) (wcsncmp_arg2 s0+4*k))) in *.
      all: rewrite (sub_flags_signed_compare
        (getmem 32 LittleE 4 (save_ebx_memory s0) (cdecl_arg s0+4*k))
        (getmem 32 LittleE 4 (save_ebx_memory s0) (wcsncmp_arg2 s0+4*k))
        (getmem_bound _ _ _ _ _) (getmem_bound _ _ _ _ _)) in *.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: right; exists k; split; [exact K|]; split; [exact PREFIX|]; split; [exact STOP|].
      all: csimpl.
      all: rewrite ?Bool.negb_involutive in BC.
      * symmetry. apply wide_character_order_less. exact BC.
      * rewrite BC. cbn [negb]. symmetry. apply wide_character_order_not_less. exact BC.
    + unfold wcsncmp_join, ebx_save_frame in PRE.
      destruct PRE as ((MEM & SP & SI & DI & BP & RD & WR) & RESULT).
      repeat x86_step.
      unfold wcsncmp_post, cdecl_leaf_frame, save_ebx_reference. psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & NOP & NOQ).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      split.
      * rewrite (N.mod_small _ _ SPBOUND), (saved_ebx_load s0 BXBOUND).
        repeat split; first [reflexivity|assumption].
      * eapply wide_bounded_string_transport with (m1:=save_ebx_memory s0).
        -- intros i I. exact (save_ebx_wide s0 _ _ i NOP I).
        -- intros i I. exact (save_ebx_wide s0 _ _ i NOQ I).
        -- exact RESULT.
Qed.

Theorem wcsncmp_correct :
  forall prog (EXT : wcsncmp_i386 ⊆2 prog) s0 (PRE0 : wcsncmp_pre s0) t xs
    (ENTRY : startof t xs = (Addr 0x76861,s0)),
  satisfies_all prog (wcsncmp_invs s0) wcsncmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY.
  eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO.
    unfold wcsncmp_invs, wcsncmp_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *;
      try reflexivity; try discriminate).
  - intros xs' t' START. apply wcsncmp_correct_local; [exact PRE0|].
    rewrite START. exact ENTRY.
Qed.

Theorem wcsncmp_returns :
  forall prog (EXT : wcsncmp_i386 ⊆2 prog) s0 (PRE0 : wcsncmp_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x7689f,s) = (Addr 0x76861,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x7689f,s)::t))
    (UT : unterminated wcsncmp_exit t),
  exists result,
    wide_bounded_string_result (s0 V_MEM32) (cdecl_arg s0) (wcsncmp_arg2 s0) (wcsncmp_count s0) result /\
    cdecl_returned (save_ebx_reference s0) result x s' /\
    x = Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcsncmp_correct prog EXT s0 PRE0 t (Addr 0x7689f,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcsncmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_ebx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p := prog) (ret := 0x7689f) (s := s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x = Addr (getmem 32 LittleE 4 (save_ebx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_ebx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
