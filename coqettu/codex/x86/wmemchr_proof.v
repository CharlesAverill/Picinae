(* wmemchr -- musl i386, bounded wide-character scan

   SEMANTICS
   ---------
   Inspect at most n consecutive four-byte wchar_t values and return the
   address of the first value equal to c, or NULL if all n values differ.

   SPECIFICATION (wmemchr(3), Linux man-pages 6.9.1, 2024-05-02)
   ---------------------------------------------------------
     #include <wchar.h>
     wchar_t *wmemchr(const wchar_t *s, wchar_t c, size_t n);
   Return the first matching element in the specified n-element array,
   or NULL if no element matches.
   Source: /usr/share/man/man3/wmemchr.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: wmemchr, ELF VA 0x37c80; Ghidra image base 0x10000,
           global entry 0x47c80, RET sites 0x47c9e and 0x47ca1.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  s, c and n are the entry stack words at ESP+4, ESP+8 and ESP+12.
   Output: EAX is the first matching address, or zero after n nonmatches.
           Memory and callee-saved registers are preserved. ESP increases
           by four when RET pops the original saved return address.
   Scope:  Partial correctness for all 32-bit s, c, n, including n=0.
           No precomputed match index or size restriction is required.
           Addresses wrap modulo 2^32; concrete access success and
           termination are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings wmemchr_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wmemchr_char (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wmemchr_count (s0 : store) :=
  getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).

Definition wmemchr_result (s0 : store) (result : N) : Prop :=
  (exists k, k < wmemchr_count s0 /\
    wide_prefix (s0 V_MEM32) (cdecl_arg s0) (wmemchr_char s0) k /\
    getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k) = wmemchr_char s0 /\
    result = (cdecl_arg s0+4*k) mod 2^32) \/
  (result = 0 /\ wide_prefix (s0 V_MEM32) (cdecl_arg s0)
    (wmemchr_char s0) (wmemchr_count s0)).

Definition wmemchr_cursor (s0 s : store) : Prop :=
  cdecl_leaf_frame s0 s /\ exists k,
    k <= wmemchr_count s0 /\
    s R_EDX = wmemchr_count s0-k /\
    s R_ECX = wmemchr_char s0 /\
    s R_EAX = (cdecl_arg s0+4*k) mod 2^32 /\
    wide_prefix (s0 V_MEM32) (cdecl_arg s0) (wmemchr_char s0) k.

Definition wmemchr_post (s0 s : store) : Prop :=
  cdecl_leaf_frame s0 s /\ wmemchr_result s0 (s R_EAX).

Definition wmemchr_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x47c80 => Some (s=s0)
  | 0x47c96 => Some (wmemchr_cursor s0 s)
  | 0x47c9e | 0x47ca1 => Some (wmemchr_post s0 s)
  | _ => None end | _ => None end.
Definition wmemchr_exit (t : trace) :=
  (at_address 0x47c9e t || at_address 0x47ca1 t)%bool.

Theorem wmemchr_nwc : forall s1 s2, wmemchr_i386 s1 = wmemchr_i386 s2.
Proof. reflexivity. Qed.

Theorem wmemchr_preserves_memory :
  forall_endstates wmemchr_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wmemchr_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates wmemchr_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem wmemchr_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x47c80,s0)),
  satisfies_all wmemchr_i386 (wmemchr_invs s0) wmemchr_exit (xs::t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold wmemchr_cursor, cdecl_leaf_frame. psimpl.
      split; [repeat split; reflexivity|].
      exists 0. unfold cdecl_arg, wmemchr_char, wmemchr_count, wide_prefix.
      psimpl. repeat split; try reflexivity.
      * apply N.le_0_l.
      * intros i I. clear - I. lia.
    + unfold wmemchr_cursor, cdecl_leaf_frame in PRE.
      destruct PRE as ((MEM & SP & BX & SI & DI & BP & RD & WR) &
        k & K & DX & CX & AX & PREFIX).
      repeat x86_step.
      all: unfold wmemchr_cursor, wmemchr_post, cdecl_leaf_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: assert (CHARBOUND : wmemchr_char s0 < 2^32)
        by (unfold wmemchr_char; apply getmem_bound).
      all: try rewrite (N.mod_small _ _ CHARBOUND) in *.
      all: csimpl.
      * right. split; [reflexivity|].
        assert (EQ : k = wmemchr_count s0).
        { match goal with ZERO : wmemchr_count s0-k = 0 |- _ =>
            set (n := wmemchr_count s0) in *; clearbody n;
            clear - K ZERO; lia end. }
        rewrite <- EQ. exact PREFIX.
      * left. exists k.
        assert (LT : k < wmemchr_count s0).
        { match goal with NONZERO : wmemchr_count s0-k <> 0 |- _ =>
            set (n := wmemchr_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        repeat split; first [exact LT | exact PREFIX | reflexivity | assumption].
      * assert (LT : k < wmemchr_count s0).
        { match goal with NONZERO : wmemchr_count s0-k <> 0 |- _ =>
            set (n := wmemchr_count s0) in *; clearbody n;
            clear - K NONZERO; lia end. }
        exists (k+1). repeat split; try reflexivity.
        -- set (n := wmemchr_count s0) in *; clearbody n; clear - LT; lia.
        -- apply remaining_decrement; [unfold wmemchr_count; apply getmem_bound|exact LT].
        -- replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (wide_prefix_advance (s0 V_MEM32) (cdecl_arg s0)
             (wmemchr_char s0) k PREFIX).
           rewrite getmem_mod_l. assumption.
Qed.

Theorem wmemchr_correct :
  forall prog (EXT : wmemchr_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x47c80,s0)),
  satisfies_all prog (wmemchr_invs s0) wmemchr_exit (xs::t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO.
    unfold wmemchr_invs, wmemchr_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *;
      try reflexivity; try discriminate).
  - intros xs' t' START. apply wmemchr_correct_local.
    rewrite START. exact ENTRY.
Qed.

Theorem wmemchr_returns :
  forall prog (EXT : wmemchr_i386 ⊆2 prog) s0 t s ret x s'
    (RET : ret = 0x47c9e \/ ret = 0x47ca1)
    (ENTRY : startof t (Addr ret,s) = (Addr 0x47c80,s0))
    (XP : exec_prog prog ((x,s')::(Addr ret,s)::t))
    (UT : unterminated wmemchr_exit t),
  exists result, wmemchr_result s0 result /\ cdecl_returned s0 result x s'.
Proof.
  intros prog EXT s0 t s ret x s' RET ENTRY XP UT.
  pose proof (wmemchr_correct prog EXT s0 t (Addr ret,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  assert (POST : wmemchr_post s0 s).
  { destruct RET as [EQ|EQ]; subst ret; exact INV. }
  destruct POST as [FRAME RESULT].
  exists (s R_EAX). split; [exact RESULT|].
  eapply cdecl_ret_step with (p := prog) (ret := ret) (s := s).
  - destruct RET as [EQ|EQ]; subst ret; apply EXT; reflexivity.
  - split; [reflexivity|exact FRAME].
  - exact (exec_prog_final _ _ _ _ XP).
Qed.
