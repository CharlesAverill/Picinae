(* strlen -- musl i386, aligned four-byte scan

   SEMANTICS
   ---------
   Scan individual bytes until the pointer is four-byte aligned, then scan
   words using (x-0x01010101) & ~x & 0x80808080. A zero mask proves all four
   bytes are nonzero. On a nonzero mask, locate the first NUL byte by a byte
   scan, then subtract the original pointer.

   SPECIFICATION (strlen(3), Linux man-pages 6.9.1, local manual)
   -----------------------------------------------------------
     #include <string.h>
     size_t strlen(const char *s);
   Return the number of bytes preceding the first terminating NUL.
   Source: /usr/share/man/man3/strlen.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: strlen, ELF VA 0x2f500; Ghidra image base 0x10000,
           global entry 0x3f500, RET 0x3f54c.
   Lifter: Ghidra 12.0 PUBLIC + tools/ghidra-lifter/pcode2coq_headless.py,
           --globalAddressing --strictFailure --typeCheck.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The pointer s is the 32-bit word at entry ESP+4.
   Output: EAX is the first-NUL index in entry memory. Memory, EBX, ESI,
           EDI, EBP and access permissions are preserved; ESP is preserved
           at RET and increases by four after RET.
   Scope:  Partial correctness. No input length, termination witness, pointer
           alignment or artificial string-size bound is required of callers.
           Word loads may read past the terminator. Addresses wrap modulo
           2^32 as in Picinae. Access success and termination are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strlen_cursor (s0 s : store) : Prop :=
  cdecl_leaf_frame s0 s /\ exists k,
  s R_EAX = (cdecl_arg s0+k) mod 2^32 /\
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.

Definition strlen_post (s0 s : store) : Prop :=
  cdecl_leaf_frame s0 s /\ exists k,
  s R_EAX = k /\ first_nul (s0 V_MEM32) (cdecl_arg s0) k.

Definition strlen_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x3f500 => Some (s=s0)
  | 0x3f513 | 0x3f523 | 0x3f543 => Some (strlen_cursor s0 s)
  | 0x3f54c => Some (strlen_post s0 s)
  | _ => None end
  | _ => None end.
Definition strlen_exit := at_address 0x3f54c.

Theorem strlen_nwc : forall s1 s2, strlen_i386 s1 = strlen_i386 s2.
Proof. reflexivity. Qed.

Theorem strlen_preserves_memory :
  forall_endstates strlen_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strlen_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates strlen_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem strlen_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x3f500,s0)),
  satisfies_all strlen_i386 (strlen_invs s0) strlen_exit (xs::t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold strlen_cursor, cdecl_leaf_frame. psimpl.
      split; [repeat split; reflexivity|].
      exists 0. unfold cdecl_arg, nonzero_prefix. psimpl.
      split; [reflexivity|]. intros i I. clear - I. lia.
    + unfold strlen_cursor, cdecl_leaf_frame in PRE.
      destruct PRE as ((MEM & SP & BX & SI & DI & BP & RD & WR) & k & AX & NZ).
      repeat x86_step.
      all: unfold strlen_cursor, strlen_post, cdecl_leaf_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity | assumption]|].
      * exists k. split; [reflexivity|exact NZ].
      * exists (k mod 2^32). split.
        -- unfold cdecl_arg. apply add_msub_l.
        -- apply (prefix_stop (s0 V_MEM32) (cdecl_arg s0) k NZ).
           rewrite getmem_mod_l. csimpl. assumption.
      * exists (k+1). split.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (prefix_advance1 (s0 V_MEM32) (cdecl_arg s0) k NZ).
           rewrite getmem_mod_l. csimpl. assumption.
    + unfold strlen_cursor, cdecl_leaf_frame in PRE.
      destruct PRE as ((MEM & SP & BX & SI & DI & BP & RD & WR) & k & AX & NZ).
      repeat x86_step.
      all: unfold strlen_cursor, strlen_post, cdecl_leaf_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity | assumption]|].
      * exists (k+4). split.
        -- replace (4+cdecl_arg s0+k) with (cdecl_arg s0+(k+4))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (prefix_advance4 (s0 V_MEM32) (cdecl_arg s0) k NZ).
           unfold zero_mask32. rewrite getmem_mod_l.
           psimpl. csimpl. assumption.
      * exists k. split; [reflexivity|exact NZ].
    + unfold strlen_cursor, cdecl_leaf_frame in PRE.
      destruct PRE as ((MEM & SP & BX & SI & DI & BP & RD & WR) & k & AX & NZ).
      repeat x86_step.
      all: unfold strlen_cursor, strlen_post, cdecl_leaf_frame.
      all: psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity | assumption]|].
      * exists (k mod 2^32). split.
        -- unfold cdecl_arg. apply add_msub_l.
        -- apply (prefix_stop (s0 V_MEM32) (cdecl_arg s0) k NZ).
           rewrite getmem_mod_l. csimpl. assumption.
      * exists (k+1). split.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p := cdecl_arg s0); clearbody p; clear - p k; lia).
           reflexivity.
        -- apply (prefix_advance1 (s0 V_MEM32) (cdecl_arg s0) k NZ).
           rewrite getmem_mod_l. csimpl. assumption.
Qed.

Theorem strlen_correct :
  forall prog (EXT : strlen_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x3f500,s0)),
  satisfies_all prog (strlen_invs s0) strlen_exit (xs::t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO.
    unfold strlen_invs, strlen_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *;
      try reflexivity; try discriminate).
  - intros xs' t' START. apply strlen_correct_local.
    rewrite START. exact ENTRY.
Qed.

Theorem strlen_returns :
  forall prog (EXT : strlen_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x3f54c,s) = (Addr 0x3f500,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x3f54c,s)::t))
    (UT : unterminated strlen_exit t),
  exists k, first_nul (s0 V_MEM32) (cdecl_arg s0) k /\
    cdecl_returned s0 k x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  pose proof (strlen_correct prog EXT s0 t (Addr 0x3f54c,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as POST.
  change (strlen_post s0 s) in POST.
  destruct POST as (FRAME & k & AX & NUL).
  exists k. split; [exact NUL|].
  eapply cdecl_ret_step with (p := prog) (ret := 0x3f54c) (s := s).
  - apply EXT. reflexivity.
  - split; assumption.
  - exact (exec_prog_final _ _ _ _ XP).
Qed.
