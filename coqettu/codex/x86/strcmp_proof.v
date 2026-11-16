(* strcmp -- musl i386, unsigned byte comparison

   SEMANTICS
   ---------
   Save ESI and EBX, load two pointers, and compare unsigned bytes until
   a mismatch or a common NUL. Return their signed difference and restore
   both registers. No locale-dependent table or caller-supplied length.

   SPECIFICATION (strcmp(3), Linux man-pages 6.9.1, 2024-06-15)
   --------------------------------------------------------
     #include <string.h>
     int strcmp(const char *s1, const char *s2);
   Compare unsigned characters. The result's sign gives their ordering at
   the first mismatch; equal NUL-terminated strings give zero.
   Source: /usr/share/man/man3/strcmp.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: strcmp, ELF VA 0x2f400; global entry 0x3f400, RET 0x3f43e.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global-address lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  Two 32-bit pointers at entry ESP+4 and ESP+8. Each input string
           through its first NUL avoids the callee's two four-byte save slots.
           Architectural values have their declared widths.
   Output: Exact modular unsigned-byte difference at the first mismatch or
           common NUL, with an equal nonzero prefix in original memory.
           Memory changes only at ESP-4 (saved ESI) and ESP-8 (saved EBX).
           All callee-saved registers and access permissions are restored.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness. No length, stop index or termination witness
           is supplied by the caller. No concrete memory-access safety claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_compare i386_stack2 i386_stringcmp strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strcmp_arg2 (s0 : store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition strcmp_pre (s0 : store) := models x86typctx s0 /\
  string_avoids_saves s0 (cdecl_arg s0) /\ string_avoids_saves s0 (strcmp_arg2 s0).
Definition strcmp_cursor (s0 s : store) :=
  si_bx_save_frame s0 s /\ s R_EBX=cdecl_arg s0 /\ s R_ESI=strcmp_arg2 s0 /\
  exists k, s R_EAX=k mod 2^32 /\
    string_equal_prefix (s0 V_MEM32) (cdecl_arg s0) (strcmp_arg2 s0) k.
Definition strcmp_prepop (s0 s : store) := si_bx_save_frame s0 s /\
  string_compare_result (s0 V_MEM32) (cdecl_arg s0) (strcmp_arg2 s0) (s R_EAX).
Definition strcmp_post (s0 s : store) := cdecl_leaf_frame (save_si_bx_reference s0) s /\
  string_compare_result (s0 V_MEM32) (cdecl_arg s0) (strcmp_arg2 s0) (s R_EAX).
Definition strcmp_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x3f400 => Some (s=s0)
  | 0x3f420 => Some (strcmp_cursor s0 s)
  | 0x3f43c => Some (strcmp_prepop s0 s)
  | 0x3f43e => Some (strcmp_post s0 s)
  | _ => None end | _ => None end.
Definition strcmp_exit := at_address 0x3f43e.
Theorem strcmp_nwc : forall s1 s2, strcmp_i386 s1=strcmp_i386 s2.
Proof. reflexivity. Qed.

Theorem strcmp_correct_local : forall s0 (PRE0 : strcmp_pre s0) t xs
  (ENTRY : startof t xs=(Addr 0x3f400,s0)),
  satisfies_all strcmp_i386 (strcmp_invs s0) strcmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step. unfold strcmp_cursor, si_bx_save_frame.
      psimpl. fold (save_si_bx_memory s0).
      split; [repeat split; reflexivity|].
      unfold cdecl_arg, strcmp_arg2.
      repeat split; try reflexivity. exists 0. split; [reflexivity|].
      split; intros i I; clear - I; lia.
    + unfold strcmp_cursor, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & BX & SI & k & AX & PREFIX).
      pose proof (proj2 PREFIX) as NZ.
      pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
      destruct PRE0 as (MDL & NOP & NOQ).
      pose proof (saved_string_byte s0 _ k NOP NZ) as PREAD.
      pose proof (saved_string_byte s0 _ k NOQ NZQ) as QREAD.
      clear MDL NOP NOQ. repeat x86_step.
      all: unfold strcmp_cursor, strcmp_prepop, si_bx_save_frame; psimpl; elimstore; psimpl.
      all: repeat rewrite byte_offset_mod in *.
      all: rewrite ?PREAD, ?QREAD in *.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: csimpl.
      * eapply string_compare_stop with (k:=k); [exact PREFIX| |].
        -- left. rewrite BC, BC0. reflexivity.
        -- rewrite BC, BC0. reflexivity.
      * split; [reflexivity|]. split; [reflexivity|]. exists (k+1). split.
        -- replace (1+k) with (k+1) by lia. reflexivity.
        -- apply string_equal_prefix_advance; [exact PREFIX|exact BC|].
           rewrite BC. exact BC0.
      * eapply string_compare_stop with (k:=k); [exact PREFIX|right; exact BC|reflexivity].
    + unfold strcmp_prepop, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & RESULT).
      repeat x86_step.
      unfold strcmp_post, cdecl_leaf_frame, save_si_bx_reference. psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & _).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      pose proof (MDL R_ESI 32 eq_refl) as SIBOUND.
      split; [|exact RESULT].
      rewrite (N.mod_small _ _ SPBOUND),
        (saved_si_bx_load_bx s0 BXBOUND), (saved_si_bx_load_si s0 SIBOUND).
      repeat split; first [reflexivity|assumption].
Qed.

Theorem strcmp_correct :
  forall prog (EXT : strcmp_i386 ⊆2 prog) s0 (PRE0 : strcmp_pre s0) t xs
    (ENTRY : startof t xs=(Addr 0x3f400,s0)),
  satisfies_all prog (strcmp_invs s0) strcmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold strcmp_invs, strcmp_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply strcmp_correct_local; [exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem strcmp_returns :
  forall prog (EXT : strcmp_i386 ⊆2 prog) s0 (PRE0 : strcmp_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x3f43e,s)=(Addr 0x3f400,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x3f43e,s)::t))
    (UT : unterminated strcmp_exit t),
  exists result, string_compare_result (s0 V_MEM32) (cdecl_arg s0) (strcmp_arg2 s0) result /\
    cdecl_returned (save_si_bx_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (strcmp_correct prog EXT s0 PRE0 t (Addr 0x3f43e,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (strcmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_si_bx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x3f43e) (s:=s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (save_si_bx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_si_bx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
