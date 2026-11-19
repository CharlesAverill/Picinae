(* wcscmp -- musl i386, signed wide-character comparison

   SEMANTICS
   ---------
   Save ESI and EBX, load two pointers, and compare signed wide-characters until
   a mismatch or a common NUL. Return their ordering (-1, 0, +1) and restore
   both registers. No locale-dependent table or caller-supplied length.

   SPECIFICATION (wcscmp(3), Linux man-pages 6.9.1, 2024-05-02)
   --------------------------------------------------------
     #include <wchar.h>
     int wcscmp(const wchar_t *s1, const wchar_t *s2);
   Compare signed wide characters. The result's sign gives their signed ordering at
   the first mismatch; equal NUL-terminated strings give zero.
   Source: /usr/share/man/man3/wcscmp.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: wcscmp, ELF VA 0x2f860; global entry 0x3f860, RET 0x3f8a2.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global-address lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  Two 32-bit pointers at entry ESP+4 and ESP+8. Each input string
           through its first NUL avoids the callee's two four-byte save slots.
           Architectural values have their declared widths.
   Output: Exact signed ordering (-1, 0, +1) at the first mismatch or
           common NUL, with an equal nonzero prefix in original memory.
           Memory changes only at ESP-4 (saved ESI) and ESP-8 (saved EBX).
           All callee-saved registers and access permissions are restored.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness. No length, stop index or termination witness
           is supplied by the caller. No concrete memory-access safety claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_compare i386_stack2 i386_signed i386_wstringcmp wcscmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition wcscmp_arg2 (s0:store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wcscmp_pre (s0:store) := models x86typctx s0 /\
  wide_string_avoids_saves s0 (cdecl_arg s0) /\ wide_string_avoids_saves s0 (wcscmp_arg2 s0).
Definition wcscmp_cursor (s0 s:store) := si_bx_save_frame s0 s /\
  s R_EBX=cdecl_arg s0 /\ s R_ESI=wcscmp_arg2 s0 /\ exists k,
  s R_EAX=(4*k) mod 2^32 /\ wide_string_prefix (s0 V_MEM32) (cdecl_arg s0) (wcscmp_arg2 s0) k.
Definition wcscmp_tail (s0 s:store) := si_bx_save_frame s0 s /\ exists k,
  s R_EDX=getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k) /\
  s R_ECX=getmem 32 LittleE 4 (s0 V_MEM32) (wcscmp_arg2 s0+4*k) /\
  wide_string_prefix (s0 V_MEM32) (cdecl_arg s0) (wcscmp_arg2 s0) k /\
  (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)=0 \/
   getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)<>
   getmem 32 LittleE 4 (s0 V_MEM32) (wcscmp_arg2 s0+4*k)).
Definition wcscmp_join (s0 s:store) := si_bx_save_frame s0 s /\
  wide_string_result (s0 V_MEM32) (cdecl_arg s0) (wcscmp_arg2 s0) (s R_EAX).
Definition wcscmp_post (s0 s:store) := cdecl_leaf_frame (save_si_bx_reference s0) s /\
  wide_string_result (s0 V_MEM32) (cdecl_arg s0) (wcscmp_arg2 s0) (s R_EAX).
Definition wcscmp_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x3f860 => Some (s=s0)
  | 0x3f880 => Some (wcscmp_cursor s0 s)
  | 0x3f891 => Some (wcscmp_tail s0 s)
  | 0x3f8a0 => Some (wcscmp_join s0 s)
  | 0x3f8a2 => Some (wcscmp_post s0 s)
  | _ => None end | _ => None end.
Definition wcscmp_exit := at_address 0x3f8a2.
Theorem wcscmp_nwc : forall s1 s2, wcscmp_i386 s1=wcscmp_i386 s2.
Proof. reflexivity. Qed.
Theorem wcscmp_correct_local : forall s0 (PRE0:wcscmp_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x3f860,s0)),
  satisfies_all wcscmp_i386 (wcscmp_invs s0) wcscmp_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0. destruct_inv 32 PRE.
    + subst s. repeat x86_step. unfold wcscmp_cursor, si_bx_save_frame. psimpl.
      fold (save_si_bx_memory s0). split; [repeat split; reflexivity|].
      unfold cdecl_arg, wcscmp_arg2. repeat split; try reflexivity.
      exists 0. split; [reflexivity|]. split; intros i I; clear - I; lia.
    + unfold wcscmp_cursor, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & BX & SI & k & AX & PREFIX).
      destruct PRE0 as (_ & NOP & NOQ).
      pose proof (saved_wide_string_word s0 _ k NOP (proj2 PREFIX)) as PREAD.
      pose proof (saved_wide_string_word s0 _ k NOQ (wide_string_prefix_right _ _ _ _ PREFIX)) as QREAD.
      repeat x86_step.
      all: unfold wcscmp_cursor, wcscmp_tail, si_bx_save_frame; psimpl; elimstore; psimpl.
      all: repeat rewrite wide_word_offset_mod in *.
      all: rewrite ?PREAD, ?QREAD in *.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: csimpl.
      * exists k. split; [reflexivity|]. split; [reflexivity|]. split; [exact PREFIX|].
        left. exact BC0.
      * split; [reflexivity|]. split; [reflexivity|]. exists (k+1). split.
        -- replace (4+4*k) with (4*(k+1)) by (clear - k; lia). reflexivity.
        -- apply wide_string_prefix_advance; assumption.
      * exists k. split; [reflexivity|]. split; [reflexivity|]. split; [exact PREFIX|].
        right. exact BC.
    + unfold wcscmp_tail, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & k & DX & CX & PREFIX & STOP).
      repeat x86_step.
      all: unfold wcscmp_join, si_bx_save_frame; psimpl; elimstore; psimpl.
      all: fold (sub_overflow32
        (getmem 32 LittleE 4 (s0 V_MEM32) (wcscmp_arg2 s0+4*k))
        (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k))) in *.
      all: rewrite (sub_flags_signed_compare
        (getmem 32 LittleE 4 (s0 V_MEM32) (wcscmp_arg2 s0+4*k))
        (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k))
        (getmem_bound _ _ _ _ _) (getmem_bound _ _ _ _ _)) in *.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: exists k; split; [exact PREFIX|]; split; [exact STOP|].
      all: csimpl.
      all: set (a:=getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)) in *.
      all: set (b:=getmem 32 LittleE 4 (s0 V_MEM32) (wcscmp_arg2 s0+4*k)) in *.
      all: assert (A:a<2^32) by (unfold a; apply getmem_bound).
      all: assert (B:b<2^32) by (unfold b; apply getmem_bound).
      all: clearbody a b.
      all: rewrite ?Bool.negb_involutive.
      all: destruct (slt 32 b a) eqn:GT; cbn [negb] in BC |- *; try discriminate.
      all: try solve [symmetry; apply wide_character_order_greater; exact GT].
      all: destruct (b=?a) eqn:EQ; cbn in BC; try discriminate.
      * apply N.eqb_eq in EQ. rewrite EQ. symmetry. apply wide_character_order_equal.
      * rewrite (wide_character_order_reverse_not_less a b A B GT), N.eqb_sym, EQ. reflexivity.
    + unfold wcscmp_join, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & RESULT). repeat x86_step.
      unfold wcscmp_post, cdecl_leaf_frame, save_si_bx_reference. psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & _).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      pose proof (MDL R_ESI 32 eq_refl) as SIBOUND.
      split; [|exact RESULT].
      rewrite (N.mod_small _ _ SPBOUND),
        (saved_si_bx_load_bx s0 BXBOUND), (saved_si_bx_load_si s0 SIBOUND).
      repeat split; first [reflexivity|assumption].
Qed.

Theorem wcscmp_correct :
  forall prog (EXT : wcscmp_i386 ⊆2 prog) s0 (PRE0 : wcscmp_pre s0) t xs
    (ENTRY : startof t xs=(Addr 0x3f860,s0)),
  satisfies_all prog (wcscmp_invs s0) wcscmp_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold wcscmp_invs, wcscmp_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply wcscmp_correct_local; [exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wcscmp_returns :
  forall prog (EXT : wcscmp_i386 ⊆2 prog) s0 (PRE0 : wcscmp_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x3f8a2,s)=(Addr 0x3f860,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x3f8a2,s)::t))
    (UT : unterminated wcscmp_exit t),
  exists result, wide_string_result (s0 V_MEM32) (cdecl_arg s0) (wcscmp_arg2 s0) result /\
    cdecl_returned (save_si_bx_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wcscmp_correct prog EXT s0 PRE0 t (Addr 0x3f8a2,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wcscmp_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_si_bx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x3f8a2) (s:=s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (save_si_bx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_si_bx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
