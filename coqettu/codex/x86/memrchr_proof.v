(* memrchr -- musl i386, backwards byte search

   SEMANTICS
   ---------
   Save ESI and EBX. Start at s+n-1 and inspect bytes backwards until s-1,
   returning the last matching byte in the original interval, or NULL.
   Only the low byte of the int argument participates in comparisons.

   SPECIFICATION (memchr(3), Linux man-pages 6.9.1, 2024-05-02)
   --------------------------------------------------------
     #include <string.h>
     void *memrchr(const void *s, int c, size_t n);
   Search the n-byte region backwards for c converted to unsigned char.
   Return the matching pointer, or NULL if no byte matches.
   Source: /usr/share/man/man3/memchr.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: memrchr, ELF VA 0x37b00; global entry 0x47b00, RET 0x47b38.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global-address lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  Pointer, int and count at entry ESP+4, ESP+8 and ESP+12.
           The n-byte input region avoids the two four-byte save slots at
           entry ESP-4 and ESP-8. Architectural values have declared widths.
   Output: EAX is zero after n nonmatches, or the greatest matching index's
           address with all later bytes unequal, in original input memory.
           Only the two save slots change; ESI and EBX are restored along
           with all other callee-saved registers and access permissions.
           RET pops the original return address and adds four to entry ESP.
   Scope:  Partial correctness for all 32-bit counts, including zero. No
           match witness or artificial size bound; addresses wrap modulo
           2^32. No concrete access-success or termination claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack2 i386_reverse memrchr_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition memrchr_char (s0 : store) := getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP).
Definition memrchr_count (s0 : store) := getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition memrchr_pre (s0 : store) := models x86typctx s0 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 (cdecl_arg s0) (memrchr_count s0) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 4 (cdecl_arg s0) (memrchr_count s0).
Definition memrchr_result (s0 : store) result :=
  reverse_search_result (s0 V_MEM32) (cdecl_arg s0) (memrchr_char s0) (memrchr_count s0) result.
Definition memrchr_cursor (s0 s : store) := si_bx_save_frame s0 s /\
  s R_EBX=msub 32 (cdecl_arg s0) 1 /\ s R_ESI=memrchr_char s0 /\
  exists k, k<=memrchr_count s0 /\ s R_EAX=msub 32 (cdecl_arg s0+k) 1 /\
    nonmatching_suffix (s0 V_MEM32) (cdecl_arg s0) (memrchr_char s0) k (memrchr_count s0).
Definition memrchr_prepop (s0 s : store) := si_bx_save_frame s0 s /\ memrchr_result s0 (s R_EAX).
Definition memrchr_post (s0 s : store) := cdecl_leaf_frame (save_si_bx_reference s0) s /\
  memrchr_result s0 (s R_EAX).
Definition memrchr_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x47b00 => Some (s=s0)
  | 0x47b20 => Some (memrchr_cursor s0 s)
  | 0x47b36 => Some (memrchr_prepop s0 s)
  | 0x47b38 => Some (memrchr_post s0 s)
  | _ => None end | _ => None end.
Definition memrchr_exit := at_address 0x47b38.
Theorem memrchr_nwc : forall s1 s2, memrchr_i386 s1=memrchr_i386 s2.
Proof. reflexivity. Qed.

Theorem memrchr_correct_local : forall s0 (PRE0 : memrchr_pre s0) t xs
  (ENTRY : startof t xs=(Addr 0x47b00,s0)),
  satisfies_all memrchr_i386 (memrchr_invs s0) memrchr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step. unfold memrchr_cursor, si_bx_save_frame.
      psimpl. fold (save_si_bx_memory s0).
      split; [repeat split; reflexivity|].
      unfold cdecl_arg, memrchr_char, memrchr_count. psimpl.
      repeat split; try reflexivity. exists (getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP)).
      split; [apply N.le_refl|]. split.
      * symmetry. apply add_msub_swap.
      * intros i LOWER UPPER. clear - LOWER UPPER. lia.
    + unfold memrchr_cursor, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & BX & SI & k & K & AX & SUFFIX).
      assert (COUNT : memrchr_count s0<2^32) by (unfold memrchr_count; apply getmem_bound).
      assert (KB : k<2^32) by (set (n:=memrchr_count s0) in *; clearbody n; clear - K COUNT; lia).
      repeat x86_step.
      all: unfold memrchr_cursor, memrchr_prepop, si_bx_save_frame; psimpl; elimstore; psimpl.
      all: split; [repeat split; first [reflexivity|assumption]|].
      all: assert (CHARBOUND : memrchr_char s0<2^32)
        by (unfold memrchr_char; eapply N.lt_le_trans; [apply getmem_bound|lia]).
      all: rewrite ?(N.mod_small _ _ CHARBOUND) in *.
      all: csimpl.
      * subst k. unfold memrchr_result, reverse_search_result. left. split; [reflexivity|exact SUFFIX].
      * assert (POS : 0<k) by (clear - BC; lia).
        assert (IN : k-1<memrchr_count s0)
          by (set (n:=memrchr_count s0) in *; clearbody n; clear - K POS; lia).
        destruct PRE0 as (_ & NO4 & NO8).
        pose proof (save_si_bx_region_byte s0 _ _ (k-1) NO4 NO8 IN) as READ.
        rewrite (reverse_cursor_byte _ _ POS), getmem_mod_l, READ in BC0.
        unfold memrchr_result, reverse_search_result. right. exists (k-1).
        split; [exact IN|]. split.
        -- replace (k-1+1) with k by (clear - POS; lia). exact SUFFIX.
        -- split; [exact BC0|apply reverse_cursor_byte; exact POS].
      * assert (POS : 0<k) by (clear - BC; lia).
        assert (IN : k-1<memrchr_count s0)
          by (set (n:=memrchr_count s0) in *; clearbody n; clear - K POS; lia).
        destruct PRE0 as (_ & NO4 & NO8).
        pose proof (save_si_bx_region_byte s0 _ _ (k-1) NO4 NO8 IN) as READ.
        rewrite (reverse_cursor_byte _ _ POS), getmem_mod_l, READ in BC0.
        split; [reflexivity|]. split; [reflexivity|]. exists (k-1).
        split; [clear - K IN; lia|]. split.
        -- pose proof (msub_add_distr 32 (cdecl_arg s0+k) 1 1) as DECREMENT.
           change (msub 32 (cdecl_arg s0+k) 2 =
             msub 32 (msub 32 (cdecl_arg s0+k) 1) 1) in DECREMENT.
           rewrite DECREMENT.
           apply reverse_cursor_previous. exact POS.
        -- apply nonmatching_suffix_previous; assumption.
    + unfold memrchr_prepop, si_bx_save_frame in PRE.
      destruct PRE as ((MEM & SP & DI & BP & RD & WR) & RESULT). repeat x86_step.
      unfold memrchr_post, cdecl_leaf_frame, save_si_bx_reference. psimpl; elimstore; psimpl.
      destruct PRE0 as (MDL & _).
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      pose proof (MDL R_ESI 32 eq_refl) as SIBOUND.
      split; [|exact RESULT].
      rewrite (N.mod_small _ _ SPBOUND),
        (saved_si_bx_load_bx s0 BXBOUND), (saved_si_bx_load_si s0 SIBOUND).
      repeat split; first [reflexivity|assumption].
Qed.

Lemma memrchr_unsigned_char : forall s0,
  memrchr_char s0 = getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP) mod 256.
Proof.
  intros s0. unfold memrchr_char. symmetry.
  change (getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP) mod 2^(1*8) =
    getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP)).
  rewrite getmem_mod. reflexivity.
Qed.

Theorem memrchr_correct :
  forall prog (EXT : memrchr_i386 ⊆2 prog) s0 (PRE0 : memrchr_pre s0) t xs
    (ENTRY : startof t xs=(Addr 0x47b00,s0)),
  satisfies_all prog (memrchr_invs s0) memrchr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold memrchr_invs, memrchr_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply memrchr_correct_local; [exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem memrchr_returns :
  forall prog (EXT : memrchr_i386 ⊆2 prog) s0 (PRE0 : memrchr_pre s0) t s x s'
    (ENTRY : startof t (Addr 0x47b38,s)=(Addr 0x47b00,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x47b38,s)::t))
    (UT : unterminated memrchr_exit t),
  exists result, memrchr_result s0 result /\
    cdecl_returned (save_si_bx_reference s0) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (memrchr_correct prog EXT s0 PRE0 t (Addr 0x47b38,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (memrchr_post s0 s) in INV. destruct INV as [FRAME RESULT].
  assert (RETURN : cdecl_returned (save_si_bx_reference s0) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x47b38) (s:=s).
    - apply EXT. reflexivity.
    - split; [reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s R_EAX). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (save_si_bx_memory s0) (s0 R_ESP))) in ADDRESS.
  pose proof (save_si_bx_stack_word s0 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
