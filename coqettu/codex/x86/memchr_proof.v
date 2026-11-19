(* memchr -- musl i386, bounded alignment/word/tail byte search

   SEMANTICS / SPECIFICATION
   Search n bytes for c converted to unsigned char, returning the first
   matching pointer or NULL after n nonmatches. Source: local Linux
   man-pages 6.9.1, /usr/share/man/man3/memchr.3.gz (paraphrased).

   PROVENANCE
   musl-1.2.6-r6, coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   ELF VA 0x20f00; Ghidra image base 0x10000; global RET 0x30fde.
   Ghidra 12.0 PUBLIC, frozen strict/global-address/typed lifter.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT / OUTPUT
   Pointer, int and count: entry ESP+4, ESP+8 and ESP+12. Architectural
   values have declared widths. The input region avoids the 20-byte frame
   below entry ESP. The exact memory snapshot saves EBP, EDI, ESI and EBX,
   with an optional endpoint word at depth 20. All four registers, access
   permissions and the original return address are restored; RET adds four
   to entry ESP. The result refers to the original input memory.
   Scope: partial correctness for every 32-bit count, including zero,
   in any containing program. No match witness or alignment premise.
   Addresses wrap modulo 2^32; termination/access success are not asserted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_stack4 i386_byte_search i386_search_arith
  memchr_support memchr_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition memchr_invs (s0:store) (t:trace):option Prop:=
  match t with (Addr a,s)::_ =>match a with
  | 0x30f00=>Some (s=s0)
  | 0x30f1c=>Some (memchr_align s0 s)
  | 0x30f30=>Some (memchr_setup s0 s)
  | 0x30f83=>Some (memchr_words s0 s)
  | 0x30fc6=>Some (memchr_tail s0 s)
  | 0x30fd5=>Some (memchr_prepop s0 s)
  | 0x30fde=>Some (memchr_post s0 s)
  | _=>None end | _=>None end.
Definition memchr_exit:=at_address 0x30fde.

Theorem memchr_correct_local:forall s0 (PRE0:memchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x30f00,s0)),
  satisfies_all memchr_i386 (memchr_invs s0) memchr_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold memchr_align,memchr_frame,memchr_memory,memchr_local,save4_memory.
      psimpl. fold (save4_registers s0).
      split;[repeat split;reflexivity|]. split.
      * unfold memchr_char. reflexivity.
      * exists 0. unfold memchr_count,cdecl_arg. psimpl.
        repeat split;try reflexivity;try apply N.le_0_l.
        intros i I. clear - I;lia.
    + destruct PRE as [FRAME [BX [k [K [AX [DX PREFIX]]]]]].
      unfold memchr_frame in FRAME. destruct FRAME as (MEM & SP & RD & WR).
      pose proof (memchr_count_bound s0) as COUNT.
      pose proof (memchr_char_bound s0) as CHAR.
      repeat x86_step.
      all: unfold memchr_frame;psimpl;elimstore;psimpl;csimpl.
      * exists false. split;[repeat split;first[reflexivity|assumption]|].
        eapply memchr_exhausted;[exact K|exact BC0|exact PREFIX].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|exact BX]|].
        exists k. repeat split;try reflexivity;try assumption.
        set (n:=memchr_count s0) in *;clearbody n;clear - K BC0;lia.
      * exists false. split;[repeat split;first[reflexivity|assumption]|].
        eapply memchr_exhausted;[exact K|exact BC0|exact PREFIX].
      * split;[repeat split;first[reflexivity|assumption]|]. split;[reflexivity|].
        exists k. repeat split;try reflexivity;try assumption.
        set (n:=memchr_count s0) in *;clearbody n;clear - K BC0;lia.
      * assert (LT:k<memchr_count s0) by
          (set (n:=memchr_count s0) in *;clearbody n;clear - K BC0;lia).
        split;[repeat split;first[reflexivity|assumption]|]. split;[reflexivity|].
        exists (k+1). repeat split;try reflexivity.
        -- set (n:=memchr_count s0) in *;clearbody n;clear - LT;lia.
        -- apply remaining_decrement;assumption.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- eapply memchr_prefix_step1;[exact PRE0|exact LT|exact PREFIX|exact BC1].
    + destruct PRE as [FRAME [BX [k [K [AX [DX PREFIX]]]]]].
      unfold memchr_frame in FRAME. destruct FRAME as (MEM & SP & RD & WR).
      pose proof (memchr_count_bound s0) as COUNT.
      pose proof (memchr_char_bound s0) as CHAR.
      repeat x86_step.
      all: unfold memchr_frame;psimpl;elimstore;psimpl;csimpl.
      * exists false. split;[repeat split;first[reflexivity|assumption]|].
        split;[reflexivity|]. exists k. repeat split;try reflexivity;try assumption.
        set (n:=memchr_count s0) in *;clearbody n;clear - K;lia.
      * assert (LE:k<=memchr_count s0) by (clear - K;lia).
        split.
        -- unfold memchr_memory,memchr_local,save4_memory,memchr_endpoint. psimpl.
           rewrite search_endpoint_write by exact LE. repeat split;first[reflexivity|assumption].
        -- split;[reflexivity|]. split;[apply search_repeated_signed_product;exact CHAR|].
           exists k,(k+N.land (memchr_count s0-k) 4294967292).
           pose proof (search_word_endpoint (memchr_count s0) k COUNT LE) as (LOW & HIGH & MULT).
           repeat split;try assumption;try reflexivity. apply search_word_address.
    + destruct PRE as [FRAME [BX [BP [k [e [KE [EN [MULT [DX [CX PREFIX]]]]]]]]]].
      unfold memchr_frame in FRAME. destruct FRAME as (MEM & SP & RD & WR).
      pose proof (memchr_count_bound s0) as COUNT.
      pose proof (memchr_char_bound s0) as CHAR.
      assert (KN:k<=memchr_count s0) by (clear - KE EN;lia).
      assert (KB:k<2^32) by
        (set (n:=memchr_count s0) in *;clearbody n;clear - KN COUNT;lia).
      assert (EB:e<2^32) by
        (set (n:=memchr_count s0) in *;clearbody n;clear - EN COUNT;lia).
      repeat x86_step.
      all: unfold memchr_frame;psimpl;elimstore;psimpl.
      all: rewrite ?(memchr_remaining_load s0 k KN).
      all: csimpl.
      * subst e. exists true. split;[repeat split;first[reflexivity|assumption]|].
        split;[first[reflexivity|exact BX]|]. exists k. repeat split;first[reflexivity|assumption].
      * assert (ROOM:k+4<=e) by (apply search_word_room;assumption).
        assert (FIT:k+4<=memchr_count s0) by (clear - ROOM EN;lia).
        split;[repeat split;first[reflexivity|assumption]|]. split;[first[reflexivity|exact BX]|]. split;[reflexivity|].
        exists (k+4),e. repeat split;try reflexivity;try assumption.
        -- apply search_word_multiple_next;assumption.
        -- replace (4+cdecl_arg s0+k) with (cdecl_arg s0+(k+4))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- eapply memchr_prefix_step4;[exact PRE0|exact FIT|exact PREFIX|].
           rewrite <- zero_mask32_machine. exact BC0.
      * exists true. split;[repeat split;first[reflexivity|assumption]|].
        split;[first[reflexivity|exact BX]|]. exists k. repeat split;first[reflexivity|assumption].
    + destruct PRE as [used [FRAME [BX [k [K [AX [CX PREFIX]]]]]]].
      unfold memchr_frame in FRAME. destruct FRAME as (MEM & SP & RD & WR).
      pose proof (memchr_count_bound s0) as COUNT.
      pose proof (memchr_char_bound s0) as CHAR.
      repeat x86_step.
      all: unfold memchr_frame;psimpl;elimstore;psimpl;csimpl.
      * exists used. split;[repeat split;first[reflexivity|assumption]|].
        eapply memchr_exhausted;[exact K|exact BC|exact PREFIX].
      * assert (LT:k<memchr_count s0) by
          (set (n:=memchr_count s0) in *;clearbody n;clear - K BC;lia).
        exists used. split;[repeat split;first[reflexivity|assumption]|].
        rewrite ?CX. eapply memchr_found with (used:=used) (k:=k);
          [exact PRE0|exact LT|exact PREFIX|exact BC0].
      * assert (LT:k<memchr_count s0) by
          (set (n:=memchr_count s0) in *;clearbody n;clear - K BC;lia).
        exists used. split;[repeat split;first[reflexivity|assumption]|].
        split;[first[reflexivity|exact BX]|]. exists (k+1). repeat split;try reflexivity.
        -- set (n:=memchr_count s0) in *;clearbody n;clear - LT;lia.
        -- apply remaining_decrement;assumption.
        -- replace (1+cdecl_arg s0+k) with (cdecl_arg s0+(k+1))
             by (set (p:=cdecl_arg s0);clearbody p;clear - p k;lia). reflexivity.
        -- eapply memchr_prefix_step1;[exact PRE0|exact LT|exact PREFIX|exact BC0].
    + destruct PRE as [used [FRAME RESULT]]. unfold memchr_frame in FRAME.
      destruct FRAME as (MEM & SP & RD & WR).
      repeat x86_step. unfold memchr_post. exists used.
      unfold cdecl_leaf_frame,memchr_reference. psimpl;elimstore;psimpl.
      destruct PRE0 as [MDL NO].
      pose proof (MDL R_ESP 32 eq_refl) as SPBOUND.
      pose proof (MDL R_EBX 32 eq_refl) as BXBOUND.
      pose proof (MDL R_ESI 32 eq_refl) as SIBOUND.
      pose proof (MDL R_EDI 32 eq_refl) as DIBOUND.
      pose proof (MDL R_EBP 32 eq_refl) as BPBOUND.
      split;[|exact RESULT].
      rewrite (N.mod_small _ _ SPBOUND). unfold memchr_memory.
      rewrite (save4_load_bx s0 _ BXBOUND),(save4_load_si s0 _ SIBOUND),
        (save4_load_di s0 _ DIBOUND),(save4_load_bp s0 _ BPBOUND).
      repeat split;first[reflexivity|assumption].
Qed.


Theorem memchr_correct:forall prog (EXT:memchr_i386 ⊆2 prog) s0 (PRE0:memchr_pre s0) t xs
  (ENTRY:startof t xs=(Addr 0x30f00,s0)),
  satisfies_all prog (memchr_invs s0) memchr_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono;[exact EXT| |].
  - intros a s tl EX NO. unfold memchr_invs,memchr_i386 in *.
    destruct a as [|a];[reflexivity|].
    repeat (destruct a as [a|a|];cbn in *;try reflexivity;try discriminate).
  - intros xs' t' START. apply memchr_correct_local;[exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem memchr_returns:forall prog (EXT:memchr_i386 ⊆2 prog) s0 (PRE0:memchr_pre s0) t s x s'
  (ENTRY:startof t (Addr 0x30fde,s)=(Addr 0x30f00,s0))
  (XP:exec_prog prog ((x,s')::(Addr 0x30fde,s)::t)) (UT:unterminated memchr_exit t),
  exists used result,memchr_result s0 result /\
    cdecl_returned (memchr_reference s0 used) result x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (memchr_correct prog EXT s0 PRE0 t (Addr 0x30fde,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (memchr_post s0 s) in INV. destruct INV as [used [FRAME RESULT]].
  assert (RETURN:cdecl_returned (memchr_reference s0 used) (s R_EAX) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x30fde) (s:=s).
    - apply EXT. reflexivity.
    - split;[reflexivity|exact FRAME].
    - exact (exec_prog_final _ _ _ _ XP). }
  exists used,(s R_EAX). split;[exact RESULT|]. split;[exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS.
  change (x=Addr (getmem 32 LittleE 4 (memchr_memory s0 used) (s0 R_ESP))) in ADDRESS.
  pose proof (save4_stack_word s0 (memchr_local s0 used) 0 ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. unfold memchr_memory in ADDRESS. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.

Lemma memchr_unsigned_char:forall s0,
  memchr_char s0=getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP) mod 256.
Proof.
  intros s0. unfold memchr_char. symmetry.
  change (getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP) mod 2^(1*8)=
    getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP)). rewrite getmem_mod. reflexivity.
Qed.
