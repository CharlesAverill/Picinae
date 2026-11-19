(* iswcntrl -- musl i386

   SEMANTICS
   ---------
   Classify the full 32-bit argument as an wide control character in 0..31, 127..159, 8232..8233 or 65529..65531.
   Return exactly zero or one, preserving memory and the cdecl ABI frame.

   SPECIFICATION (iswcntrl(3), Linux man-pages 6.9.1, 2024-05-02)
   -------------------------------------------------------
     #include <wctype.h>
     int iswcntrl(wint_t c);
   Return nonzero exactly for an wide control character in 0..31, 127..159, 8232..8233 or 65529..65531; musl returns one.
   Source: /usr/share/man/man3/iswcntrl.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: iswcntrl, ELF VA 0x3f1b8; global entry 0x4f1b8, RET 0x4f1ef.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The 32-bit argument is the word at entry ESP+4.
   Output: EAX is the classification result; memory, ESP, callee-saved registers
           and access permissions are preserved. RET pops the original address.
   Scope:  Partial correctness for all binary argument representations, including WEOF. No locale table is consulted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits i386_wctype iswcntrl_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

Definition iswcntrl_spec (c:N) : N := if wide_control c then 1 else 0.
Definition iswcntrl_invs (s0 : store) :=
  leaf_invs 0x4f1b8 0x4f1ef s0 (iswcntrl_spec (cdecl_arg s0)).
Definition iswcntrl_exit := at_address 0x4f1ef.

Theorem iswcntrl_nwc : forall s1 s2, iswcntrl_i386 s1 = iswcntrl_i386 s2.
Proof. reflexivity. Qed.

Theorem iswcntrl_preserves_memory :
  forall_endstates iswcntrl_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem iswcntrl_correct_local :
  forall s0 t xs (ENTRY : startof t xs = (Addr 0x4f1b8, s0)),
  satisfies_all iswcntrl_i386 (iswcntrl_invs s0) iswcntrl_exit (xs :: t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE.
    clear - PRE. unfold iswcntrl_invs, leaf_invs in PRE.
    destruct_inv 32 PRE.
    all: try subst s.
    all: unfold iswcntrl_invs, leaf_invs, iswcntrl_exit, at_address.
    all: repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame, iswcntrl_spec, cdecl_arg.
    all: psimpl.
    all: try exact PRE.
    all: repeat split; try reflexivity.
    all: fold (cdecl_arg s0) in *.
    all: assert (BOUND:cdecl_arg s0<2^32) by (unfold cdecl_arg;apply getmem_bound).
    all: set (c:=cdecl_arg s0) in *;clearbody c.
    all: pose proof (classify_interval (c) 127 159 BOUND ltac:(lia) ltac:(lia)) as T1.
    all: pose proof (classify_interval (c) 8232 8233 BOUND ltac:(lia) ltac:(lia)) as T2.
    all: pose proof (classify_interval (c) 65529 65531 BOUND ltac:(lia) ltac:(lia)) as T3.
    all: change (N.lor (if msub 32 (c) 127 <? 32 then 1 else 0)
       (if c=?159 then 1 else 0)=if (127<=?c)&&(c<=?159) then 1 else 0) in T1.
    all: change (N.lor (if msub 32 (c) 8232 <? 1 then 1 else 0)
       (if c=?8233 then 1 else 0)=if (8232<=?c)&&(c<=?8233) then 1 else 0) in T2.
    all: change (N.lor (if msub 32 (c) 65529 <? 2 then 1 else 0)
       (if c=?65531 then 1 else 0)=if (65529<=?c)&&(c<=?65531) then 1 else 0) in T3.
    all: rewrite ?T1,?T2,?T3,?lt_eq_word in *.
    all: unfold wide_control.
    all: destruct (c<=?31), ((127<=?c)&&(c<=?159)),
      ((8232<=?c)&&(c<=?8233)),
      ((65529<=?c)&&(c<=?65531));cbn in *;congruence.
Qed.

Theorem iswcntrl_correct :
  forall prog (EXT : iswcntrl_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs = (Addr 0x4f1b8, s0)),
  satisfies_all prog (iswcntrl_invs s0) iswcntrl_exit (xs :: t).
Proof.
  intros prog EXT s0 t xs ENTRY.
  eapply leaf_correct_extend with (p := iswcntrl_i386).
  - exact EXT.
  - intros s H. discriminate H.
  - intros s H. discriminate H.
  - intros. apply iswcntrl_correct_local. assumption.
  - exact ENTRY.
Qed.

Theorem iswcntrl_preserves_callee_saved : forall v,
  List.In v cdecl_saved ->
  forall_endstates iswcntrl_i386 (fun _ s _ s' => s v = s' v).
Proof. prove_cdecl_saved. Qed.

Theorem iswcntrl_returns :
  forall prog (EXT : iswcntrl_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x4f1ef,s) = (Addr 0x4f1b8,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x4f1ef,s)::t))
    (UT : unterminated iswcntrl_exit t),
  cdecl_returned s0 (iswcntrl_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  eapply leaf_return with (p := prog) (t := t) (s := s) (entry := 0x4f1b8) (ret := 0x4f1ef).
  - discriminate.
  - apply EXT. reflexivity.
  - apply iswcntrl_correct; assumption.
  - exact XP.
  - exact UT.
Qed.
