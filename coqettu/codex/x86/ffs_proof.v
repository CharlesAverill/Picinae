(* ffs -- musl i386, BSF implementation

   SEMANTICS
   ---------
   Return zero for an all-zero int representation. Otherwise return one plus
   the index of its least significant set bit, including for negative inputs.

   SPECIFICATION (ffs(3), Linux man-pages 6.9.1, 2024-05-02)
   -----------------------------------------------------
     #include <strings.h>
     int ffs(int i);
   Number bit positions from one at the least significant bit. Return the
   first set position, or zero if no bits are set.
   Source: /usr/share/man/man3/ffs.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: ffs, ELF VA 0x53b96; Ghidra image base 0x10000,
           global entry 0x63b96, BSF 0x63b9e, RET 0x63ba4.
   Lifter: Ghidra 12.0 PUBLIC + Codex-local pcode2coq_codex.py with the
           committed lifter snapshot in ../lifter_base. Strict global lift.
           BSF's exact p-code graph is adapted to 32 guarded iterations;
           i386_bsf.v proves its per-iteration, loop and instruction semantics.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The int's 32-bit representation is the stack word at entry ESP+4.
   Output: EAX = 0 if input = 0, otherwise k+1 for the first set bit k<32.
           Memory, EBX, ESI, EDI, EBP and access permissions are preserved.
           ESP is unchanged at RET; RET pops the saved return address and
           increases ESP by four modulo 2^32.
   Scope:  Partial correctness for every 32-bit input. No bit-index witness
           is required from callers. The zero path bypasses BSF, whose
           zero-input destination is architecturally undefined.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bsf ffs_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition ffs_post (s0 s : store) :=
  cdecl_leaf_frame s0 s /\ ffs_result32 (cdecl_arg s0) (s R_EAX).
Definition ffs_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x63b96 => Some (s=s0)
  | 0x63b9e => Some (cdecl_leaf_frame s0 s /\ s R_EAX=cdecl_arg s0 /\ cdecl_arg s0<>0)
  | 0x63ba1 => Some (cdecl_leaf_frame s0 s /\
      exists k, first_set32 (cdecl_arg s0) k /\ s R_EAX=k)
  | 0x63ba4 => Some (ffs_post s0 s)
  | _ => None end | _ => None end.
Definition ffs_exit := at_address 0x63ba4.

Theorem ffs_nwc : forall s1 s2, ffs_i386 s1=ffs_i386 s2.
Proof. reflexivity. Qed.
Theorem ffs_preserves_memory :
  forall_endstates ffs_i386 (fun _ s _ s' => s V_MEM32=s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Theorem ffs_preserves_callee_saved : forall v, List.In v cdecl_saved ->
  forall_endstates ffs_i386 (fun _ s _ s' => s v=s' v).
Proof. prove_cdecl_saved. Qed.

Theorem ffs_correct_local :
  forall s0 t xs (ENTRY : startof t xs=(Addr 0x63b96,s0)),
  satisfies_all ffs_i386 (ffs_invs s0) ffs_exit (xs::t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      all: unfold ffs_post; psimpl.
      all: split; [unfold cdecl_leaf_frame; psimpl; repeat split; reflexivity|].
      all: try (unfold ffs_result32, cdecl_arg; csimpl; left; split; assumption).
      all: unfold cdecl_arg; psimpl; split; [reflexivity|csimpl; assumption].
    + destruct PRE as (FRAME & AX & NONZERO).
      eapply NIStep; [reflexivity|reflexivity|]. intros c1 s1 x XS.
      change (exec_stmt x86typctx s (bsf32_stmt R_EAX R_EAX) c1 s1 x) in XS.
      assert (B : s R_EAX < 2^32) by (rewrite AX; unfold cdecl_arg; apply getmem_bound).
      destruct (bsf32_machine_effect R_EAX R_EAX s c1 s1 x eq_refl eq_refl B XS)
        as (NO & k & SPEC & STATE).
      subst x. rewrite AX in SPEC.
      destruct SPEC as [[ZERO _]|FIRST]; [contradiction|].
      rewrite STATE. x86_step.
      unfold cdecl_leaf_frame in FRAME |- *. psimpl.
      split; [exact FRAME|]. exists k. split; [exact FIRST|reflexivity].
    + destruct PRE as (FRAME & k & FIRST & AX). repeat x86_step.
      unfold ffs_post, cdecl_leaf_frame in *; psimpl; elimstore; psimpl.
      split; [exact FRAME|]. right. exists k. split; [exact FIRST|].
      apply bsf_increment_small. exact (proj1 FIRST).
Qed.

Theorem ffs_correct :
  forall prog (EXT : ffs_i386 ⊆2 prog) s0 t xs
    (ENTRY : startof t xs=(Addr 0x63b96,s0)),
  satisfies_all prog (ffs_invs s0) ffs_exit (xs::t).
Proof.
  intros prog EXT s0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold ffs_invs, ffs_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply ffs_correct_local. rewrite START. exact ENTRY.
Qed.

Theorem ffs_returns :
  forall prog (EXT : ffs_i386 ⊆2 prog) s0 t s x s'
    (ENTRY : startof t (Addr 0x63ba4,s)=(Addr 0x63b96,s0))
    (XP : exec_prog prog ((x,s')::(Addr 0x63ba4,s)::t))
    (UT : unterminated ffs_exit t),
  exists result, ffs_result32 (cdecl_arg s0) result /\ cdecl_returned s0 result x s'.
Proof.
  intros prog EXT s0 t s x s' ENTRY XP UT.
  pose proof (ffs_correct prog EXT s0 t (Addr 0x63ba4,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (ffs_post s0 s) in INV. destruct INV as [FRAME RESULT].
  exists (s R_EAX). split; [exact RESULT|].
  eapply cdecl_ret_step with (p:=prog) (ret:=0x63ba4) (s:=s).
  - apply EXT. reflexivity.
  - split; [reflexivity|exact FRAME].
  - exact (exec_prog_final _ _ _ _ XP).
Qed.
