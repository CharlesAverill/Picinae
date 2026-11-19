(* toupper -- musl i386

   SEMANTICS
   ---------
   Convert uppercase ASCII to lowercase (tolower), or the reverse (toupper).
   Other representations are unchanged; memory and the ABI frame are preserved.

   SPECIFICATION (toupper(3), Linux man-pages 6.9.1, 2024-05-02)
   -------------------------------------------------------
     #include <ctype.h>
     int toupper(int c);
   Return the converted letter, or the input unchanged.
   Source: /usr/share/man/man3/toupper.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: toupper, ELF VA 0x3f663; global entry 0x4f663, RET 0x4f66f/0x4f673.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  The 32-bit argument is the word at entry ESP+4.
   Output: EAX is the converted representation; memory, ESP, callee-saved registers
           and access permissions are preserved. RET pops the original address.
   Scope:  Partial correctness for all binary argument representations, stronger
           than C's unsigned-char/EOF domain. No locale table is consulted.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_common i386_bits i386_ascii toupper_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition toupper_spec (c:N) := if ascii_lower c then c-32 else c.
Definition toupper_invs (s0:store) (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x4f663 => Some (s=s0)
  | 0x4f66f | 0x4f673 => Some (cdecl_leaf_post s0 (toupper_spec (cdecl_arg s0)) s)
  | _ => None end | _ => None end.
Definition toupper_exit (t:trace) := (at_address 0x4f66f t || at_address 0x4f673 t)%bool.
Theorem toupper_nwc : forall s1 s2, toupper_i386 s1=toupper_i386 s2.
Proof. reflexivity. Qed.
Theorem toupper_preserves_memory :
  forall_endstates toupper_i386 (fun _ s _ s' => s V_MEM32=s' V_MEM32).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Theorem toupper_preserves_callee_saved : forall v, List.In v cdecl_saved ->
  forall_endstates toupper_i386 (fun _ s _ s' => s v=s' v).
Proof. prove_cdecl_saved. Qed.
Theorem toupper_correct_local : forall s0 t xs
  (ENTRY:startof t xs=(Addr 0x4f663,s0)),
  satisfies_all toupper_i386 (toupper_invs s0) toupper_exit (xs::t).
Proof.
  intros s0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE. destruct_inv 32 PRE.
    subst s. repeat x86_step.
    all: unfold cdecl_leaf_post, cdecl_leaf_frame; psimpl.
    all: split; [|repeat split; reflexivity].
    all: fold (cdecl_arg s0) in *.
    all: assert (B: cdecl_arg s0<2^32) by (unfold cdecl_arg; apply getmem_bound).
    all: rewrite (ascii_lower_test (cdecl_arg s0) B) in BC.
    all: fold (ascii_lower (cdecl_arg s0)) in BC.
    all: destruct (ascii_lower (cdecl_arg s0)) eqn:CASE; cbn in BC; try discriminate.
    all: unfold toupper_spec; rewrite CASE.
    all: try reflexivity.
    assert (BYTE : cdecl_arg s0 mod 256 = getmem 32 LittleE 1 (s0 V_MEM32) (4+s0 R_ESP)).
    { unfold cdecl_arg. exact (getmem_mod 32 LittleE 1 4 (s0 V_MEM32) (4+s0 R_ESP)). }
    rewrite <- BYTE.
    change (N.land (cdecl_arg s0 mod 2^8) 95 = cdecl_arg s0-32).
    rewrite <- N.land_ones, <- N.land_assoc.
    change (N.land (cdecl_arg s0) 95 = cdecl_arg s0-32).
    apply uppercase_and95. exact CASE.
Qed.
Theorem toupper_correct : forall prog (EXT:toupper_i386 ⊆2 prog) s0 t xs
  (ENTRY:startof t xs=(Addr 0x4f663,s0)),
  satisfies_all prog (toupper_invs s0) toupper_exit (xs::t).
Proof.
  intros prog EXT s0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold toupper_invs, toupper_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply toupper_correct_local. rewrite START. exact ENTRY.
Qed.
Theorem toupper_returns : forall prog (EXT:toupper_i386 ⊆2 prog) s0 t s x s' ret
  (RET:ret=0x4f66f \/ ret=0x4f673)
  (ENTRY:startof t (Addr ret,s)=(Addr 0x4f663,s0))
  (XP:exec_prog prog ((x,s')::(Addr ret,s)::t)) (UT:unterminated toupper_exit t),
  cdecl_returned s0 (toupper_spec (cdecl_arg s0)) x s'.
Proof.
  intros prog EXT s0 t s x s' ret RET ENTRY XP UT.
  pose proof (toupper_correct prog EXT s0 t (Addr ret,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  destruct RET as [EQ|EQ]; subst ret.
  - eapply cdecl_ret_step with (ret:=0x4f66f) (s:=s);
      [apply EXT; reflexivity|exact INV|exact (exec_prog_final _ _ _ _ XP)].
  - eapply cdecl_ret_step with (ret:=0x4f673) (s:=s);
      [apply EXT; reflexivity|exact INV|exact (exec_prog_final _ _ _ _ XP)].
Qed.
