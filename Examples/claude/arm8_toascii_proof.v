(* toascii (AArch64 / ARMv8) -- convert character to ASCII

   SEMANTICS
   ---------
   toascii clears every bit of its int argument except the low 7, producing a
   value in [0, 127].  On AArch64 this is a single `and w0, w0, #0x7f` followed
   by `ret` (return address in the link register X30; no stack frame).

   SPECIFICATION (man 3 toascii, Linux man-pages, Ubuntu 22.04)
   ------------------------------------------------------------
     int toascii(int c);
     toascii() converts c to a 7-bit unsigned char value that fits into the
     ASCII character set, by clearing the high-order bits.  The value returned
     is that of the converted character.

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (Ubuntu 22.04 ports), sha256
            79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
            symbol toascii at 0x134460.
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq; see toascii_arm8.v.
   Model:   Specification and proof written by Claude Opus 4.8
            (claude-opus-4-8), an AI model by Anthropic, machine-checked by Rocq.
   Note:    First function of the AArch64 glibc port.  The specification is the
            same as the x86-64 proof (amd64_toascii_proof.v); only the lifted
            body, the argument/return register (W0/X0 under AAPCS64), and the
            step tactic differ.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   W0 (low 32 bits of X0) holds c.
   Output:  On return, X0 = c & 0x7f; in particular it lies in [0, 127].
            Memory is not modified; no callee-saved register is modified.
 *)

Require Import Picinae_armv8.
Require Import toascii_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem toascii_nwc: forall s2 s1, toascii_arm8 s1 = toascii_arm8 s2.
Proof. reflexivity. Qed.

Theorem toascii_welltyped: welltyped_prog arm8typctx toascii_arm8.
Proof. Picinae_typecheck. Qed.

Theorem toascii_preserves_memory:
  forall_endstates toascii_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem toascii_preserves_callee_saved:
  forall v, In v [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25; R_X26; R_X27; R_X28] ->
  forall_endstates toascii_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 4. *)
Definition toascii_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 4 => true
  | _ => false
  end | _ => false end.

Definition postcondition (c:N) (s:store) :=
  s R_X0 = c .& 127.

Definition toascii_invs (c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 mod 2^32 = c)
  | 4 => Some (postcondition c s)
  | _ => None
  end | _ => None end.

Theorem toascii_correct:
  forall s t s' x' c
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (C: s R_X0 mod 2^32 = c),
  satisfies_all toascii_arm8 (toascii_invs c) toascii_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply toascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into C.
  repeat arm8_step.
  unfold postcondition.
  rewrite <- C, N_mod_mod_pow by discriminate. reflexivity.
Qed.
