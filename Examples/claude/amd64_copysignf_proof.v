(* copysignf -- copy sign

   SEMANTICS
   ---------
   copysignf(x, y) returns a float with the magnitude of x and the sign of
   y.  glibc loads mask = 0x7fffffff (MOVSS, upper lanes zero), ANDs it
   into XMM0, ANDNs it into XMM1 and ORs the two.  The mask lives in
   .rodata; the theorem takes its value as a precondition on memory.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     float copysignf(float x, float y);

     These functions return a value whose absolute value matches that of x,
     but whose sign bit matches that of y.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol copysignf at 0x141810 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see copysignf_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x, XMM1 holds y; memory m holds 0x7fffffff at
            0x2cc880 (read-only data).
   Output:  the low 32 bits of YMM0 are (x & 0x7fffffff) | (y & 0x80000000):
            bits 0-30 of x and bit 31 of y.  (Bits 32 and up come from y,
            since ANDNPS complements the mask's zero upper lanes.)  RSP and
            memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import copysignf_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem copysignf_nwc: forall s2 s1, copysignf_amd64 s1 = copysignf_amd64 s2.
Proof. reflexivity. Qed.

Theorem copysignf_welltyped: welltyped_prog x64typctx copysignf_amd64.
Proof. Picinae_typecheck. Qed.

Theorem copysignf_preserves_memory:
  forall_endstates copysignf_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem copysignf_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates copysignf_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition copysignf_exit (t:trace) :=
  match t with (Addr 1316901,_)::_ => true | _ => false end.

Definition copysignf_invs (m:memory) (x y rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1316880 => Some (s R_YMM0 = x /\ s R_YMM1 = y /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1316901 => Some (s R_YMM0 mod 2^32 = x .& 0x7fffffff .| y .& 0x80000000 /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem copysignf_correct:
  forall s t s' x' m x y rsp
         (ENTRY: startof t (x',s') = (Addr 1316880, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x) (Y: s R_YMM1 = y) (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) (MK: m Ⓓ[0x2cc880] = 0x7fffffff),
  satisfies_all copysignf_amd64 (copysignf_invs m x y rsp) copysignf_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply copysignf_welltyped. intro MDL1.
  clear - PRE MDL1 MK. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [Y [MEM RSP]]].
  repeat x64_step.
  rewrite MK. split; [|split; first [reflexivity | assumption]].
  change (N.lnot 2147483647 32) with (2^31). change 2147483647 with (N.ones 31).
  rewrite N.land_ones, (N.land_comm (2^31) y). reflexivity.
Qed.
