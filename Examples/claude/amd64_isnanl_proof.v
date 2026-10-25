(* isnanl -- test whether a long double is a NaN

   SEMANTICS
   ---------
   isnanl(x) is nonzero for a NaN: exponent all ones and a nonzero fraction
   (the significand without its integer bit).  glibc also returns nonzero
   for x87 "unnormals": a nonzero exponent with the explicit integer bit
   clear.  The CPU rejects those encodings as invalid operands, so glibc
   classes them with NaNs.  The function computes, without branches,
     ((-(2e) & ~hi) >> 31) | ((0xfffe - (2e | f)) >> 16)
   where e = exp80 se and f = [fraction <> 0].  The first term is 1 for an
   unnormal; the second is 0xffff for a NaN (or pseudo-NaN).

   SPECIFICATION (man 3 isnan, Linux man-pages 5.10, Ubuntu 22.04)
   ---------------------------------------------------------------

     int isnanl(long double x);

     The isnan() functions return a nonzero value if x is a NaN, and 0
     otherwise.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol isnanl at 0x41040 (Ghidra address 0x141040, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isnanl_amd64.v (global addresses).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   the long double x is passed in memory at RSP+8 (at entry):
            lo = m Ⓓ[8+rsp] and hi = m Ⓓ[12+rsp] are the 64-bit significand
            (bit 31 of hi is the explicit integer bit), se = m Ⓦ[16+rsp] holds
            the sign (bit 15) and the biased exponent (exp80 se = bits 0..14).
   Output:  RAX = isnanl_spec lo hi se (amd64_ieee.v):
              (1 if exp80 se <> 0 and bit 31 of hi is clear, else 0)
            | (0xffff if exp80 se = 0x7fff and (hi mod 2^31 | lo) <> 0, else 0).
            So RAX <> 0 exactly for NaNs, pseudo-NaNs and unnormals.
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import isnanl_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem isnanl_nwc: forall s2 s1, isnanl_amd64 s1 = isnanl_amd64 s2.
Proof. reflexivity. Qed.

Theorem isnanl_welltyped: welltyped_prog x64typctx isnanl_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isnanl_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isnanl_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.


Definition isnanl_exit (t:trace) :=
  match t with (Addr 0x141086,_)::_ => true | _ => false end.

Definition isnanl_invs (m:memory) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x141040 => Some (s V_MEM64 = m /\ s R_RSP = rsp)
  | 0x141086 => Some (s R_RAX = isnanl_spec (m Ⓓ[8 + rsp]) (m Ⓓ[12 + rsp]) (m Ⓦ[16 + rsp]) /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem isnanl_correct:
  forall s t s' x' m rsp
         (ENTRY: startof t (x',s') = (Addr 0x141040, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp),
  satisfies_all isnanl_amd64 (isnanl_invs m rsp) isnanl_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isnanl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM RSP].
  repeat x64_step.
  split. apply isnanl_bits; apply (getmem_bound 64 LittleE 4).
  split; reflexivity || assumption.
Time Qed.
