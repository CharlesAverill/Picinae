(* finitel -- test whether a long double is finite

   SEMANTICS
   ---------
   finitel(x) returns 1 unless x is an infinity or a NaN, i.e. unless the
   15-bit exponent of the x87 extended value is all ones.  glibc computes
   ((se | 0xffff8000) + 1) >> 31 on the 32-bit word holding se: the OR sets
   bits 15..31, so adding 1 carries out of bit 31 exactly when bits 0..14
   (the exponent) are all ones.

   SPECIFICATION (man 3 finite, Linux man-pages 5.10, Ubuntu 22.04)
   ----------------------------------------------------------------

     int finitel(long double x);

     The finite(), finitef(), and finitel() functions return a nonzero
     value if x is neither infinite nor a "not-a-number" (NaN) value, and
     0 otherwise.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol finitel at 0x41090 (Ghidra address 0x141090, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see finitel_amd64.v (global addresses).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   the long double x is passed in memory at RSP+8 (at entry):
            lo = m Ⓓ[8+rsp] and hi = m Ⓓ[12+rsp] are the 64-bit significand
            (bit 31 of hi is the explicit integer bit), se = m Ⓦ[16+rsp] holds
            the sign (bit 15) and the biased exponent (exp80 se = bits 0..14).
   Output:  RAX = finitel_spec se = 0 if exp80 se = 0x7fff, else 1.
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import finitel_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem finitel_nwc: forall s2 s1, finitel_amd64 s1 = finitel_amd64 s2.
Proof. reflexivity. Qed.

Theorem finitel_welltyped: welltyped_prog x64typctx finitel_amd64.
Proof. Picinae_typecheck. Qed.

Theorem finitel_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates finitel_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Definition finitel_spec (se:N) := if exp80 se =? 0x7fff then 0 else 1.

Definition finitel_exit (t:trace) :=
  match t with (Addr 0x1410a2,_)::_ => true | _ => false end.

Definition finitel_invs (m:memory) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x141090 => Some (s V_MEM64 = m /\ s R_RSP = rsp)
  | 0x1410a2 => Some (s R_RAX = finitel_spec (m Ⓦ[16 + rsp]) /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem finitel_correct:
  forall s t s' x' m rsp
         (ENTRY: startof t (x',s') = (Addr 0x141090, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp),
  satisfies_all finitel_amd64 (finitel_invs m rsp) finitel_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply finitel_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM RSP].
  repeat x64_step.
  split. rewrite finitel_bits by apply (getmem_bound 64 LittleE 4).
    unfold finitel_spec, exp80. rewrite getmem_dw_w, mod16_15. reflexivity.
  split; reflexivity || assumption.
Time Qed.
