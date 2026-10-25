(* isnan -- IEEE-754 classification

   SEMANTICS
   ---------
   isnan(x) returns nonzero iff x is a NaN.  glibc tests the bit pattern of
   the double in XMM0 with integer arithmetic: with a = bits & ~sign,
   (0x7ff0000000000000 - a) >> 63 is 1 exactly when a exceeds +inf's pattern,
   that is when the exponent is all ones and the mantissa is nonzero.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     int isnan(double x);

     isnan() returns a nonzero value if x is a NaN (not a number), and 0
     otherwise.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol isnan at 0x1413d0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isnan_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x; its low 64 bits are the binary64 pattern.
   Output:  RAX = 1 if x is a NaN (exp64 = 2047, man64 <> 0), else 0.
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import isnan_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem isnan_nwc: forall s2 s1, isnan_amd64 s1 = isnan_amd64 s2.
Proof. reflexivity. Qed.

Theorem isnan_welltyped: welltyped_prog x64typctx isnan_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isnan_preserves_memory:
  forall_endstates isnan_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isnan_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isnan_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition isnan_exit (t:trace) :=
  match t with (Addr 1315823,_)::_ => true | _ => false end.

Definition isnan_invs (m:memory) (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1315792 => Some (s R_YMM0 = x /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1315823 => Some (s R_RAX = (if is_nan64 x then 1 else 0) /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem isnan_correct:
  forall s t s' x' m x rsp
         (ENTRY: startof t (x',s') = (Addr 1315792, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x)  (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) ,
  satisfies_all isnan_amd64 (isnan_invs m x rsp) isnan_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isnan_welltyped. intro MDL1.
  clear - PRE MDL1 . rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [MEM RSP]].
  repeat x64_step.
  split; [|split; [assumption | exact MEM]].
  rewrite shr_msub64, nan64_iff. reflexivity.
  change (2^63) with 9223372036854775808. lia. apply N.mod_lt. discriminate.
Qed.
