(* isnanf -- IEEE-754 classification

   SEMANTICS
   ---------
   isnanf(x) returns nonzero iff the float x is a NaN.  glibc computes
   (0x7f800000 - (bits & 0x7fffffff)) >> 31 in 32-bit arithmetic.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     int isnanf(float x);

     isnan() returns a nonzero value if x is a NaN (not a number), and 0
     otherwise.  (isnanf is the float version.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol isnanf at 0x1417d0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isnanf_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x; its low 32 bits are the binary32 pattern.
   Output:  RAX = 1 if x is a NaN (exp32 = 255, man32 <> 0), else 0.
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import isnanf_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem isnanf_nwc: forall s2 s1, isnanf_amd64 s1 = isnanf_amd64 s2.
Proof. reflexivity. Qed.

Theorem isnanf_welltyped: welltyped_prog x64typctx isnanf_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isnanf_preserves_memory:
  forall_endstates isnanf_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isnanf_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isnanf_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition isnanf_exit (t:trace) :=
  match t with (Addr 1316840,_)::_ => true | _ => false end.

Definition isnanf_invs (m:memory) (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1316816 => Some (s R_YMM0 = x /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1316840 => Some (s R_RAX = (if is_nan32 x then 1 else 0) /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem isnanf_correct:
  forall s t s' x' m x rsp
         (ENTRY: startof t (x',s') = (Addr 1316816, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x)  (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) ,
  satisfies_all isnanf_amd64 (isnanf_invs m x rsp) isnanf_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isnanf_welltyped. intro MDL1.
  clear - PRE MDL1 . rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [MEM RSP]].
  repeat x64_step.
  split; [|split; [assumption | exact MEM]].
  rewrite shr_msub32, nan32_iff. reflexivity.
  change (2^31) with 2147483648. lia. apply N.mod_lt. discriminate.
Qed.
