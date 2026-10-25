(* finite -- IEEE-754 classification

   SEMANTICS
   ---------
   finite(x) returns nonzero iff x is neither infinite nor a NaN, that is
   iff its exponent field is not all ones.  glibc spills XMM0 to the red zone
   at [rsp-8] and computes ((bits & 0x7ff0000000000000) - 0x7ff0000000000000)
   >> 63.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     int finite(double x);

     The finite() functions return a nonzero value if x is neither infinite
     nor a "not-a-number" (NaN) value, and 0 otherwise.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol finite at 0x1413f0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see finite_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x; its low 64 bits are the binary64 pattern.
   Output:  RAX = 1 if exp64 x <> 2047, else 0.  RSP is unchanged; memory
            equals m except that the 8 bytes below RSP (the red zone) hold
            the bits of x.
 *)

Require Import Picinae_amd64.
Require Import finite_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem finite_nwc: forall s2 s1, finite_amd64 s1 = finite_amd64 s2.
Proof. reflexivity. Qed.

Theorem finite_welltyped: welltyped_prog x64typctx finite_amd64.
Proof. Picinae_typecheck. Qed.

Theorem finite_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates finite_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition finite_exit (t:trace) :=
  match t with (Addr 1315859,_)::_ => true | _ => false end.

Definition finite_invs (m:memory) (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1315824 => Some (s R_YMM0 = x /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1315859 => Some (s R_RAX = (if is_finite64 x then 1 else 0) /\ s R_RSP = rsp /\ s V_MEM64 = m [Ⓠ rsp ⊖ 8 := x])
  | _ => None
  end | _ => None end.

Theorem finite_correct:
  forall s t s' x' m x rsp
         (ENTRY: startof t (x',s') = (Addr 1315824, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x)  (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) ,
  satisfies_all finite_amd64 (finite_invs m x rsp) finite_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply finite_welltyped. intro MDL1.
  clear - PRE MDL1 . rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [MEM RSP]].
  repeat x64_step.
  split; [|split; [first [reflexivity | assumption] | first [reflexivity | assumption]]].
  rewrite shr_msub64, finite64_iff. reflexivity.
  eapply N.le_lt_trans. apply N.land_le_r. reflexivity. reflexivity.
Qed.
(* This Qed used to hang: the carry flag of SUB RAX,RDX is
   (if x .& 0x7ff0000000000000 <? 0x7ff0000000000000 then 1 else 0), and the
   kernel unfolded Pos.compare_cont over the 64-bit literal.  The Strategy
   hint in Picinae_core.v fixes it (Qed now takes about 3 s). *)
