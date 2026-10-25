(* finitef -- IEEE-754 classification

   SEMANTICS
   ---------
   finitef(x) returns nonzero iff the float x is neither infinite nor a
   NaN.  glibc spills XMM0 to [rsp-4] and computes
   ((bits & 0x7f800000) - 0x7f800000) >> 31 in 32-bit arithmetic.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     int finitef(float x);

     The finite() functions return a nonzero value if x is neither infinite
     nor a "not-a-number" (NaN) value, and 0 otherwise.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol finitef at 0x1417f0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see finitef_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x; its low 32 bits are the binary32 pattern.
   Output:  RAX = 1 if exp32 x <> 255, else 0.  RSP is unchanged; memory
            equals m except that the 4 bytes below RSP hold the bits of x.
 *)

Require Import Picinae_amd64.
Require Import finitef_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem finitef_nwc: forall s2 s1, finitef_amd64 s1 = finitef_amd64 s2.
Proof. reflexivity. Qed.

Theorem finitef_welltyped: welltyped_prog x64typctx finitef_amd64.
Proof. Picinae_typecheck. Qed.

Theorem finitef_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates finitef_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition finitef_exit (t:trace) :=
  match t with (Addr 1316875,_)::_ => true | _ => false end.

Definition finitef_invs (m:memory) (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1316848 => Some (s R_YMM0 = x /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1316875 => Some (s R_RAX = (if is_finite32 x then 1 else 0) /\ s R_RSP = rsp /\ s V_MEM64 = m [Ⓓ rsp ⊖ 4 := x])
  | _ => None
  end | _ => None end.

Theorem finitef_correct:
  forall s t s' x' m x rsp
         (ENTRY: startof t (x',s') = (Addr 1316848, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x)  (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) ,
  satisfies_all finitef_amd64 (finitef_invs m x rsp) finitef_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply finitef_welltyped. intro MDL1.
  clear - PRE MDL1 . rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [MEM RSP]].
  repeat x64_step.
  split; [|split; [first [reflexivity | assumption] | first [reflexivity | assumption]]].
  rewrite shr_msub32, finite32_iff. reflexivity.
  eapply N.le_lt_trans. apply N.land_le_r. reflexivity. reflexivity.
Qed.
