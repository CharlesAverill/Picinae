(* copysign -- copy sign

   SEMANTICS
   ---------
   copysign(x, y) returns a value with the magnitude of x and the sign of
   y.  glibc ANDs XMM0 with othermask (0x7fffffffffffffff in its low
   quadword) and XMM1 with signmask (0x8000000000000000), then ORs them.
   The masks live in .rodata; the theorem takes their values as a
   precondition on memory.

   SPECIFICATION (Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------

     double copysign(double x, double y);

     These functions return a value whose absolute value matches that of x,
     but whose sign bit matches that of y.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol copysign at 0x141420 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see copysign_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   XMM0 holds x, XMM1 holds y; memory m holds othermask at
            0x2e2090 and signmask at 0x2e2080 (read-only data).
   Output:  the low 64 bits of YMM0 are (x & 0x7fffffffffffffff) |
            (y & 0x8000000000000000): bits 0-62 of x and bit 63 of y.  RSP and
            memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import copysign_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem copysign_nwc: forall s2 s1, copysign_amd64 s1 = copysign_amd64 s2.
Proof. reflexivity. Qed.

Theorem copysign_welltyped: welltyped_prog x64typctx copysign_amd64.
Proof. Picinae_typecheck. Qed.

Theorem copysign_preserves_memory:
  forall_endstates copysign_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem copysign_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates copysign_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition copysign_exit (t:trace) :=
  match t with (Addr 1315896,_)::_ => true | _ => false end.

Definition copysign_invs (m:memory) (x y rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1315872 => Some (s R_YMM0 = x /\ s R_YMM1 = y /\ s V_MEM64 = m /\ s R_RSP = rsp)
  | 1315896 => Some (s R_YMM0 mod 2^64 = x .& 0x7fffffffffffffff .| y .& 0x8000000000000000 /\ s R_RSP = rsp /\ s V_MEM64 = m)
  | _ => None
  end | _ => None end.

Theorem copysign_correct:
  forall s t s' x' m x y rsp
         (ENTRY: startof t (x',s') = (Addr 1315872, s))
         (MDL: models x64typctx s)
         (X: s R_YMM0 = x) (Y: s R_YMM1 = y) (MEM: s V_MEM64 = m) (RSP: s R_RSP = rsp) (OM: m Ⓠ[0x2e2090] = 0x7fffffffffffffff) (SM: m Ⓠ[0x2e2080] = 0x8000000000000000),
  satisfies_all copysign_amd64 (copysign_invs m x y rsp) copysign_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply copysign_welltyped. intro MDL1.
  clear - PRE MDL1 OM SM. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [X [Y [MEM RSP]]].
  repeat x64_step.
  rewrite OM, SM. split; [|split; first [reflexivity | assumption]].
  change 9223372036854775807 with (N.ones 63). rewrite N.land_ones. reflexivity.
Qed.
