(* mbsinit (AArch64 / ARMv8) -- test for the initial multibyte conversion state

   Returns nonzero iff ps is NULL or *ps (the 4-byte __count field) is 0.
   On AArch64: `cbz x0,L; ldr w0,[x0]; cmp w0,#0; cset w0,eq; ret | L: mov w0,#1; ret`.

   PROVENANCE: aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
   (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
   symbol mbsinit at 0x19d6d0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Specification (mbsinit_result) shared with amd64_mbsinit_proof.v.
   AArch64 glibc port; demonstrates a memory load.
 *)

Require Import Picinae_armv8.
Require Import mbsinit_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem mbsinit_nwc: forall s2 s1, mbsinit_arm8 s1 = mbsinit_arm8 s2.
Proof. reflexivity. Qed.

Theorem mbsinit_welltyped: welltyped_prog arm8typctx mbsinit_arm8.
Proof. Picinae_typecheck. Qed.

Theorem mbsinit_preserves_memory:
  forall_endstates mbsinit_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition mbsinit_result (m:memory) (ps:N) :=
  if ps =? 0 then 1 else if m Ⓓ[ps] =? 0 then 1 else 0.

Definition mbsinit_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 16 | 24 => true
  | _ => false
  end | _ => false end.

Definition postcondition (m ps:N) (s:store) :=
  s R_X0 = mbsinit_result m ps.

Definition mbsinit_invs (m ps:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_X0 = ps)
  | 16 | 24 => Some (postcondition m ps s)
  | _ => None
  end | _ => None end.

Theorem mbsinit_correct:
  forall s t s' x' m ps
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = m) (PS: s R_X0 = ps),
  satisfies_all mbsinit_arm8 (mbsinit_invs m ps) mbsinit_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply mbsinit_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM PS].
  repeat arm8_step.
  all: unfold postcondition, mbsinit_result; rewrite BC; reflexivity.
Qed.
