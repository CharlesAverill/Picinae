(* cfgetospeed (AArch64 / ARMv8) -- get terminal output baud rate

   Returns c_cflag & (CBAUD|CBAUDEX) = mask 0x100f of the c_cflag field at
   termios_p+8.  On AArch64: `ldr w0,[x0,#8]; mov w1,#0x100f; and w0,w0,w1; ret`.

   PROVENANCE: aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
   (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
   symbol cfgetospeed at 0x1e0ed0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Specification (cfspeed) shared with amd64_cfgetospeed_proof.v.  AArch64 port.
 *)

Require Import Picinae_armv8.
Require Import cfgetospeed_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem cfgetospeed_nwc: forall s2 s1, cfgetospeed_arm8 s1 = cfgetospeed_arm8 s2.
Proof. reflexivity. Qed.

Theorem cfgetospeed_welltyped: welltyped_prog arm8typctx cfgetospeed_arm8.
Proof. Picinae_typecheck. Qed.

Theorem cfgetospeed_preserves_memory:
  forall_endstates cfgetospeed_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition cfspeed (m:memory) (p:N) := m Ⓦ[8 + p] .& 0x100f.  (* c_cflag & (CBAUD|CBAUDEX); the 2-byte load suffices as 0x100f < 2^16 *)

Definition cfgetospeed_exit (t:trace) :=
  match t with (Addr 12,_)::_ => true | _ => false end.

Definition postcondition (m p:N) (s:store) :=
  s R_X0 = cfspeed m p.

Definition cfgetospeed_invs (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_X0 = p)
  | 12 => Some (postcondition m p s)
  | _ => None
  end | _ => None end.

Theorem cfgetospeed_correct:
  forall s t s' x' m p
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = m) (P: s R_X0 = p),
  satisfies_all cfgetospeed_arm8 (cfgetospeed_invs m p) cfgetospeed_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfgetospeed_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM P].
  repeat arm8_step.
  unfold postcondition, cfspeed. reflexivity.
Qed.
