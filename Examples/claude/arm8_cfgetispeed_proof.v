(* cfgetispeed (AArch64 / ARMv8) -- get terminal input baud rate.
   `ldr w1,[x0]; tbnz w1,#31,L; ldr w0,[x0,#8]; and w0,w0,#0x100f; ret | L: mov w0,#0; ret`.
   If IBAUD0 (bit 31 of c_iflag) is set, returns 0; else c_cflag & (CBAUD|CBAUDEX).
   Spec (cfispeed) shared with amd64_cfgetispeed_proof.v.  AArch64 glibc port.
   PROVENANCE: aarch64 libc.so.6 glibc 2.35-0ubuntu3.15, symbol cfgetispeed at 0x1e0ee0. *)

Require Import Picinae_armv8.
Require Import cfgetispeed_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem cfgetispeed_nwc: forall s2 s1, cfgetispeed_arm8 s1 = cfgetispeed_arm8 s2.
Proof. reflexivity. Qed.
Theorem cfgetispeed_welltyped: welltyped_prog arm8typctx cfgetispeed_arm8.
Proof. Picinae_typecheck. Qed.
Theorem cfgetispeed_preserves_memory:
  forall_endstates cfgetispeed_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* IBAUD0 = bit 31 of c_iflag; `m Ⓓ[p] >> 31 =? 0' is IBAUD0 clear (equivalently
   negb (N.testbit (m Ⓓ[p]) 31), the amd64 form, since the field is 32-bit). *)
Definition cfispeed (m:memory) (p:N) :=
  if m Ⓓ[p] >> 31 =? 0 then m Ⓦ[8 + p] .& 0x100f else 0.

Definition cfgetispeed_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 20 | 28 => true | _ => false end | _ => false end.

Definition postcondition (m p:N) (s:store) := s R_X0 = cfispeed m p.

Definition cfgetispeed_invs (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_X0 = p)
  | 20 | 28 => Some (postcondition m p s)
  | _ => None
  end | _ => None end.

Theorem cfgetispeed_correct:
  forall s t s' x' m p
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = m) (P: s R_X0 = p),
  satisfies_all cfgetispeed_arm8 (cfgetispeed_invs m p) cfgetispeed_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfgetispeed_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM P].
  repeat arm8_step.
  all: unfold postcondition, cfispeed.
  all: rewrite BC; reflexivity.
Qed.
