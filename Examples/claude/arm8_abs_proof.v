(* abs (AArch64 / ARMv8) -- absolute value of an int.  `cmp w0,#0; cneg w0,w0,lt; ret`.
   Spec shared with amd64_abs_proof.v (X0 = |j| mod 2^32).  AArch64 glibc port;
   32-bit analogue of arm8_labs, using the shared arm8_common normalization lemmas.
   PROVENANCE: aarch64 libc.so.6 glibc 2.35-0ubuntu3.15 (sha256 79fd4eca…dff06),
   symbol abs at 0x13d810; Ghidra 11.4.2 + pcode2coq. *)

Require Import Picinae_armv8.
Require Import abs_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith List.
Import ListNotations.
Open Scope N.

Theorem abs_nwc: forall s2 s1, abs_arm8 s1 = abs_arm8 s2.
Proof. reflexivity. Qed.
Theorem abs_welltyped: welltyped_prog arm8typctx abs_arm8.
Proof. Picinae_typecheck. Qed.
Theorem abs_preserves_memory:
  forall_endstates abs_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition abs_exit (t:trace) := match t with (Addr 8,_)::_ => true | _ => false end.
Definition postcondition (j:Z) (s:store) := s R_X0 = ofZ 32 (Z.abs j).
Definition abs_invs (j:Z) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_X0) = j)
  | 8 => Some (postcondition j s)
  | _ => None
  end | _ => None end.

Theorem abs_correct:
  forall s t s' x' j
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (J: toZ 32 (s R_X0) = j),
  satisfies_all abs_arm8 (abs_invs j) abs_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply abs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into J.
  pose proof (cneg_abs 32 (s1 R_X0)) as [LM1 LM2]. rewrite J in LM1, LM2.
  repeat arm8_step.
  all: unfold postcondition.
  all: rewrite N.shiftr_0_r, msub_0_r, mp2_mod_mod, slt_mod in BC.
  - destruct (slt 32 (s1 R_X0) 0) eqn:SL; [ apply LM1; reflexivity | cbn in BC; discriminate ].
  - destruct (slt 32 (s1 R_X0) 0) eqn:SL; [ cbn in BC; discriminate | apply LM2; reflexivity ].
Qed.
