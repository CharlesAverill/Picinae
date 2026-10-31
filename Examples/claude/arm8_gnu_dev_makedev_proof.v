(* gnu_dev_makedev (AArch64 / ARMv8) -- build a device number from major/minor.

   SEMANTICS
   ---------
   gnu_dev_makedev (the makedev() macro) packs a major and a minor ID into a
   dev_t, interleaving their bit-fields as the kernel's new (large) device-number
   encoding prescribes.  The result layout (dev_make) is shared with the amd64
   proof and with arm8_gnu_dev_major / arm8_gnu_dev_minor, which invert it.

   SPECIFICATION (sys/sysmacros.h)
   -------------------------------
     dev_t gnu_dev_makedev(unsigned int major, unsigned int minor);
     __dev_t __gnu_dev_makedev (unsigned int __major, unsigned int __minor)
     {
       return ((__major & 0x00000fffu) <<  8)
            | ((__major & 0xfffff000u) << 32)
            | ((__minor & 0x000000ffu)      )
            | ((__minor & 0xffffff00u) << 12);
     }

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
            symbol gnu_dev_makedev at 0x1e9a20.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Model:   Specification and proof written by Claude Opus 4.8 (claude-opus-4-8),
            an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   W0 = major, W1 = minor (low 32 bits of X0, X1).
   Output:  X0 = dev_make (major mod 2^32) (minor mod 2^32).  Memory and the
            stack pointer are unchanged (leaf function, returns via X30).
 *)

Require Import Picinae_armv8.
Require Import gnu_dev_makedev_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem gnu_dev_makedev_nwc: forall s2 s1, gnu_dev_makedev_arm8 s1 = gnu_dev_makedev_arm8 s2.
Proof. reflexivity. Qed.
Theorem gnu_dev_makedev_welltyped: welltyped_prog arm8typctx gnu_dev_makedev_arm8.
Proof. Picinae_typecheck. Qed.
Theorem gnu_dev_makedev_preserves_memory:
  forall_endstates gnu_dev_makedev_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* The RET is at offset 36. *)
Definition gnu_dev_makedev_exit (t:trace) :=
  match t with (Addr 36,_)::_ => true | _ => false end.

Definition postcondition (maj min:N) (s:store) := s R_X0 = dev_make maj min.

Definition gnu_dev_makedev_invs (maj min:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 = maj /\ s R_X1 = min)
  | 36 => Some (postcondition maj min s)
  | _ => None
  end | _ => None end.

Theorem gnu_dev_makedev_correct:
  forall s t s' x' maj min
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (MAJ: s R_X0 = maj) (MIN: s R_X1 = min),
  satisfies_all gnu_dev_makedev_arm8 (gnu_dev_makedev_invs maj min) gnu_dev_makedev_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply gnu_dev_makedev_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MAJ MIN].
  assert (MJ: s1 R_X0 < 2^64) by (apply (MDL1 R_X0 64); reflexivity).
  assert (MN: s1 R_X1 < 2^64) by (apply (MDL1 R_X1 64); reflexivity).
  repeat arm8_step.
  unfold postcondition. rewrite <- MAJ, <- MIN. unfold dev_make.
  (* the ubfiz lift rotates, so wrap the (64-bit) inputs in mod 2^64 to kill the
     rotate's high-bit leaves. *)
  rewrite <- (N.mod_small (s1 R_X0) (2^64) MJ), <- (N.mod_small (s1 R_X1) (2^64) MN).
  bitblast_upto 64.
Qed.
