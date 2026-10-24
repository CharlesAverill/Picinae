(* gnu_dev_makedev -- build a device number from major and minor IDs

   SEMANTICS
   ---------
   gnu_dev_makedev (the makedev() macro) combines a major and a minor ID into a device ID.
   glibc's 64-bit dev_t encoding is
     makedev(maj, min) = (min & 0xff)        | ((maj & 0xfff) << 8)
                       | ((min & ~0xff) << 12) | ((maj & ~0xfff) << 32)
     major(dev) = ((dev >> 8) & 0xfff)  | ((dev >> 32) & ~0xfff)
     minor(dev) = (dev & 0xff)          | ((dev >> 12) & ~0xff)
   with 32-bit unsigned int maj, min and results.  The definitions dev_make,
   dev_major and dev_minor in amd64_common.v state this encoding.
   Corollary (dev_make_inj): makedev is injective on 32-bit inputs, so
   distinct (maj, min) pairs yield distinct device IDs.

   SPECIFICATION (man 3 makedev, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <sys/sysmacros.h>
            dev_t makedev(unsigned int maj, unsigned int min);
            unsigned int major(dev_t dev);
            unsigned int minor(dev_t dev);

     DESCRIPTION
            A device ID consists of two parts: a major ID, identifying the class of
            the device, and a minor ID, identifying a specific instance of a device
            in that class.  A device ID is represented using the type dev_t.

            Given major and minor device IDs, makedev() combines these to produce a
            device ID, returned as the function result.  This  device  ID  can  be
            given to mknod(2), for example.

            The  major()  and  minor() functions perform the converse task: given a
            device ID, they return, respectively, the major and  minor  components.

     (In glibc, the major, minor and makedev macros expand to calls of
      gnu_dev_major, gnu_dev_minor and gnu_dev_makedev.)

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol gnu_dev_makedev at 0x225500 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see gnu_dev_makedev_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI = maj, ESI = min (unsigned int; the upper halves of RDI and
            RSI are ignored).
   Output:  On return, RAX = dev_make (maj mod 2^32) (min mod 2^32), the dev_t result.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import gnu_dev_makedev_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem gnu_dev_makedev_nwc: forall s2 s1, gnu_dev_makedev_amd64 s1 = gnu_dev_makedev_amd64 s2.
Proof. reflexivity. Qed.

Theorem gnu_dev_makedev_welltyped: welltyped_prog x64typctx gnu_dev_makedev_amd64.
Proof. Picinae_typecheck. Qed.

Theorem gnu_dev_makedev_preserves_memory:
  forall_endstates gnu_dev_makedev_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem gnu_dev_makedev_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates gnu_dev_makedev_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 71. *)
Definition gnu_dev_makedev_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 71 => true
  | _ => false
  end | _ => false end.

Definition postcondition (maj min rsp:N) (s:store) :=
  s R_RAX = dev_make maj min /\ s R_RSP = rsp.

Definition gnu_dev_makedev_invs (maj min rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI mod 2^32 = maj /\ s R_RSI mod 2^32 = min /\ s R_RSP = rsp)
  | 71 => Some (postcondition maj min rsp s)
  | _ => None
  end | _ => None end.

Theorem gnu_dev_makedev_correct:
  forall s t s' x' maj min rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MAJ: s R_RDI mod 2^32 = maj) (MIN: s R_RSI mod 2^32 = min) (RSP: s R_RSP = rsp),
  satisfies_all gnu_dev_makedev_amd64 (gnu_dev_makedev_invs maj min rsp) gnu_dev_makedev_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply gnu_dev_makedev_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MAJ [MIN RSP]].
  repeat x64_step.
  split; [|assumption]. rewrite <- MAJ, <- MIN. unfold dev_make. bitblast_upto 64.
Qed.

Theorem dev_make_inj:
  forall a b c d, a < 2^32 -> b < 2^32 -> c < 2^32 -> d < 2^32 ->
  dev_make a b = dev_make c d -> a = c /\ b = d.
Proof.
  intros a b c d A B C D EQ. split.
    rewrite <- (N.mod_small a (2^32)), <- (N.mod_small c (2^32)) by assumption.
    rewrite <- (dev_major_make a b), <- (dev_major_make c d), EQ. reflexivity.
    rewrite <- (N.mod_small b (2^32)), <- (N.mod_small d (2^32)) by assumption.
    rewrite <- (dev_minor_make a b), <- (dev_minor_make c d), EQ. reflexivity.
Qed.
