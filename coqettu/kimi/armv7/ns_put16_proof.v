(* ns_put16 -- store a 16-bit unsigned integer in network byte order

   SEMANTICS
   ---------
   The implementation writes the low input byte at dst+1 and the next input
   byte at dst, producing the big-endian representation of the low 16 bits.

   SPECIFICATION (BIND resolver library, <arpa/nameser.h>)
   ------------------------------------------------------

     SYNOPSIS
            void ns_put16(unsigned int src, unsigned char *dst);

     DESCRIPTION
            ns_put16 writes the 16-bit unsigned integer src at dst in network
            byte order.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            ns_put16 at ELF VA 0x42f59 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x52f58.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see ns_put16_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = src, R1 = dst, and M is entry memory.  Start at 0x52f58.
   Output:  At BX LR at 0x52f5e, M[dst] = bits 8..15 of src and
            M[dst+1] = bits 0..7 of src; all other memory is unchanged.  R0,
            R1, SP, LR, and all AAPCS callee-saved registers are unchanged.
            The proof stops before BX LR because its mode-switch userop is
            unmodeled.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import ns_put16_armv7.
Import ARM7Notations.
Open Scope N.

Definition ns_put16_entry : addr := 0x52f58.
Definition ns_put16_return : addr := 0x52f5e.

Definition ns_put16_post (s0 s : store) : Prop :=
  s V_MEM32 =
    ((s0 V_MEM32)[Ⓑ(s0 R_R1)⊕1 := (s0 R_R0) mod 2^8])
      [Ⓑs0 R_R1 := ((s0 R_R0) >> 8) mod 2^8] /\
  s R_R0 = s0 R_R0 /\
  s R_R1 = s0 R_R1 /\
  s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR.

Definition ns_put16_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x52f58 => Some (s = s0)
      | 0x52f5e => Some (ns_put16_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition ns_put16_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? ns_put16_return
  | _ => false
  end.

Theorem ns_put16_nwc : forall s1 s2, ns_put16_armv7 s1 = ns_put16_armv7 s2.
Proof. reflexivity. Qed.

Theorem ns_put16_welltyped : welltyped_prog arm7typctx ns_put16_armv7.
Proof. exact welltyped. Qed.

Theorem ns_put16_preserves_lr :
  forall_endstates ns_put16_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem ns_put16_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates ns_put16_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem ns_put16_correct :
  forall prog (EXT : ns_put16_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr ns_put16_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (ns_put16_invs s0) ns_put16_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := ns_put16_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold ns_put16_invs.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - s0 MDL START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply ns_put16_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst s0.
      arm7_step. arm7_step. arm7_step.
      unfold ns_put16_post.
      elimstore.
      repeat split; psimpl; reflexivity.
Qed.
