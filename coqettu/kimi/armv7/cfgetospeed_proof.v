(* cfgetospeed -- read the output baud rate from a termios structure

   SEMANTICS
   ---------
   On this musl ARMv7 target, the output speed is encoded in the c_cflag word
   at offset 8.  The function loads that word and masks it with 0x100f.

   SPECIFICATION (POSIX cfgetospeed)
   --------------------------------

     SYNOPSIS
            #include <termios.h>
            speed_t cfgetospeed(const struct termios *termios_p);

     DESCRIPTION
            cfgetospeed() returns the output baud rate stored in the termios
            structure pointed to by termios_p.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            cfgetospeed at ELF VA 0x4c54b (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5c54a.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see cfgetospeed_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = termios_p and M is entry memory.  Start at 0x5c54a.
   Output:  At BX LR at 0x5c552, R0 = M[termios_p+8] bitwise-and 0x100f.
            Memory, SP, LR, and all AAPCS callee-saved registers are unchanged.
            Stopping before BX LR excludes the unmodeled ISA-mode-switch userop.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import cfgetospeed_armv7.
Import ARM7Notations.
Open Scope N.

Definition cfgetospeed_entry : addr := 0x5c54a.
Definition cfgetospeed_return : addr := 0x5c552.

Definition cfgetospeed_post (s0 s : store) : Prop :=
  s R_R0 = ((s0 V_MEM32) Ⓓ[(s0 R_R0)⊕8]) .& 0x100f /\
  s V_MEM32 = s0 V_MEM32 /\
  s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR.

Definition cfgetospeed_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5c54a => Some (s = s0)
      | 0x5c552 => Some (cfgetospeed_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition cfgetospeed_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? cfgetospeed_return
  | _ => false
  end.

Theorem cfgetospeed_nwc : forall s1 s2, cfgetospeed_armv7 s1 = cfgetospeed_armv7 s2.
Proof. reflexivity. Qed.

Theorem cfgetospeed_welltyped : welltyped_prog arm7typctx cfgetospeed_armv7.
Proof. exact welltyped. Qed.

Theorem cfgetospeed_preserves_memory :
  forall_endstates cfgetospeed_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem cfgetospeed_preserves_lr :
  forall_endstates cfgetospeed_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem cfgetospeed_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates cfgetospeed_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem cfgetospeed_correct :
  forall prog (EXT : cfgetospeed_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr cfgetospeed_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (cfgetospeed_invs s0) cfgetospeed_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := cfgetospeed_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold cfgetospeed_invs.
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
        apply cfgetospeed_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst s0.
      arm7_step. arm7_step. arm7_step.
      unfold cfgetospeed_post.
      elimstore.
      repeat split; psimpl; reflexivity.
Qed.
