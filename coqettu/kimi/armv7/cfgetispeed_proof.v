(* cfgetispeed -- read the input baud rate from a termios structure

   SEMANTICS
   ---------
   On this musl ARMv7 target, the input speed is encoded in the high halfword
   of c_cflag.  The function loads the halfword at offset 10 and masks it with
   0x100f.

   SPECIFICATION (POSIX cfgetispeed)
   --------------------------------

     SYNOPSIS
            #include <termios.h>
            speed_t cfgetispeed(const struct termios *termios_p);

     DESCRIPTION
            cfgetispeed() returns the input baud rate stored in the termios
            structure pointed to by termios_p.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            cfgetispeed at ELF VA 0x4c555 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5c554.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see cfgetispeed_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = termios_p and M is entry memory.  Start at 0x5c554.
   Output:  At BX LR at 0x5c55c, R0 = M[termios_p+10] bitwise-and 0x100f.
            Memory, SP, LR, and all AAPCS callee-saved registers are unchanged.
            Stopping before BX LR excludes the unmodeled ISA-mode-switch userop.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import cfgetispeed_armv7.
Import ARM7Notations.
Open Scope N.

Definition cfgetispeed_entry : addr := 0x5c554.
Definition cfgetispeed_return : addr := 0x5c55c.

Definition cfgetispeed_post (s0 s : store) : Prop :=
  s R_R0 = ((s0 V_MEM32) Ⓦ[(s0 R_R0)⊕0xa]) .& 0x100f /\
  s V_MEM32 = s0 V_MEM32 /\
  s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR.

Definition cfgetispeed_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5c554 => Some (s = s0)
      | 0x5c55c => Some (cfgetispeed_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition cfgetispeed_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? cfgetispeed_return
  | _ => false
  end.

Theorem cfgetispeed_nwc : forall s1 s2, cfgetispeed_armv7 s1 = cfgetispeed_armv7 s2.
Proof. reflexivity. Qed.

Theorem cfgetispeed_welltyped : welltyped_prog arm7typctx cfgetispeed_armv7.
Proof. exact welltyped. Qed.

Theorem cfgetispeed_preserves_memory :
  forall_endstates cfgetispeed_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem cfgetispeed_preserves_lr :
  forall_endstates cfgetispeed_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem cfgetispeed_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates cfgetispeed_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem cfgetispeed_correct :
  forall prog (EXT : cfgetispeed_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr cfgetispeed_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (cfgetispeed_invs s0) cfgetispeed_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := cfgetispeed_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold cfgetispeed_invs.
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
        apply cfgetispeed_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst s0.
      arm7_step. arm7_step. arm7_step.
      unfold cfgetispeed_post.
      elimstore.
      repeat split; psimpl; reflexivity.
Qed.
