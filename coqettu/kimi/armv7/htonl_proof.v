(* htonl -- convert a 32-bit value from host to network byte order

   SEMANTICS
   ---------
   ARMv7 musl is little-endian, so htonl reverses the four bytes of its
   argument.  The implementation is one REV instruction followed by BX LR.

   SPECIFICATION (man 3 htonl, Linux man-pages)
   --------------------------------------------

     SYNOPSIS
            #include <arpa/inet.h>
            uint32_t htonl(uint32_t hostlong);

     DESCRIPTION
            The htonl() function converts the unsigned integer hostlong from
            host byte order to network byte order.

     RETURN VALUE
            The htonl() function returns the converted value.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            htonl at ELF VA 0x426dd (Thumb); Ghidra image base 0x10000,
            lifted entry 0x526dc.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see htonl_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = hostlong.  The proof starts at 0x526dc.
   Output:  At the BX LR instruction at 0x526de, R0 = bswap32 hostlong.
            Memory, SP, LR, and all AAPCS callee-saved registers are unchanged.
            Stopping before BX LR keeps the unmodeled ISA-mode-switch userop
            outside the trusted correctness claim.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common htonl_armv7.
Import ARM7Notations.
Open Scope N.

Definition htonl_entry : addr := 0x526dc.
Definition htonl_return : addr := 0x526de.

Definition htonl_post (s0 s : store) : Prop :=
  s R_R0 = bswap32 (s0 R_R0) /\
  s V_MEM32 = s0 V_MEM32 /\
  s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR.

Definition htonl_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x526dc => Some (s = s0)
      | 0x526de => Some (htonl_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition htonl_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? htonl_return
  | _ => false
  end.

Theorem htonl_nwc : forall s1 s2, htonl_armv7 s1 = htonl_armv7 s2.
Proof. reflexivity. Qed.

Theorem htonl_welltyped : welltyped_prog arm7typctx htonl_armv7.
Proof. exact welltyped. Qed.

Theorem htonl_preserves_memory :
  forall_endstates htonl_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem htonl_preserves_lr :
  forall_endstates htonl_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem htonl_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates htonl_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem htonl_correct :
  forall prog (EXT : htonl_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr htonl_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (htonl_invs s0) htonl_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := htonl_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold htonl_invs.
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
        apply htonl_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst s0.
      arm7_step.
      unfold htonl_post, bswap32.
      elimstore.
      repeat split.
      psimpl. rewrite bswap32_low_byte. reflexivity.
Qed.
