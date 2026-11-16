(* ntohs -- convert a 16-bit value from network to host byte order

   SEMANTICS
   ---------
   ARMv7 musl is little-endian.  REV16 reverses the bytes in each halfword and
   UXTH then selects the low halfword, yielding the byte reversal of the low
   16 input bits.

   SPECIFICATION (man 3 ntohs, Linux man-pages)
   --------------------------------------------

     SYNOPSIS
            #include <arpa/inet.h>
            uint16_t ntohs(uint16_t netshort);

     DESCRIPTION
            The ntohs() function converts the unsigned integer netshort from
            network byte order to host byte order.

     RETURN VALUE
            The ntohs() function returns the converted value.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            ntohs at ELF VA 0x431e3 (Thumb); Ghidra image base 0x10000,
            lifted entry 0x531e2.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see ntohs_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = netshort in its low 16 bits.  The proof starts at 0x531e2.
   Output:  At the BX LR instruction at 0x531e6, R0 = bswap16 netshort,
            zero-extended to 32 bits.  Memory, SP, LR, and all AAPCS
            callee-saved registers are unchanged.  Stopping before BX LR keeps
            the unmodeled ISA-mode-switch userop outside the correctness claim.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import armv7_common ntohs_armv7.
Import ARM7Notations.
Open Scope N.

Definition ntohs_entry : addr := 0x531e2.
Definition ntohs_return : addr := 0x531e6.

Definition ntohs_post (s0 s : store) : Prop :=
  s R_R0 = bswap16 (s0 R_R0) /\
  s V_MEM32 = s0 V_MEM32 /\
  s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR.

Definition ntohs_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x531e2 => Some (s = s0)
      | 0x531e6 => Some (ntohs_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition ntohs_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? ntohs_return
  | _ => false
  end.

Theorem ntohs_nwc : forall s1 s2, ntohs_armv7 s1 = ntohs_armv7 s2.
Proof. reflexivity. Qed.

Theorem ntohs_welltyped : welltyped_prog arm7typctx ntohs_armv7.
Proof. exact welltyped. Qed.

Theorem ntohs_preserves_memory :
  forall_endstates ntohs_armv7 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem ntohs_preserves_lr :
  forall_endstates ntohs_armv7 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem ntohs_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 | R_SP => true
    | _ => false
    end = true ->
    forall_endstates ntohs_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem ntohs_correct :
  forall prog (EXT : ntohs_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr ntohs_entry, s0))
         (MDL : models arm7typctx s0),
    satisfies_all prog (ntohs_invs s0) ntohs_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL.
  eapply satisfies_all_pmono with (p1 := ntohs_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold ntohs_invs.
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
        apply ntohs_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.
      simpl in PRE. subst s0.
      arm7_step. arm7_step.
      unfold ntohs_post.
      elimstore.
      repeat split.
      apply bswap16_shifted.
Qed.
