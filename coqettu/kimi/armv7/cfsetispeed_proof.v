(* cfsetispeed -- set the input baud rate in a termios structure

   SEMANTICS
   ---------
   For a valid speed encoding, the function clears the input-speed field at
   offset 8 and installs speed << 16.  The proof covers that successful path;
   invalid encodings call the libc errno-location helper and return -1 after
   storing EINVAL, which is outside this theorem.

   SPECIFICATION (POSIX cfsetispeed)
   ---------------------------------

     SYNOPSIS
            #include <termios.h>
            int cfsetispeed(struct termios *termios_p, speed_t speed);

     RETURN VALUE
            On success, zero is returned.  This proof requires the binary's
            validity condition: speed has no bits outside 0x100f.

   PROVENANCE
   ----------
   Binary:  coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1, musl 1.2.6-r6
            sha256 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
            cfsetispeed at ELF VA 0x4c5cd (Thumb); Ghidra image base 0x10000,
            lifted entry 0x5c5cc.
   Lifter:  Ghidra 12.0 (headless) + pcode2coq, global addressing;
            see cfsetispeed_armv7.v.
   Model:   This specification and proof were written by Kimi, an AI model by
            Moonshot AI, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS, Thumb state)
   -----------------------------------------------
   Input:   R0 = termios_p, R1 = speed, with no speed bits outside 0x100f.
   Output:  At the POP instruction at 0x5c5ea, R0 = 0 and the word at R0+8 in
            the original structure has new value ((old & ~0x100f0000) |
            (speed << 16)) mod 2^32.  The stack contains saved LR and R3 at
            SP-4 and SP-8, and SP = initial SP-8.  The proof stops before POP.
 *)

From Stdlib Require Import NArith.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import cfsetispeed_armv7.
Import ARM7Notations.
Open Scope N.

Definition cfsetispeed_entry : addr := 0x5c5cc.
Definition cfsetispeed_return : addr := 0x5c5ea.

Definition cfsetispeed_valid (speed : N) : Prop :=
  (speed .& (N.lnot 0x1000 32)) .& (N.lnot 0xf 32) = 0.

Definition cfsetispeed_newword (old speed : N) : N :=
  ((old .& (N.lnot 0x10000000 32)) .& (N.lnot 0xf0000 32)) .|
  ((speed << 16) mod 2^32).

Definition cfsetispeed_pushmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
    ((s0 R_SP) ⊖ 8) (s0 R_R3).

Definition cfsetispeed_post (s0 s : store) : Prop :=
  s R_R0 = 0 /\
  s R_SP = (s0 R_SP) ⊖ 8 /\
  s V_MEM32 = setmem 32 LittleE 4 (cfsetispeed_pushmem s0)
    ((s0 R_R0) ⊕ 8)
    (cfsetispeed_newword ((cfsetispeed_pushmem s0) Ⓓ[(s0 R_R0) ⊕ 8]
                         ) (s0 R_R1)).

Definition cfsetispeed_invs (s0 : store) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x5c5cc => Some (s = s0 /\ cfsetispeed_valid (s0 R_R1))
      | 0x5c5ea => Some (cfsetispeed_post s0 s)
      | _ => None
      end
  | _ => None
  end.

Definition cfsetispeed_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? cfsetispeed_return
  | _ => false
  end.

Theorem cfsetispeed_nwc : forall s1 s2, cfsetispeed_armv7 s1 = cfsetispeed_armv7 s2.
Proof. reflexivity. Qed.

Theorem cfsetispeed_welltyped : welltyped_prog arm7typctx cfsetispeed_armv7.
Proof. exact welltyped. Qed.

Theorem cfsetispeed_preserves_callee_saved :
  forall v,
    match v with
    | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 | R_R11 => true
    | _ => false
    end = true ->
    forall_endstates cfsetispeed_armv7 (fun _ s _ s' => s v = s' v).
Proof.
  intros v HV.
  apply noassign_prog_same.
  destruct v; simpl in HV; try discriminate; prove_noassign.
Qed.

Theorem cfsetispeed_correct :
  forall prog (EXT : cfsetispeed_armv7 ⊆2 prog) s0 t xs
         (ENTRY : startof t xs = (Addr cfsetispeed_entry, s0))
         (MDL : models arm7typctx s0)
         (VALID : cfsetispeed_valid (s0 R_R1)),
    satisfies_all prog (cfsetispeed_invs s0) cfsetispeed_exit (xs :: t).
Proof.
  intros prog EXT s0 t [x' s'] ENTRY MDL VALID.
  eapply satisfies_all_pmono with (p1 := cfsetispeed_armv7); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold cfsetispeed_invs.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - s0 MDL VALID START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. split; [reflexivity|exact VALID].
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply cfsetispeed_welltyped.
      intro MDL1.
      clear - PRE MDL1.
      destruct_inv 32 PRE.

      * destruct PRE as [EQ VALID]. simpl in EQ. subst s0.
        do 4 arm7_step. unfold cfsetispeed_valid in VALID.
        change (s1 R_R1 .& 4294963199 .& 4294967280 = 0) in VALID.
        rewrite VALID. arm7_step.
        -- simpl in BC. discriminate.
        -- do 5 arm7_step.
           unfold cfsetispeed_post, cfsetispeed_newword, cfsetispeed_pushmem.
           elimstore. repeat split; psimpl; reflexivity.
Qed.
