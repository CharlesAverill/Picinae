(* isascii (AArch64 / ARMv8) -- test whether c is a 7-bit ASCII value

   SEMANTICS
   ---------
   isascii(c) returns nonzero iff c is in 0..127.  On AArch64 this is
   `tst w0, #0xffffff80` (set flags on the high bits) followed by
   `cset w0, eq` (1 iff those bits are all zero) and `ret`.

   SPECIFICATION (man 3 isascii, Linux man-pages, Ubuntu 22.04)
   ------------------------------------------------------------
     int isascii(int c);
     isascii() checks whether c is a 7-bit unsigned char value that fits into
     the ASCII character set.

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (Ubuntu 22.04 ports), sha256
            79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
            symbol isascii at 0x134470.
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq; see isascii_arm8.v.
   Model:   Specification and proof written by Claude Opus 4.8
            (claude-opus-4-8), an AI model by Anthropic, machine-checked by Rocq.
   Note:    AArch64 glibc port.  The specification (and the pure-arithmetic
            helper lemmas land_mask7/toZ32_ascii) are shared with the x86-64
            proof amd64_isascii_proof.v; only the lifted body, the argument/
            return register (W0/X0), and the step tactic differ.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   W0 (low 32 bits of X0) holds c; c (signed) = toZ 32 (X0 mod 2^32).
   Output:  On return, X0 = 1 if 0 <= c <= 127, and X0 = 0 otherwise.
            Memory is not modified; no callee-saved register is modified.
 *)

Require Import Picinae_armv8.
Require Import isascii_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith List.
Import ListNotations.
Open Scope N.

Theorem isascii_nwc: forall s2 s1, isascii_arm8 s1 = isascii_arm8 s2.
Proof. reflexivity. Qed.

Theorem isascii_welltyped: welltyped_prog arm8typctx isascii_arm8.
Proof. Picinae_typecheck. Qed.

Theorem isascii_preserves_memory:
  forall_endstates isascii_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* Pure-arithmetic helpers, shared verbatim with amd64_isascii_proof.v. *)
Lemma land_mask7:
  forall x, (x .& 4294967168 =? 0) = (x mod 2^32 <? 128).
Proof.
  intro x.
  replace (x .& 4294967168) with (N.shiftl (N.shiftr (x mod 2^32) 7) 7).
    rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2.
    destruct (N.ltb_spec (x mod 2^32) 128) as [H|H].
      rewrite N.div_small by exact H. reflexivity.
      apply N.eqb_neq. intro H0. apply N.eq_mul_0_l in H0; [|discriminate].
      apply N.div_small_iff in H0; [|discriminate]. lia.
  apply N.bits_inj. intro i. rewrite N.land_spec.
  change 4294967168 with (N.shiftl (N.ones 25) 7).
  destruct (N.lt_ge_cases i 7) as [I|I].
    rewrite !N.shiftl_spec_low by exact I. symmetry. apply Bool.andb_false_r.
    rewrite !N.shiftl_spec_high' by exact I. rewrite N.shiftr_spec', N.sub_add by exact I.
    rewrite Nmod_pow2_bits.
    destruct (N.lt_ge_cases i 32) as [J|J].
      rewrite (proj2 (N.ltb_lt _ _) J), N.ones_spec_low by lia. apply Bool.andb_comm.
      rewrite (proj2 (N.ltb_ge _ _) J), N.ones_spec_high by lia. symmetry. apply Bool.andb_false_r.
Qed.

Lemma toZ32_ascii:
  forall n, andb (Z.leb 0 (toZ 32 n)) (Z.leb (toZ 32 n) 127) = (n mod 2^32 <? 128).
Proof.
  intro n. destruct (N.lt_ge_cases (n mod 2^32) (2^31)) as [H|H].
    rewrite (proj1 (toZ_nonneg 32 n) H).
    destruct (N.ltb_spec (n mod 2^32) 128); destruct (Z.leb_spec 0 (Z.of_N (n mod 2^32)));
    destruct (Z.leb_spec (Z.of_N (n mod 2^32)) 127); simpl; lia.
    assert (NEG: Z.lt (toZ 32 n) 0).
      apply Z.nle_gt. intro H1. apply toZ_sign in H1. simpl in H1. lia.
    destruct (Z.leb_spec 0 (toZ 32 n)); [lia|].
    simpl. symmetry. apply N.ltb_ge. change (2^31) with 2147483648 in H. lia.
Qed.

(* The RET is at offset 8. *)
Definition isascii_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 8 => true
  | _ => false
  end | _ => false end.

Definition postcondition (c:Z) (s:store) :=
  s R_X0 = (if andb (0 <=? c)%Z (c <=? 127)%Z then 1 else 0).

Definition isascii_invs (c:Z) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_X0 mod 2^32) = c)
  | 8 => Some (postcondition c s)
  | _ => None
  end | _ => None end.

Theorem isascii_correct:
  forall s t s' x' c
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (C: toZ 32 (s R_X0 mod 2^32) = c),
  satisfies_all isascii_arm8 (isascii_invs c) isascii_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into C.
  repeat arm8_step.
  unfold postcondition.
  rewrite land_mask7, <- C, toZ32_ascii, mp2_mod_mod. reflexivity.
Qed.
