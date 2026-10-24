(* isascii -- test for a 7-bit ASCII character

   SEMANTICS
   ---------
   isascii returns nonzero exactly when its int argument is in [0, 127].
   glibc's implementation returns precisely 1 or 0.

   SPECIFICATION (man 3 isascii, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int isascii(int c);

     DESCRIPTION
            These  functions  check  whether c, which must have the value of an un-
            signed char or EOF, falls into a certain character class  according  to
            the  specified  locale.

            isascii()
                   checks whether c is a 7-bit unsigned char value that  fits  into
                   the ASCII character set.

     RETURN VALUE
            The  values  returned  are  nonzero  if  the character c falls into the
            tested class, and zero if not.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see isascii_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI (low 32 bits of RDI) holds c, read as a 32-bit two's-complement int.
   Output:  On return, RAX = 1 if 0 <= c <= 127, and RAX = 0 otherwise.
            (The theorem is stronger than the man page, which only promises
            nonzero/zero, and it holds for every int c, not just unsigned-char
            values and EOF.)
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import isascii_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem isascii_nwc: forall s2 s1, isascii_amd64 s1 = isascii_amd64 s2.
Proof. reflexivity. Qed.

Theorem isascii_welltyped: welltyped_prog x64typctx isascii_amd64.
Proof. Picinae_typecheck. Qed.

Theorem isascii_preserves_memory:
  forall_endstates isascii_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem isascii_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates isascii_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 12. *)
Definition isascii_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 12 => true
  | _ => false
  end | _ => false end.

(* c is the signed value of EDI. *)
Definition postcondition (c:Z) (rsp:N) (s:store) :=
  s R_RAX = (if andb (0 <=? c)%Z (c <=? 127)%Z then 1 else 0) /\ s R_RSP = rsp.

Definition isascii_invs (c:Z) (rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 32 (s R_RDI mod 2^32) = c /\ s R_RSP = rsp)
  | 12 => Some (postcondition c rsp s)
  | _ => None
  end | _ => None end.

(* EDI .& 0xffffff80 = 0  iff  EDI < 128 (as an unsigned 32-bit value). *)
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

(* ... iff EDI, read as a signed int, is in [0, 127]. *)
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

Theorem isascii_correct:
  forall s t s' x' c rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (C: toZ 32 (s R_RDI mod 2^32) = c) (RSP: s R_RSP = rsp),
  satisfies_all isascii_amd64 (isascii_invs c rsp) isascii_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [C RSP].
  repeat x64_step.
  rewrite land_mask7, <- C, toZ32_ascii, mp2_mod_mod. split; [reflexivity|assumption].
Qed.
