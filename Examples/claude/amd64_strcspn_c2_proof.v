(* strcspn_c2 -- strcspn with a two-character reject set

   SEMANTICS
   ---------
   __strcspn_c2(s, reject1, reject2) is the exported helper that older glibc <string.h>
   headers emit for strcspn(s, "ab") with a two-character literal reject string.
   It returns the length of the initial segment of s that contains neither the
   terminating NUL nor either reject character, i.e. strcspn(s, reject_str)
   for reject_str = {reject1, reject2}.  Bytes are compared as signed
   chars (MOVSX) against the int arguments.  There is no man page for
   __strcspn_c2, so the specification below quotes strcspn(3).

   SPECIFICATION (man 3 strcspn, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strcspn(const char *s, const char *reject);

     DESCRIPTION
            The strcspn() function calculates the length of the initial segment  of
            s which consists entirely of bytes not in reject.

     RETURN VALUE
            The strcspn() function returns the number of bytes in the initial  seg-
            ment of s which are not in the string reject.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol __strcspn_c2 at 0x1b1130 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strcspn_c2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; ESI = reject1, EDX = reject2 (ints, the chars promoted to int);
            m = memory.  Let sx(b) = the byte b sign-extended to 32 bits.
   Output:  On return, RAX = k where for all i < k, s[i] <> 0 and sx(s[i]) is
            neither reject1 nor reject2; and s[k] = 0, or sx(s[k]) = reject1, or
            sx(s[k]) = reject2.  Here s[i] = m[s + i] (1-byte loads, addresses
            mod 2^64).  So k is strcspn(s, {reject1, reject2}).  (Partial
            correctness.)
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import strcspn_c2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem strcspn_c2_nwc: forall s2 s1, strcspn_c2_amd64 s1 = strcspn_c2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strcspn_c2_welltyped: welltyped_prog x64typctx strcspn_c2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strcspn_c2_preserves_memory:
  forall_endstates strcspn_c2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strcspn_c2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strcspn_c2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 40; offset 33 compares the current byte with reject2. *)
Definition strcspn_c2_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 40 => true
  | _ => false
  end | _ => false end.

Definition avoids (m:memory) (p c1 c2 k:N) :=
  forall i, i < k -> m Ⓑ[p ⊕ i] <> 0 /\ sx (m Ⓑ[p ⊕ i]) <> c1 /\ sx (m Ⓑ[p ⊕ i]) <> c2.

Lemma avoids_le: forall m p c1 c2 n k, avoids m p c1 c2 n -> k <= n -> avoids m p c1 c2 k.
Proof. intros m p c1 c2 n k A LE i I. apply A. lia. Qed.

Lemma avoids_snoc:
  forall m p c1 c2 k, avoids m p c1 c2 k -> m Ⓑ[p ⊕ k] <> 0 ->
  sx (m Ⓑ[p ⊕ k]) <> c1 -> sx (m Ⓑ[p ⊕ k]) <> c2 -> avoids m p c1 c2 (k + 1).
Proof.
  intros m p c1 c2 k A NZ N1 N2 i I. destruct (N.lt_ge_cases i k). apply A. assumption.
  replace i with k by lia. repeat split; assumption.
Qed.

Definition postcondition (m p c1 c2 rsp:N) (s:store) :=
  avoids m p c1 c2 (s R_RAX) /\
  (m Ⓑ[p ⊕ s R_RAX] = 0 \/ sx (m Ⓑ[p ⊕ s R_RAX]) = c1 \/ sx (m Ⓑ[p ⊕ s R_RAX]) = c2) /\
  s R_RSP = rsp.

Definition strcspn_c2_invs (m p c1 c2 rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c1 /\
               s R_RDX mod 2^32 = c2 /\ s R_RSP = rsp)
  | 33 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c1 /\
                s R_RDX mod 2^32 = c2 /\ s R_RSP = rsp /\
                s R_RAX = sx (m Ⓑ[p ⊕ s R_R8]) /\ m Ⓑ[p ⊕ s R_R8] <> 0 /\
                avoids m p c1 c2 (s R_R8))
  | 40 => Some (postcondition m p c1 c2 rsp s)
  | _ => None
  end | _ => None end.

Theorem strcspn_c2_correct:
  forall s t s' x' m p c1 c2 rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C1: s R_RSI mod 2^32 = c1)
         (C2: s R_RDX mod 2^32 = c2) (RSP: s R_RSP = rsp),
  satisfies_all strcspn_c2_amd64 (strcspn_c2_invs m p c1 c2 rsp) strcspn_c2_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcspn_c2_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [MEM [P [C1 [C2 RSP]]]].
    assert (PL: p < 2^64) by (rewrite <- P; apply (MDL1 R_RDI 64), eq_refl).
    assert (P0: p ⊕ 0 = p) by (rewrite N.add_0_r; apply N.mod_small; exact PL).
    repeat x64_step.
    all: repeat (rewrite update_frame by discriminate); try rewrite update_updated.
    all: fold (sx (m Ⓑ[p])) in BC; rewrite sx_low8 in BC by apply getmem_bound.
    + split. intros j J. lia. split; [|assumption]. left. apply N.eqb_eq. assumption.
    + apply N.eqb_neq in BC. repeat split; try assumption; try lia.
      rewrite P0. apply sx_mod.
  - destruct PRE as [MEM [P [C1 [C2 [RSP [RAX [NZ AV]]]]]]].
    assert (RL: s1 R_R8 < 2^64) by apply (MDL1 R_R8 64), eq_refl.
    repeat x64_step.
    all: repeat (rewrite update_frame by discriminate); try rewrite update_updated.
    all: rewrite ?sx_mod, ?C1, ?C2 in BC; try (rewrite ?sx_mod, ?C1, ?C2 in BC0).
    all: try rewrite mul1_mod in BC1 by apply mp2_mod_lt.
    all: repeat match goal with H: context [scast 8 32 ?b] |- _ => fold (sx b) in H end.
    all: repeat match goal with |- context [scast 8 32 ?b] => fold (sx b) end.
    all: rewrite ?byte_addr_succ, ?byte_addr, ?mul1_mod in * by apply mp2_mod_lt.
    all: rewrite ?sx_low8 in * by apply getmem_bound.
    + apply N.eqb_eq in BC. split; [assumption|]. split; [|assumption]. right; right; assumption.
    + apply N.eqb_neq in BC. apply N.eqb_eq in BC0.
      split; [assumption|]. split; [|assumption]. right; left; assumption.
    + apply N.eqb_neq in BC. apply N.eqb_neq in BC0. apply N.eqb_eq in BC1.
      split. eapply avoids_le. apply avoids_snoc; eassumption. apply succ_le.
      split; [|assumption]. left; assumption.
    + apply N.eqb_neq in BC. apply N.eqb_neq in BC0. apply N.eqb_neq in BC1.
      split; [reflexivity|]. split; [reflexivity|]. do 3 (split; [assumption|]).
      split. apply sx_mod. split. assumption.
      eapply avoids_le. apply avoids_snoc; eassumption. apply succ_le.
Qed.
