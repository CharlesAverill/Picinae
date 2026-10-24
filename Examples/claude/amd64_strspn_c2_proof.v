(* strspn_c2 -- strspn with a two-character accept set

   SEMANTICS
   ---------
   __strspn_c2(s, accept1, accept2) is the exported helper that older glibc <string.h>
   headers emit for strspn(s, "ab") with a two-character literal accept string.
   It counts how many leading bytes of s equal accept1 or accept2, i.e. it
   computes strspn(s, accept_str) for accept_str = {accept1, accept2}.
   The byte is compared as a signed char (MOVSX) against the int arguments;
   callers pass the character promoted from char, which makes the two
   representations agree.  There is no man page for __strspn_c2, so the
   specification below quotes strspn(3).

   SPECIFICATION (man 3 strspn, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strspn(const char *s, const char *accept);

     DESCRIPTION
            The  strspn()  function calculates the length (in bytes) of the initial
            segment of s which consists entirely of bytes in accept.

     RETURN VALUE
            The strspn() function returns the number of bytes in the initial  seg-
            ment of s which consist only of bytes from accept.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol __strspn_c2 at 0x1b11d0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strspn_c2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; ESI = accept1, EDX = accept2 (ints, the chars promoted to int);
            m = memory.  Let sx(b) = the byte b sign-extended to 32 bits.
   Output:  On return, RAX = k where sx(s[i]) is accept1 or accept2 for all i < k,
            and sx(s[k]) is neither, with s[i] = m[s + i] (1-byte loads,
            addresses mod 2^64).  If both accept characters are nonzero, s[0..k)
            contains no NUL, so k is exactly strspn(s, {accept1, accept2}).
            (Partial correctness.)
   Frame:   RSP is unchanged at both RETs, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import strspn_c2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem strspn_c2_nwc: forall s2 s1, strspn_c2_amd64 s1 = strspn_c2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strspn_c2_welltyped: welltyped_prog x64typctx strspn_c2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strspn_c2_preserves_memory:
  forall_endstates strspn_c2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strspn_c2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strspn_c2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 40 and 43; the loop head is offset 24. *)
Definition strspn_c2_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 40 | 43 => true
  | _ => false
  end | _ => false end.

Definition in2 (c1 c2 b:N) := sx b = c1 \/ sx b = c2.

Definition matches (m:memory) (p c1 c2 k:N) := forall i, i < k -> in2 c1 c2 (m Ⓑ[p ⊕ i]).

Lemma matches_le: forall m p c1 c2 n k, matches m p c1 c2 n -> k <= n -> matches m p c1 c2 k.
Proof. intros m p c1 c2 n k M LE i I. apply M. lia. Qed.

Lemma matches_snoc:
  forall m p c1 c2 k, matches m p c1 c2 k -> in2 c1 c2 (m Ⓑ[p ⊕ k]) -> matches m p c1 c2 (1 + k).
Proof.
  intros m p c1 c2 k M E i I. destruct (N.lt_ge_cases i k). apply M. assumption.
  replace i with k by lia. assumption.
Qed.

Definition postcondition (m p c1 c2 rsp:N) (s:store) :=
  matches m p c1 c2 (s R_RAX) /\ ~ in2 c1 c2 (m Ⓑ[p ⊕ s R_RAX]) /\ s R_RSP = rsp.

Definition strspn_c2_invs (m p c1 c2 rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c1 /\
               s R_RDX mod 2^32 = c2 /\ s R_RSP = rsp)
  | 24 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c1 /\
                s R_RDX mod 2^32 = c2 /\ s R_RSP = rsp /\ matches m p c1 c2 (s R_RAX + 1))
  | 40 | 43 => Some (postcondition m p c1 c2 rsp s)
  | _ => None
  end | _ => None end.

Theorem strspn_c2_correct:
  forall s t s' x' m p c1 c2 rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C1: s R_RSI mod 2^32 = c1)
         (C2: s R_RDX mod 2^32 = c2) (RSP: s R_RSP = rsp),
  satisfies_all strspn_c2_amd64 (strspn_c2_invs m p c1 c2 rsp) strspn_c2_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strspn_c2_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [MEM [P [C1 [C2 RSP]]]].
    assert (PL: p < 2^64) by (rewrite <- P; apply (MDL1 R_RDI 64), eq_refl).
    assert (P0: p ⊕ 0 = p) by (rewrite N.add_0_r; apply N.mod_small; exact PL).
    repeat x64_step.
    all: repeat (rewrite update_frame by discriminate); try rewrite update_updated.
    all: norm_byte_bc BC; try norm_byte_bc BC0; rewrite ?C1, ?C2 in *.
    + repeat split; try assumption. intros i I. replace i with 0 by lia. rewrite P0. right. symmetry. assumption.
    + repeat split; try assumption. intros i I. replace i with 0 by lia. rewrite P0. left. symmetry. assumption.
    + split. intros i I. lia. split; [|assumption].
      intros [H|H]; [apply BC0|apply BC]; symmetry; assumption.
  - destruct PRE as [MEM [P [C1 [C2 [RSP MT]]]]].
    repeat x64_step.
    all: repeat (rewrite update_frame by discriminate); try rewrite update_updated.
    all: norm_byte_bc BC; try norm_byte_bc BC0; rewrite ?C1, ?C2 in *.
    + repeat split; try assumption. apply matches_snoc.
      eapply matches_le. eassumption. apply succ_le. right. assumption.
    + repeat split; try assumption. apply matches_snoc.
      eapply matches_le. eassumption. apply succ_le. left. assumption.
    + split. eapply matches_le. eassumption. apply succ_le.
      split; [|assumption]. rewrite byte_addr_succ.
      intros [H|H]; [apply BC0|apply BC]; assumption.
Qed.
