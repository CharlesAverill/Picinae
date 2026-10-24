(* strspn_c1 -- strspn with a one-character accept set

   SEMANTICS
   ---------
   __strspn_c1(s, accept) is the exported helper that older glibc <string.h>
   headers emit for strspn(s, "c") with a one-character literal accept string.
   It counts how many leading bytes of s equal accept, i.e. it computes
   strspn(s, accept_str) for the one-character string accept_str = {accept}.
   The byte is compared as a signed char (MOVSX) against the int argument;
   callers pass the character promoted from char, which makes the two
   representations agree.  There is no man page for __strspn_c1, so the
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
            symbol __strspn_c1 at 0x1b11a0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strspn_c1_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; ESI = accept (int, the char promoted to int); m = memory.
            Let sx(b) = the byte b sign-extended to 32 bits (signed char -> int).
   Output:  On return, RAX = k where sx(s[i]) = accept for all i < k, and
            sx(s[k]) <> accept, with s[i] = m[s + i] (1-byte loads, addresses
            mod 2^64).  If accept is nonzero, s[0..k) contains no NUL, so k is
            exactly strspn(s, {accept}).  (Partial correctness.)
   Frame:   RSP is unchanged at both RETs, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import strspn_c1_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem strspn_c1_nwc: forall s2 s1, strspn_c1_amd64 s1 = strspn_c1_amd64 s2.
Proof. reflexivity. Qed.

Theorem strspn_c1_welltyped: welltyped_prog x64typctx strspn_c1_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strspn_c1_preserves_memory:
  forall_endstates strspn_c1_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strspn_c1_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strspn_c1_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 28 and 32; the loop head is offset 16. *)
Definition strspn_c1_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 28 | 32 => true
  | _ => false
  end | _ => false end.


Definition matches (m:memory) (p c k:N) := forall i, i < k -> sx (m Ⓑ[p ⊕ i]) = c.

Lemma matches_le: forall m p c n k, matches m p c n -> k <= n -> matches m p c k.
Proof. intros m p c n k M LE i I. apply M. lia. Qed.

Lemma matches_snoc:
  forall m p c k, matches m p c k -> sx (m Ⓑ[p ⊕ k]) = c -> matches m p c (1 + k).
Proof.
  intros m p c k M E i I. destruct (N.lt_ge_cases i k). apply M. assumption.
  replace i with k by lia. assumption.
Qed.

