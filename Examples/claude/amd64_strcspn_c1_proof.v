(* strcspn_c1 -- strcspn with a one-character reject set

   SEMANTICS
   ---------
   __strcspn_c1(s, reject) is the exported helper that older glibc <string.h>
   headers emit for strcspn(s, "c") with a one-character literal reject string.
   It returns the length of the initial segment of s that contains neither the
   terminating NUL nor the character reject, i.e. strcspn(s, reject_str) for
   the one-character string reject_str = {reject}.  Bytes are compared as signed
   chars (MOVSX) against the int argument.  There is no man page for
   __strcspn_c1, so the specification below quotes strcspn(3).

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
            symbol __strcspn_c1 at 0x1b1100 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strcspn_c1_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; ESI = reject (int, the char promoted to int); m = memory.
            Let sx(b) = the byte b sign-extended to 32 bits (signed char -> int).
   Output:  On return, RAX = k where for all i < k, s[i] <> 0 and
            sx(s[i]) <> reject; and either s[k] = 0 or sx(s[k]) = reject.  Here
            s[i] = m[s + i] (1-byte loads, addresses mod 2^64).  So k is
            strcspn(s, {reject}) and never exceeds strlen(s).  (Partial
            correctness.)
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import strcspn_c1_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem strcspn_c1_nwc: forall s2 s1, strcspn_c1_amd64 s1 = strcspn_c1_amd64 s2.
Proof. reflexivity. Qed.

Theorem strcspn_c1_welltyped: welltyped_prog x64typctx strcspn_c1_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strcspn_c1_preserves_memory:
  forall_endstates strcspn_c1_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strcspn_c1_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strcspn_c1_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 36; offset 29 compares the current byte with reject. *)
Definition strcspn_c1_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 36 => true
  | _ => false
  end | _ => false end.


Definition avoids (m:memory) (p c k:N) :=
  forall i, i < k -> m Ⓑ[p ⊕ i] <> 0 /\ sx (m Ⓑ[p ⊕ i]) <> c.

Lemma avoids_le: forall m p c n k, avoids m p c n -> k <= n -> avoids m p c k.
Proof. intros m p c n k A LE i I. apply A. lia. Qed.

Lemma avoids_snoc:
  forall m p c k, avoids m p c k -> m Ⓑ[p ⊕ k] <> 0 -> sx (m Ⓑ[p ⊕ k]) <> c ->
  avoids m p c (k + 1).
Proof.
  intros m p c k A NZ NC i I. destruct (N.lt_ge_cases i k). apply A. assumption.
  replace i with k by lia. split; assumption.
Qed.


