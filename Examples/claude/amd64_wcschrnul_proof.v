(* wcschrnul -- locate a wide character, or the end of the string

   SEMANTICS
   ---------
   wcschrnul(wcs, wc) scans the wide-character string wcs (4-byte wchar_t on
   amd64) and returns a pointer to the first element equal to wc, or to the
   terminating null wide character if wc does not occur.  This is the
   wide-character version of strchrnul.  There is no wcschrnul man page on
   this system, so the specification below quotes strchrnul from strchr(3) and
   the wide-character conventions from wcschr(3).  Like strchrnul, searching
   for wc = L'\0' returns the terminator.

   SPECIFICATION (man 3 strchr and man 3 wcschr, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     strchr(3):
            char *strchrnul(const char *s, int c);

            The  strchr() function returns a pointer to the first occurrence of the
            character c in the string s.

            The strchrnul() function is like strchr() except that if c is not found
            in s, then it returns a pointer to the null  byte  at  the  end  of  s,
            rather than NULL.

        RETURN VALUE
            The strchrnul() function returns a pointer to the matched character, or
            a pointer to the null byte at the end of s (i.e., s+strlen(s)) if the
            character is not found.

     wcschr(3):
            wchar_t *wcschr(const wchar_t *wcs, wchar_t wc);

            The wcschr() function is the wide-character equivalent of the strchr(3)
            function.  It searches the first occurrence of wc in the wide-character
            string pointed to by wcs.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol wcschrnul at 0x1c6d50 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see wcschrnul_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = wcs, ESI = wc (wchar_t, 32 bits); m = memory on entry.
   Output:  On return, RAX = wcs + 4k for some k such that every element
            wcs[i] (i < k) differs from both wc and 0, and wcs[k] = wc or
            wcs[k] = 0.  Elements are the 4-byte words m[wcs + 4i], and addresses
            are taken mod 2^64.  (This is partial correctness: the theorem holds
            whenever wcschrnul returns.)
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import wcschrnul_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem wcschrnul_nwc: forall s2 s1, wcschrnul_amd64 s1 = wcschrnul_amd64 s2.
Proof. reflexivity. Qed.

Theorem wcschrnul_welltyped: welltyped_prog x64typctx wcschrnul_amd64.
Proof. Picinae_typecheck. Qed.

Theorem wcschrnul_preserves_memory:
  forall_endstates wcschrnul_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcschrnul_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates wcschrnul_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 31.  Offset 27 tests the current element for nil. *)
Definition wcschrnul_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 31 => true
  | _ => false
  end | _ => false end.

(* wcs[0..k) contains neither wc nor 0 *)
Definition scanned (m:memory) (p c k:N) :=
  forall i, i < k -> m Ⓓ[p ⊕ 4*i] <> c /\ m Ⓓ[p ⊕ 4*i] <> 0.

Lemma scanned_succ:
  forall m p c k, scanned m p c k -> m Ⓓ[p ⊕ 4*k] <> c -> m Ⓓ[p ⊕ 4*k] <> 0 ->
  scanned m p c (k+1).
Proof.
  intros m p c k SC NC NZ i I. destruct (N.lt_ge_cases i k).
    apply SC. assumption.
    replace i with k by lia. split; assumption.
Qed.

(* Element addresses as computed by the loop. *)
Lemma elem_addr: forall (m:memory) p k, m Ⓓ[p + 4*k] = m Ⓓ[p ⊕ 4*k].
Proof. intros. symmetry. apply getmem_mod_l. Qed.

Lemma elem_addr_succ: forall (m:memory) p k, m Ⓓ[4 + p + 4*k] = m Ⓓ[p ⊕ 4*(k+1)].
Proof.
  intros. rewrite <- (getmem_mod_l _ _ _ _ (4 + p + 4*k)). f_equal.
  change (2^64) with 18446744073709551616. lia.
Qed.

Definition postcondition (m p c rsp:N) (s:store) :=
  (exists k, s R_RAX = p ⊕ 4*k /\ scanned m p c k /\
             (m Ⓓ[p ⊕ 4*k] = c \/ m Ⓓ[p ⊕ 4*k] = 0)) /\
  s R_RSP = rsp.

Definition wcschrnul_invs (m p c rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c /\ s R_RSP = rsp)
  | 27 => Some (s V_MEM64 = m /\ s R_RSI mod 2^32 = c /\ s R_RSP = rsp /\
                exists k, s R_RAX = p ⊕ 4*k /\ s R_RDX = m Ⓓ[p ⊕ 4*k] /\
                          scanned m p c k /\ m Ⓓ[p ⊕ 4*k] <> c)
  | 31 => Some (postcondition m p c rsp s)
  | _ => None
  end | _ => None end.

Theorem wcschrnul_correct:
  forall s t s' x' m p c rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI mod 2^32 = c)
         (RSP: s R_RSP = rsp),
  satisfies_all wcschrnul_amd64 (wcschrnul_invs m p c rsp) wcschrnul_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcschrnul_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [MEM [P [C RSP]]].
    assert (PL: p < 2^64) by (rewrite <- P; apply (MDL1 R_RDI 64), eq_refl).
    assert (P0: p ⊕ 4*0 = p) by (rewrite N.mul_0_r, N.add_0_r; apply N.mod_small; exact PL).
    repeat x64_step.
    + split; [|assumption]. exists 0. rewrite P0. split; [reflexivity|]. split.
        intros j J. lia.
        left. rewrite C in BC. apply N.eqb_eq in BC. symmetry. assumption.
    + split; [reflexivity|]. split; [assumption|]. split; [assumption|].
      exists 0. rewrite P0. split; [reflexivity|]. split; [reflexivity|]. split.
        intros j J. lia.
        rewrite C in BC. apply N.eqb_neq in BC. intro H. apply BC. symmetry. assumption.
  - destruct PRE as [MEM [C [RSP [k [RAX [RDX [SC NC]]]]]]].
    repeat x64_step.
    + rewrite elem_addr in BC. apply N.eqb_eq in BC.
      split; [|assumption]. exists k. split; [assumption|]. split; [assumption|]. right. assumption.
    + rewrite elem_addr in BC. apply N.eqb_neq in BC.
      rewrite elem_addr_succ, C in BC0. apply N.eqb_eq in BC0.
      split; [|assumption]. exists (k+1). split.
        try rewrite RAX. change (2^64) with 18446744073709551616. lia.
      split. apply scanned_succ; assumption. left. assumption.
    + rewrite elem_addr in BC. apply N.eqb_neq in BC.
      rewrite elem_addr_succ, C in BC0. apply N.eqb_neq in BC0.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|].
      exists (k+1). split.
        try rewrite RAX. change (2^64) with 18446744073709551616. lia.
      split. rewrite elem_addr_succ. reflexivity.
      split. apply scanned_succ; assumption. assumption.
Qed.
