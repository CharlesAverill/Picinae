(* strpbrk_c2 -- strpbrk with a two-character accept set

   SEMANTICS
   ---------
   __strpbrk_c2(s, accept1, accept2) is the exported helper that older glibc
   <string.h> headers emit for strpbrk(s, "ab") with a two-character literal
   accept string.  It returns a pointer to the first byte of s equal to
   accept1 or accept2, or NULL if the terminating NUL comes first.  Bytes are
   compared as signed chars (MOVSX) against the int arguments.  There is no man
   page for __strpbrk_c2, so the specification below quotes strpbrk(3).

   SPECIFICATION (man 3 strpbrk, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strpbrk(const char *s, const char *accept);

     DESCRIPTION
            The  strpbrk()  function locates the first occurrence in the string s
            of any of the bytes in the string accept.

     RETURN VALUE
            The strpbrk() function returns a pointer to the byte in s that matches
            one of the bytes in accept, or NULL if no such byte is found.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol __strpbrk_c2 at 0x1b1260 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strpbrk_c2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; ESI = accept1, EDX = accept2 (ints, the chars promoted to int);
            m = memory.  Let sx(b) = the byte b sign-extended to 32 bits.
   Output:  On return, for some k such that every s[i] (i < k) is non-NUL and
            sx(s[i]) is neither accept1 nor accept2:
              either s[k] <> 0, sx(s[k]) is accept1 or accept2, and RAX = s + k
                     (a pointer to the first match);
              or s[k] = 0 and RAX = 0 (NULL: no match before the terminator).
            Here s[i] = m[s + i] (1-byte loads, addresses mod 2^64).
            (Partial correctness.)
   Frame:   RSP is unchanged at all three RETs, so control returns to the
            caller's return address.  Memory is not modified.  No callee-saved
            register (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import strpbrk_c2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem strpbrk_c2_nwc: forall s2 s1, strpbrk_c2_amd64 s1 = strpbrk_c2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strpbrk_c2_welltyped: welltyped_prog x64typctx strpbrk_c2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strpbrk_c2_preserves_memory:
  forall_endstates strpbrk_c2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strpbrk_c2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strpbrk_c2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 36, 42 and 48; offset 32 compares the
   current byte with accept2. *)
Definition strpbrk_c2_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 36 | 42 | 48 => true
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

Lemma addr_next: forall p k, p ⊕ k ⊕ 1 = p ⊕ (k + 1).
Proof. intros. change (2^64) with 18446744073709551616. lia. Qed.

Lemma addr_next': forall p k, 1 + p ⊕ k = p ⊕ (k + 1).
Proof. intros. change (2^64) with 18446744073709551616. lia. Qed.

Definition postcondition (m p c1 c2 rsp:N) (s:store) :=
  (exists k, avoids m p c1 c2 k /\
     ((m Ⓑ[p ⊕ k] <> 0 /\ (sx (m Ⓑ[p ⊕ k]) = c1 \/ sx (m Ⓑ[p ⊕ k]) = c2) /\ s R_RAX = p ⊕ k) \/
      (m Ⓑ[p ⊕ k] = 0 /\ s R_RAX = 0))) /\
  s R_RSP = rsp.

Definition strpbrk_c2_invs (m p c1 c2 rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI mod 2^32 = c1 /\
               s R_RDX mod 2^32 = c2 /\ s R_RSP = rsp)
  | 32 => Some (s V_MEM64 = m /\ s R_RSI mod 2^32 = c1 /\ s R_RDX mod 2^32 = c2 /\
                s R_RSP = rsp /\ exists k, s R_RAX = p ⊕ k /\
                s R_RCX = sx (m Ⓑ[p ⊕ k]) /\ m Ⓑ[p ⊕ k] <> 0 /\ avoids m p c1 c2 k)
  | 36 | 42 | 48 => Some (postcondition m p c1 c2 rsp s)
  | _ => None
  end | _ => None end.

Theorem strpbrk_c2_correct:
  forall s t s' x' m p c1 c2 rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C1: s R_RSI mod 2^32 = c1)
         (C2: s R_RDX mod 2^32 = c2) (RSP: s R_RSP = rsp),
  satisfies_all strpbrk_c2_amd64 (strpbrk_c2_invs m p c1 c2 rsp) strpbrk_c2_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strpbrk_c2_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [MEM [P [C1 [C2 RSP]]]].
    assert (PL: p < 2^64) by (rewrite <- P; apply (MDL1 R_RDI 64), eq_refl).
    assert (P0: p ⊕ 0 = p) by (rewrite N.add_0_r; apply N.mod_small; exact PL).
    repeat x64_step.
    all: fold (sx (m Ⓑ[p])) in *; rewrite ?sx_low8 in BC by apply getmem_bound.
    + apply N.eqb_eq in BC. split; [|assumption]. exists 0. rewrite P0.
      split. intros j J. lia. right. split; [assumption|reflexivity].
    + apply N.eqb_neq in BC. split; [reflexivity|]. do 3 (split; [assumption|]).
      exists 0. rewrite P0. split; [reflexivity|]. split. apply sx_mod.
      split. assumption. intros j J. lia.
  - destruct PRE as [MEM [C1 [C2 [RSP [k [RAX [RCX [NZ AV]]]]]]]].
    repeat x64_step.
    all: rewrite ?addr_next, ?addr_next' in *.
    all: repeat match goal with H: context [scast 8 32 ?b] |- _ => fold (sx b) in H end.
    all: repeat match goal with |- context [scast 8 32 ?b] => fold (sx b) end.
    all: rewrite ?sx_mod, ?C1, ?C2 in *; rewrite ?sx_low8 in * by apply getmem_bound.
    + apply N.eqb_eq in BC. split; [|assumption]. exists k. split; [assumption|].
      left. split; [assumption|]. split; [right; assumption|assumption].
    + apply N.eqb_neq in BC. apply N.eqb_eq in BC0. split; [|assumption]. exists k.
      split; [assumption|]. left. split; [assumption|]. split; [left; assumption|assumption].
    + apply N.eqb_neq in BC. apply N.eqb_neq in BC0. apply N.eqb_eq in BC1.
      split; [|assumption]. exists (k + 1). split.
        apply avoids_snoc; assumption.
        right. split; [assumption|reflexivity].
    + apply N.eqb_neq in BC. apply N.eqb_neq in BC0. apply N.eqb_neq in BC1.
      split; [reflexivity|]. do 3 (split; [first [assumption|reflexivity]|]). exists (k + 1).
      split; [reflexivity|]. split; [reflexivity|]. split; [assumption|].
      apply avoids_snoc; assumption.
Qed.
