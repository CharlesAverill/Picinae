(* wcsspn -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcschr)

   SEMANTICS
   ---------
   musl's src/string/wcsspn.c:
       size_t wcsspn(const wchar_t s[], const wchar_t c[])
       {
           const wchar_t a[] = s;   (pointer copy)
           for (; s[0] && wcschr(c, s[0]); s++);
           return s - a;
       }
   compiled with a 48-byte frame (stp x29,x30,[sp,#-48]!; X19 = s cursor,
   X20 = c, X21 = start, all saved in the frame), a loop at 0x15fe90 that
   loads w1 = s[0], stops on 0 (cbz) and otherwise calls wcschr(c, w1)
   (bl 0x15fab4), continuing while the result is non-NULL, and returns
   (s - a) >> 2 (asr).  Because w1 is never 0 at the call, wcschr always
   takes its scan loop (cbnz w1) and never calls wcslen; wcschr's code is
   verified here inline inside wcsspn_prog = wcsspn + wcschr lifts, with an
   invariant at wcschr's loop head 0x15fae0 that carries wcsspn's state.

   SPECIFICATION (man 3 wcsspn, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            size_t wcsspn(const wchar_t wcs[], const wchar_t accept[]);
     DESCRIPTION
            The wcsspn() function is the wide-character equivalent of the
            strspn(3) function.  It determines the length of the longest
            initial segment of wcs which consists entirely of wide-characters
            listed in accept.  In other words, it searches for the first
            occurrence in the wide-character string wcs of a wide-character
            not contained in the wide-character string accept.
     RETURN VALUE
            The wcsspn() function returns the number of wide characters in
            the longest initial segment of wcs which consists entirely of
            wide-characters listed in accept.  In other words, it returns the
            position of the first occurrence in the wide-character string wcs
            of a wide-character not contained in the wide-character string
            accept, or wcslen(wcs) if there is none.
   (Pointer parameters written with [] here because C pointer syntax would
   close this comment.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcsspn at 0x5fe6c (ELF vaddr); 0x15fe6c in Ghidra (image base 0x100000);
            callee wcschr at 0x5fab4 / 0x15fab4
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcsspn_armv8.v and
            ../lifted/wcschr_armv8.v (combined as wcsspn_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = c (the accept set), SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.  All wide
            characters are 4-byte little-endian words (mem Ⓓ[.]).
   PRECONDITION (wcsspn_pre sp mem s c Ls Lc), stated explicitly:
            - s has wcslen Ls < 2^61 (words s+4i, i < Ls, nonzero; word
              s+4Ls is 0); c has wcslen Lc (same) and c <> 0 (not NULL);
            - 48 <= sp < 2^64 and both strings including their terminators
              lie below sp-48, i.e. below wcsspn's own stack frame (they are
              only read, but the frame stores must not change them).
   Output:  On reaching wcsspn's RET (0x15feb8), wcsspn_post holds: there is
            k <= Ls such that wide characters 0..k-1 of s are nonzero and
            each equals some wide character j < Lc of c (spn), and wide
            character k is 0 or equals none of them (not winset); X0 = k;
            memory = mem with only the 48-byte frame sp-48..sp-9 written
            (saved x29, raddr, x19, x20, x21); SP = sp, X30 = raddr and
            X19, X20, X21, X29 restored.  X22..X28 and Z8..Z15 are never
            written (wcsspn_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsspn_armv8 wcschr_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame.
From Grok.proofs Require Import wcslen_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsspn_prog : program := updateall2 wcsspn_armv8.wcsspn_armv8 wcschr_armv8.wcschr_armv8.

Theorem wcsspn_prog_welltyped: welltyped_prog arm8typctx wcsspn_prog.
Proof.
  intros s a. unfold wcsspn_prog, updateall2, updateall.
  destruct (wcschr_armv8.wcschr_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wcschr_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcsspn_armv8.welltyped.
Qed.

Lemma wcsspn_prog_mono: ∀ prog, wcsspn_armv8.wcsspn_armv8 ⊆2 prog -> wcschr_armv8.wcschr_armv8 ⊆2 prog -> wcsspn_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold wcsspn_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* w occurs among the Lc wide characters of the set string at c *)
Definition winset (m:memory) (c Lc w:N) := ∃ j, j < Lc /\ m Ⓓ[c + 4*j] = w.
(* the first k wide characters at s are nonzero and in the set *)
Definition spn (m:memory) (s c Lc k:N) := ∀ i, i < k -> m Ⓓ[s + 4*i] ≠ 0 /\ winset m c Lc (m Ⓓ[s + 4*i]).
(* none of the first j set characters equals w *)
Definition notin_upto (m:memory) (c w j:N) := ∀ i, i < j -> m Ⓓ[c + 4*i] ≠ w.

Definition sspn_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20] [Ⓠ sp - 16 := x21].

Definition wcsspn_pre (sp mem s c Ls Lc : N) :=
  wcs_nilfree mem s Ls /\ mem Ⓓ[s + 4*Ls] = 0 /\ Ls < 2^61 /\
  wcs_nilfree mem c Lc /\ mem Ⓓ[c + 4*Lc] = 0 /\ 0 < c /\
  48 <= sp /\ sp < 2^64 /\ s + 4*Ls + 4 <= sp - 48 /\ c + 4*Lc + 4 <= sp - 48.

Definition wcsspn_post (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N) (st:store) :=
  ∃ k, k <= Ls /\ spn mem s c Lc k /\ (mem Ⓓ[s + 4*k] = 0 \/ ¬ winset mem c Lc (mem Ⓓ[s + 4*k])) /\
  st R_X0 = k /\ st V_MEM64 = sspn_frame sp mem raddr x19 x20 x21 x29 /\
  st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N).
  Definition E0 := sspn_frame sp mem raddr x19 x20 x21 x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (st:store) (a:addr) : T :=
    match a with
    | 0x15fe6c => Inv 0 (st R_X0 = s /\ st R_X1 = c /\ st V_MEM64 = mem /\ st R_SP = sp /\ st R_X30 = raddr /\
                         st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29)
    | 0x15fe90 => Inv 0 (∃ k, k <= Ls /\ st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ spn mem s c Lc k /\
                         st V_MEM64 = E0 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48)
    (* wcschr's scan loop, called from wcsspn with a nonzero character *)
    | 0x15fae0 => Inv 0 (∃ k j, k < Ls /\ j <= Lc /\ st R_X2 = c + 4*j /\ st R_X1 = mem Ⓓ[s + 4*k] /\
                         notin_upto mem c (mem Ⓓ[s + 4*k]) j /\
                         st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ st R_X30 = 0x15fea0 /\ spn mem s c Lc k /\
                         st V_MEM64 = E0 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48)
    | 0x15feb8 => Post 0 (wcsspn_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsspn_prog invs.
  Definition invs0 := make_invs 0 wcsspn_prog invs.
End Invariants.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].


Lemma asr4: ∀ k, k < 2305843009213693952 -> ashiftr 64 ((4*k) mod 2^64) 2 = k.
Proof.
  intros k K. rewrite N.mod_small by (change (2^64) with 18446744073709551616; lia).
  rewrite ashiftr64_small by (change (2^63) with 9223372036854775808; lia).
  rewrite N.shiftr_div_pow2. change (2^2) with 4. rewrite N.mul_comm, N.div_mul by discriminate. reflexivity.
Qed.

Lemma spn_succ: ∀ m s c Lc k, spn m s c Lc k -> m Ⓓ[s + 4*k] ≠ 0 -> winset m c Lc (m Ⓓ[s + 4*k]) ->
  spn m s c Lc (k+1).
Proof.
  intros m s c Lc k S N0 W i I. destruct (N.lt_ge_cases i k). apply S; assumption.
  replace i with k by lia. split; assumption.
Qed.

Theorem wcsspn_partial_correctness:
  ∀ prog st sp mem raddr s c x19 x20 x21 x29 Ls Lc t xs'
    (P1: wcsspn_armv8.wcsspn_armv8 ⊆2 prog) (P0: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fe6c, st))
    (MDL: models arm8typctx st)
    (SP: st R_SP = sp) (MEM: st V_MEM64 = mem) (X30: st R_X30 = raddr)
    (X0: st R_X0 = s) (X1: st R_X1 = c)
    (X19: st R_X19 = x19) (X20: st R_X20 = x20) (X21: st R_X21 = x21) (X29: st R_X29 = x29)
    (PRE0: wcsspn_pre sp mem s c Ls Lc),
  satisfies_all prog (invs0 sp mem raddr s c x19 x20 x21 x29 Ls Lc)
                     (exits0 sp mem raddr s c x19 x20 x21 x29 Ls Lc) (xs'::t).
Proof.
  intros.
  assert (B: x19 < 2^64 /\ x20 < 2^64 /\ x21 < 2^64 /\ x29 < 2^64 /\ raddr < 2^64).
  { subst. splits; first [apply (MDL R_X19 64 eq_refl) | apply (MDL R_X20 64 eq_refl) | apply (MDL R_X21 64 eq_refl)
                         | apply (MDL R_X29 64 eq_refl) | apply (MDL R_X30 64 eq_refl)]. }
  eapply satisfies_all_pmono with (p1:=wcsspn_prog).
    apply wcsspn_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 PRE0 B START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsspn_prog_welltyped. intro MDL1.
  pose proof (MDL1 R_X19 64 eq_refl) as W19. pose proof (MDL1 R_X20 64 eq_refl) as W20.
  pose proof (MDL1 R_X21 64 eq_refl) as W21. pose proof (MDL1 R_X29 64 eq_refl) as W29.
  pose proof (MDL1 R_X30 64 eq_refl) as W30. pose proof (MDL1 R_X1 64 eq_refl) as W1.
  clear - PRE MDL1 PRE0 B W19 W20 W21 W29 W30 W1. rename t1 into t.
  destruct B as (B19 & B20 & B21 & B29 & B30).
  destruct PRE0 as (NFs & Zs & LsB & NFc & Zc & CP & SP48 & SPlt & BS & BC0).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W20, W21, W29, W30, W1. clear WW.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  set (C := sspn_frame sp mem raddr x19 x20 x21 x29).
  assert (CD: ∀ a, a + 4 <= sp - 48 -> C Ⓓ[a] = mem Ⓓ[a]).
  { intros a A. unfold C, sspn_frame. memsimp. reflexivity. }
  assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, sspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, sspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, sspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, sspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, sspn_frame; memsimp; apply N.mod_small; L64).
  change (2^61) with 2305843009213693952 in LsB.
  assert (Q16': C Ⓠ[32 + (sp - 48)] = x21) by (replace (32 + (sp - 48)) with (sp - 16) by lia; exact Q16).
  assert (Q24': C Ⓠ[24 + (sp - 48)] = x20) by (replace (24 + (sp - 48)) with (sp - 24) by lia; exact Q24).
  assert (Q32': C Ⓠ[16 + (sp - 48)] = x19) by (replace (16 + (sp - 48)) with (sp - 32) by lia; exact Q32).
  assert (Q40': C Ⓠ[8 + (sp - 48)] = raddr) by (replace (8 + (sp - 48)) with (sp - 40) by lia; exact Q40).
  unfold E0. change (sspn_frame sp mem raddr x19 x20 x21 x29) with C.
  destruct_inv 64 PRE.
  - (* wcschr's scan loop inside wcsspn *)
    destruct PRE as (k & j & KL & JL & X2 & X1 & NI & X19 & X20 & X21 & X30 & SPN & MEM & SP & X29).
    unfold E0 in MEM |- *. change (sspn_frame sp mem raddr x19 x20 x21 x29) with C in MEM |- *.
    assert (CDj: C Ⓓ[c + 4*j] = mem Ⓓ[c + 4*j]) by (apply CD; lia).
    repeat arm8_step. all: try rewrite X30. all: repeat arm8_step.
    all: rewrite ?CDj in *.
    all: try (simpl in BC1; discriminate BC1).
    all: try (apply Bool.negb_false_iff, N.eqb_eq in BC2; lia).
    + (* wcschr returned NULL: the character is not in the set; return k *)
      apply N.eqb_eq in BC.
      assert (JE: j = Lc) by (destruct (N.lt_ge_cases j Lc); [exfalso; apply (NFc j); assumption | lia]).
      subst j.
      exists k. splits; try assumption; try reflexivity; try lia.
      right. intros (j' & J' & W). apply (NI j' J'). exact W.
      apply asr4; lia.
    + (* found in the set: advance to k+1 *)
      apply N.eqb_eq in BC1. apply N.eqb_neq in BC.
      assert (JL': j < Lc) by (destruct (N.lt_ge_cases j Lc); [assumption | replace j with Lc in BC by lia; contradiction]).
      exists (k+1). splits; try assumption; try reflexivity; try lia.
      all: try (rewrite N.mod_small by L64; lia).
      apply spn_succ. assumption. rewrite <- BC1. exact BC. exists j. split. exact JL'. exact BC1.
    + (* mismatch: next set character *)
      apply N.eqb_neq in BC1, BC.
      assert (JL': j < Lc) by (destruct (N.lt_ge_cases j Lc); [assumption | replace j with Lc in BC by lia; contradiction]).
      exists k, (j+1). splits; try assumption; try reflexivity; try lia.
      all: try (rewrite N.mod_small by L64; lia).
      intros i I. destruct (N.lt_ge_cases i j). apply NI; assumption. replace i with j by lia. exact BC1.
  - (* entry *)
    destruct PRE as (R0 & R1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    repeat arm8_step.
    exists 0. splits; try reflexivity; try lia.
    intros i I. lia.
    unfold E0, sspn_frame. rewrite !MS by lia. reflexivity.
    all: rewrite MS by lia; reflexivity.
  - (* outer loop head *)
    destruct PRE as (k & KL & X19 & X20 & X21 & SPN & MEM & SP & X29).
    unfold E0 in MEM |- *. change (sspn_frame sp mem raddr x19 x20 x21 x29) with C in MEM |- *.
    assert (CDk: C Ⓓ[s + 4*k] = mem Ⓓ[s + 4*k]) by (apply CD; lia).
    repeat arm8_step.
    all: rewrite ?CDk in *.
    + (* terminator: return k *)
      apply N.eqb_eq in BC.
      exists k. splits; try assumption; try reflexivity; try lia.
      all: first [left; exact BC | apply asr4; lia].
    + (* call wcschr *)
      apply N.eqb_neq in BC.
      assert (KL': k < Ls) by (destruct (N.lt_ge_cases k Ls); [assumption | replace k with Ls in BC by lia; contradiction]).
      exists k, 0. splits; try assumption; try reflexivity; try lia.
      intros i I. lia.
    + apply N.eqb_neq in BC. apply cbnz32_false in BC1; [|apply dword_lt32]. contradiction.
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X19-X21/X29/X30 are
   never written by wcsspn or wcschr. *)
Theorem wcsspn_preserves_other_callee_saved:
  ∀ r, In r (R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcsspn_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
