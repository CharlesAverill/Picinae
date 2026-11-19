(* wcscspn -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcschr, tail-calls wcslen)

   SEMANTICS
   ---------
   musl's src/string/wcscspn.c (pointer syntax written with [] and s[0],
   since C pointer syntax would close this comment):
       size_t wcscspn(const wchar_t s[], const wchar_t c[])
       {
           const wchar_t a[];
           if (!c[0]) return wcslen(s);
           if (!c[1]) return (s=wcschr(a=s, c[0])) ? s-a : wcslen(a);
           for (a=s; s[0] && !wcschr(c, s[0]); s++);
           return s-a;
       }
   The binary reads c[0] first; if it is 0 it tail-branches to wcslen
   (b 0x15fc18) with no frame.  Otherwise it builds a 48-byte frame (saved
   X29, X30, X19, X20, X21) and either (c[1] = 0) calls wcschr(s, c[0]),
   returning (r - s) >> 2, or restoring the frame and tail-branching to
   wcslen(s) when r = NULL; or (c[1] <> 0) runs the general loop at 0x15fb70
   calling wcschr(c, s[k]) and returns k at the first s[k] that is 0 or is
   found.  wcschr (always entered with a nonzero character, so it never
   calls wcslen) and wcslen are verified inline in wcscspn_prog = wcscspn +
   wcschr + wcslen lifts, with invariants at wcschr's loop head 0x15fae0
   (one disjunct per call site, told apart by X30) and at wcslen's entry and
   loop head that carry wcscspn's state.

   SPECIFICATION (man 3 wcscspn, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            size_t wcscspn(const wchar_t wcs[], const wchar_t reject[]);
     DESCRIPTION
            The wcscspn() function is the wide-character equivalent of the
            strcspn(3) function.  It determines the length of the longest
            initial segment of wcs which consists entirely of wide-characters
            not listed in reject.  In other words, it searches for the first
            occurrence in the wide-character string wcs of any of the
            characters in the wide-character string reject.
     RETURN VALUE
            The wcscspn() function returns the number of wide characters in
            the longest initial segment of wcs which consists entirely of
            wide-characters not listed in reject.  In other words, it returns
            the position of the first occurrence in the wide-character string
            wcs of any of the characters in the wide-character string reject,
            or wcslen(wcs) if there is none.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcscspn at 0x5fb44 (ELF vaddr); 0x15fb44 in Ghidra (image base 0x100000);
            callees wcschr at 0x5fab4 / 0x15fab4, wcslen at 0x5fc18 / 0x15fc18
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcscspn_armv8.v,
            ../lifted/wcschr_armv8.v and ../lifted/wcslen_armv8.v (combined
            as wcscspn_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = c (the reject set), SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.  All wide
            characters are 4-byte little-endian words (mem Ⓓ[.]).
   PRECONDITION (wcscspn_pre sp mem s c Ls Lc), stated explicitly:
            - s has wcslen Ls < 2^61 and s <> 0; c has wcslen Lc and c <> 0;
            - 48 <= sp < 2^64 and both strings including their terminators
              lie below sp-48, i.e. below wcscspn's own stack frame (they are
              only read, but the frame stores must not change them).
   Output:  On reaching any return (wcscspn's RET 0x15fbcc or wcslen's RET
            0x15fc34 after a tail call), wcscspn_post holds: there is k <= Ls
            such that wide characters 0..k-1 of s are nonzero and equal none
            of the Lc set characters (cspn), and wide character k is 0 or
            equals one of them (winset); X0 = k; memory is mem (empty set) or
            mem with only the 48-byte frame sp-48..sp-9 written; SP = sp,
            X30 = raddr and X19, X20, X21, X29 restored.  X22..X28 and
            Z8..Z15 are never written (wcscspn_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcscspn_armv8 wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcslen_proof.
Import ARM8Notations.
Open Scope N.

Definition wcscspn_prog : program :=
  updateall2 (updateall2 wcscspn_armv8.wcscspn_armv8 wcschr_armv8.wcschr_armv8) wcslen_armv8.wcslen_armv8.

Theorem wcscspn_prog_welltyped: welltyped_prog arm8typctx wcscspn_prog.
Proof.
  intros s a. unfold wcscspn_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (wcschr_armv8.wcschr_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (wcschr_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
    apply wcscspn_armv8.welltyped.
Qed.

Lemma wcscspn_prog_mono: ∀ prog, wcscspn_armv8.wcscspn_armv8 ⊆2 prog -> wcschr_armv8.wcschr_armv8 ⊆2 prog ->
  wcslen_armv8.wcslen_armv8 ⊆2 prog -> wcscspn_prog ⊆2 prog.
Proof.
  intros prog PA PB PC. unfold wcscspn_prog.
  rewrite <- (updateall2_subset _ _ PC). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ PB). apply updateall2_mono. exact PA.
Qed.

(* w occurs among the Lc wide characters of the set string at c *)
Definition winset (m:memory) (c Lc w:N) := ∃ j, j < Lc /\ m Ⓓ[c + 4*j] = w.
(* the first k wide characters at s are nonzero and NOT in the set *)
Definition cspn (m:memory) (s c Lc k:N) := ∀ i, i < k -> m Ⓓ[s + 4*i] ≠ 0 /\ ¬ winset m c Lc (m Ⓓ[s + 4*i]).
(* none of the first j set characters equals w *)
Definition notin_upto (m:memory) (c w j:N) := ∀ i, i < j -> m Ⓓ[c + 4*i] ≠ w.

Definition cspn_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20] [Ⓠ sp - 16 := x21].

Definition wcscspn_pre (sp mem s c Ls Lc : N) :=
  wcs_nilfree mem s Ls /\ mem Ⓓ[s + 4*Ls] = 0 /\ Ls < 2^61 /\
  wcs_nilfree mem c Lc /\ mem Ⓓ[c + 4*Lc] = 0 /\ 0 < c /\ 0 < s /\
  48 <= sp /\ sp < 2^64 /\ s + 4*Ls + 4 <= sp - 48 /\ c + 4*Lc + 4 <= sp - 48.

(* memory on return: unchanged (empty set: direct tail call to wcslen) or
   with wcscspn's 48-byte frame written *)
Definition wcscspn_post (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N) (st:store) :=
  ∃ k, k <= Ls /\ cspn mem s c Lc k /\ (mem Ⓓ[s + 4*k] = 0 \/ winset mem c Lc (mem Ⓓ[s + 4*k])) /\
  st R_X0 = k /\ (st V_MEM64 = mem \/ st V_MEM64 = cspn_frame sp mem raddr x19 x20 x21 x29) /\
  st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N).
  Definition E0 := cspn_frame sp mem raddr x19 x20 x21 x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (st:store) (a:addr) : T :=
    match a with
    | 0x15fb44 => Inv 0 (st R_X0 = s /\ st R_X1 = c /\ st V_MEM64 = mem /\ st R_SP = sp /\ st R_X30 = raddr /\
                         st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29)
    (* general loop (set has >= 2 characters) *)
    | 0x15fb70 => Inv 0 (∃ k, k <= Ls /\ st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ cspn mem s c Lc k /\
                         st V_MEM64 = E0 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48)
    (* wcschr's scan loop: called from the general loop (scan the set for s[k]) or
       from the one-character case (scan s for c[0]) *)
    | 0x15fae0 => Inv 0 ((∃ k j, k < Ls /\ j <= Lc /\ st R_X2 = c + 4*j /\ st R_X1 = mem Ⓓ[s + 4*k] /\
                         notin_upto mem c (mem Ⓓ[s + 4*k]) j /\
                         st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ st R_X30 = 0x15fb80 /\ cspn mem s c Lc k /\
                         st V_MEM64 = E0 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48) \/
                         (∃ i, i <= Ls /\ Lc = 1 /\ st R_X2 = s + 4*i /\ st R_X1 = mem Ⓓ[c] /\ mem Ⓓ[c] ≠ 0 /\
                         st R_X19 = s /\ st R_X20 = c /\ st R_X21 = s /\ st R_X30 = 0x15fb94 /\ cspn mem s c Lc i /\
                         st V_MEM64 = E0 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48))
    (* tail call to wcslen: no character of s is in the set *)
    | 0x15fc18 => Inv 0 (∃ M, st V_MEM64 = M /\ (M = mem \/ M = E0) /\ st R_X0 = s /\ cspn mem s c Lc Ls /\
                         st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr)
    | 0x15fc24 => Inv 0 (∃ M k, st V_MEM64 = M /\ (M = mem \/ M = E0) /\ k <= Ls /\ st R_X0 = s /\ st R_X1 = s + 4*k /\
                         cspn mem s c Lc Ls /\
                         st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr)
    | 0x15fbcc => Post 0 (wcscspn_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    | 0x15fc34 => Post 0 (wcscspn_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcscspn_prog invs.
  Definition invs0 := make_invs 0 wcscspn_prog invs.
End Invariants.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma asr4: ∀ k, k < 2305843009213693952 -> ashiftr 64 ((4*k) mod 2^64) 2 = k.
Proof.
  intros k K. rewrite N.mod_small by (change (2^64) with 18446744073709551616; lia).
  rewrite ashiftr64_small by (change (2^63) with 9223372036854775808; lia).
  rewrite N.shiftr_div_pow2. change (2^2) with 4. rewrite N.mul_comm, N.div_mul by discriminate. reflexivity.
Qed.


Lemma cspn_succ: ∀ m s c Lc k, cspn m s c Lc k -> m Ⓓ[s + 4*k] ≠ 0 -> ¬ winset m c Lc (m Ⓓ[s + 4*k]) ->
  cspn m s c Lc (k+1).
Proof.
  intros m s c Lc k S N0 W i I. destruct (N.lt_ge_cases i k). apply S; assumption.
  replace i with k by lia. split; assumption.
Qed.

Ltac kill :=
  try (match goal with
  | H: negb (0 =? 0) = true |- _ => simpl in H; discriminate H
  | H: (0 =? 0) = false |- _ => simpl in H; discriminate H
  | H: negb (_ =? 0) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H; lia
  | H: (_ =? 0) = true |- _ => apply N.eqb_eq in H; lia
  end).

Theorem wcscspn_partial_correctness:
  ∀ prog st sp mem raddr s c x19 x20 x21 x29 Ls Lc t xs'
    (PA: wcscspn_armv8.wcscspn_armv8 ⊆2 prog) (PB: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (PC: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fb44, st))
    (MDL: models arm8typctx st)
    (SP: st R_SP = sp) (MEM: st V_MEM64 = mem) (X30: st R_X30 = raddr)
    (X0: st R_X0 = s) (X1: st R_X1 = c)
    (X19: st R_X19 = x19) (X20: st R_X20 = x20) (X21: st R_X21 = x21) (X29: st R_X29 = x29)
    (PRE0: wcscspn_pre sp mem s c Ls Lc),
  satisfies_all prog (invs0 sp mem raddr s c x19 x20 x21 x29 Ls Lc)
                     (exits0 sp mem raddr s c x19 x20 x21 x29 Ls Lc) (xs'::t).
Proof.
  intros.
  assert (B: x19 < 2^64 /\ x20 < 2^64 /\ x21 < 2^64 /\ x29 < 2^64 /\ raddr < 2^64).
  { subst. splits; first [apply (MDL R_X19 64 eq_refl) | apply (MDL R_X20 64 eq_refl) | apply (MDL R_X21 64 eq_refl)
                         | apply (MDL R_X29 64 eq_refl) | apply (MDL R_X30 64 eq_refl)]. }
  eapply satisfies_all_pmono with (p1:=wcscspn_prog).
    apply wcscspn_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 PRE0 B START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscspn_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 B. rename t1 into t.
  destruct B as (B19 & B20 & B21 & B29 & B30).
  destruct PRE0 as (NFs & Zs & LsB & NFc & Zc & CP & SPos & SP48 & SPlt & BS & BCc).
  change (2^64) with 18446744073709551616 in *.
  change (2^61) with 2305843009213693952 in LsB.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  set (C := cspn_frame sp mem raddr x19 x20 x21 x29).
  assert (CD: ∀ a, a + 4 <= sp - 48 -> C Ⓓ[a] = mem Ⓓ[a]).
  { intros a A. unfold C, cspn_frame. memsimp. reflexivity. }
  assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, cspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q40: C Ⓠ[8 + (sp - 48)] = raddr) by (replace (8 + (sp - 48)) with (sp - 40) by lia; unfold C, cspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q32: C Ⓠ[16 + (sp - 48)] = x19) by (replace (16 + (sp - 48)) with (sp - 32) by lia; unfold C, cspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q24: C Ⓠ[24 + (sp - 48)] = x20) by (replace (24 + (sp - 48)) with (sp - 24) by lia; unfold C, cspn_frame; memsimp; apply N.mod_small; L64).
  assert (Q16: C Ⓠ[32 + (sp - 48)] = x21) by (replace (32 + (sp - 48)) with (sp - 16) by lia; unfold C, cspn_frame; memsimp; apply N.mod_small; L64).
  unfold E0. change (cspn_frame sp mem raddr x19 x20 x21 x29) with C.
  destruct_inv 64 PRE.

  - (* wcschr's scan loop *)
    destruct PRE as [PRE|PRE].
    + (* general case: scanning the set for s[k] *)
      destruct PRE as (k & j & KL & JL & X2 & X1 & NI & X19 & X20 & X21 & X30 & SPN & MEM & SP & X29).
      unfold E0 in MEM |- *. change (cspn_frame sp mem raddr x19 x20 x21 x29) with C in MEM |- *.
      assert (CDj: C Ⓓ[c + 4*j] = mem Ⓓ[c + 4*j]) by (apply CD; lia).
      repeat arm8_step. all: try rewrite X30. all: repeat arm8_step.
      all: rewrite ?CDj in *.
      all: kill.
      all: first
      [ (* s[k] not in the set: next k *)
        match goal with H: (_ Ⓓ[_] =? 0) = true |- _ => apply N.eqb_eq in H; rename H into HZ end;
        assert (JE: j = Lc) by (destruct (N.lt_ge_cases j Lc); [exfalso; apply (NFc j); assumption | lia]);
        subst j;
        assert (SK: mem Ⓓ[s + 4*k] ≠ 0) by (apply NFs; lia);
        exists (k+1); splits; try assumption; try reflexivity; try lia;
        try (rewrite N.mod_small by L64; lia);
        apply cspn_succ; [assumption | exact SK | intros (j' & J' & W); exact (NI j' J' W)]
      | (* s[k] found in the set: return k *)
        match goal with H: (_ Ⓓ[_] =? _ Ⓓ[_]) = true |- _ => apply N.eqb_eq in H; rename H into HE end;
        match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; rename H into HN end;
        assert (JL': j < Lc) by (destruct (N.lt_ge_cases j Lc); [assumption | replace j with Lc in HN by lia; contradiction]);
        exists k; splits; try assumption; try reflexivity; try lia;
        first [ right; exists j; split; [exact JL' | exact HE] | apply asr4; lia | right; reflexivity ]
      | (* mismatch: next set character *)
        match goal with H: (_ Ⓓ[_] =? _ Ⓓ[_]) = false |- _ => apply N.eqb_neq in H; rename H into HE end;
        match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; rename H into HN end;
        assert (JL': j < Lc) by (destruct (N.lt_ge_cases j Lc); [assumption | replace j with Lc in HN by lia; contradiction]);
        left; exists k, (j+1); splits; try assumption; try reflexivity; try lia;
        try (rewrite N.mod_small by L64; lia);
        intros i I; destruct (N.lt_ge_cases i j); [apply NI; assumption | replace i with j by lia; exact HE] ].
    + (* one-character set: scanning s for c[0] *)
      destruct PRE as (i & IL & LC1 & X2 & X1 & C0 & X19 & X20 & X21 & X30 & SPN & MEM & SP & X29).
      unfold E0 in MEM |- *. change (cspn_frame sp mem raddr x19 x20 x21 x29) with C in MEM |- *.
      assert (CDi: C Ⓓ[s + 4*i] = mem Ⓓ[s + 4*i]) by (apply CD; lia).
      repeat arm8_step. all: try rewrite X30. all: repeat arm8_step.
      all: rewrite ?CDi in *.
      all: kill.
      all: first
      [ (* s[i] = 0: c[0] does not occur; tail call wcslen *)
        match goal with H: (_ Ⓓ[_] =? 0) = true |- _ => apply N.eqb_eq in H; rename H into HZ end;
        assert (IE: i = Ls) by (destruct (N.lt_ge_cases i Ls); [exfalso; apply (NFs i); assumption | lia]);
        subst i;
        exists C; splits; try assumption; try reflexivity; try lia;
        right; reflexivity
      | (* found c[0] at i *)
        match goal with H: (_ Ⓓ[_] =? _ Ⓓ[_]) = true |- _ => apply N.eqb_eq in H; rename H into HE end;
        exists i; splits; try assumption; try reflexivity; try lia;
        first [ right; exists 0; split; [lia | rewrite N.mul_0_r, N.add_0_r; symmetry; exact HE]
              | apply asr4; lia | right; reflexivity ]
      | (* mismatch: next i *)
        match goal with H: (_ Ⓓ[_] =? _ Ⓓ[_]) = false |- _ => apply N.eqb_neq in H; rename H into HE end;
        match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; rename H into HN end;
        assert (IL': i < Ls) by (destruct (N.lt_ge_cases i Ls); [assumption | replace i with Ls in HN by lia; contradiction]);
        right; exists (i+1); splits; try assumption; try reflexivity; try lia;
        try (rewrite N.mod_small by L64; lia);
        apply cspn_succ; [assumption | exact HN | intros (j & J & W); replace j with 0 in W by lia;
          rewrite N.mul_0_r, N.add_0_r in W; apply HE; symmetry; exact W] ].
  - (* entry *)
    destruct PRE as (R0 & R1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    repeat arm8_step.
    all: kill.
    all: first
    [ (* empty set: tail call wcslen *)
      match goal with H: (_ Ⓓ[_] =? 0) = true |- _ => apply N.eqb_eq in H; rename H into HZ end;
      assert (L0: Lc = 0) by (destruct (N.eq_dec Lc 0); [assumption | exfalso; apply (NFc 0); [lia | rewrite N.mul_0_r, N.add_0_r; exact HZ]]);
      eexists; splits; try assumption; try reflexivity;
      [ left; reflexivity
      | intros i I; split; [apply NFs; exact I | intros (j & J & _); lia] ]
    | (* wcschr's c = 0 branch is unreachable *)
      match goal with H: negb _ = false |- _ => apply cbnz32_false in H; [|apply dword_lt32] end;
      match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; contradiction end
    | (* one-character set *)
      match goal with H: (_ Ⓓ[_] =? 0) = true |- _ => rename H into HZ1 end;
      match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; rename H into HN end;
      assert (L1: 1 <= Lc) by (destruct (N.eq_dec Lc 0) as [E|E]; [rewrite E, N.mul_0_r, N.add_0_r in Zc; contradiction | lia]);
      rewrite !MS in HZ1 by lia; rewrite CD in HZ1 by lia; apply N.eqb_eq in HZ1;
      assert (LC1: Lc = 1) by (destruct (N.lt_ge_cases 1 Lc); [exfalso; apply (NFc 1); [assumption | replace (c + 4*1) with (4 + c) by lia; exact HZ1] | lia]);
      right; exists 0; splits; try assumption; try reflexivity; try lia;
      try (intros i I; lia);
      try (unfold E0, cspn_frame; rewrite !MS by lia; reflexivity);
      rewrite MS by lia; reflexivity
    | (* general case *)
      exists 0; splits; try assumption; try reflexivity; try lia;
      try (intros i I; lia);
      try (unfold E0, cspn_frame; rewrite !MS by lia; reflexivity);
      rewrite MS by lia; reflexivity ].
  - (* general loop head *)
    destruct PRE as (k & KL & X19 & X20 & X21 & SPN & MEM & SP & X29).
    unfold E0 in MEM |- *. change (cspn_frame sp mem raddr x19 x20 x21 x29) with C in MEM |- *.
    assert (CDk: C Ⓓ[s + 4*k] = mem Ⓓ[s + 4*k]) by (apply CD; lia).
    repeat arm8_step.
    all: rewrite ?CDk in *.
    + (* s[k] = 0: return k *)
      apply N.eqb_eq in BC.
      exists k. splits; try assumption; try reflexivity; try lia.
      all: first [left; exact BC | apply asr4; lia | right; reflexivity].
    + (* call wcschr(c, s[k]) *)
      apply N.eqb_neq in BC.
      assert (KL': k < Ls) by (destruct (N.lt_ge_cases k Ls); [assumption | replace k with Ls in BC by lia; contradiction]).
      left. exists k, 0. splits; try assumption; try reflexivity; try lia.
      intros i I. lia.
    + match goal with H: negb _ = false |- _ => apply cbnz32_false in H; [|apply dword_lt32] end.
      match goal with H: (_ Ⓓ[_] =? 0) = false |- _ => apply N.eqb_neq in H; contradiction end.
  - (* wcslen entry *)
    destruct PRE as (M & MEM & MD & X0 & CS & SP & X19 & X20 & X21 & X29 & X30).
    repeat arm8_step.
    exists M, 0. splits; try assumption; try reflexivity; try lia.
  - (* wcslen loop *)
    destruct PRE as (M & k & MEM & MD & KL & X0 & X1 & CS & SP & X19 & X20 & X21 & X29 & X30).
    unfold E0 in MD |- *. change (cspn_frame sp mem raddr x19 x20 x21 x29) with C in MD |- *.
    assert (MRk: M Ⓓ[s + 4*k] = mem Ⓓ[s + 4*k]) by (destruct MD as [-> | ->]; [reflexivity | apply CD; lia]).
    repeat arm8_step.
    all: rewrite ?MRk in *.
    + (* nonzero: next *)
      apply cbnz32_true in BC; [|apply dword_lt32].
      assert (KL': k < Ls) by (destruct (N.lt_ge_cases k Ls); [assumption | replace k with Ls in BC by lia; contradiction]).
      exists M, (k+1). splits; try assumption; try reflexivity; try lia.
      all: try (rewrite N.mod_small by L64; lia).
    + (* terminator: k = Ls *)
      apply cbnz32_false in BC; [|apply dword_lt32].
      assert (KE: k = Ls) by (destruct (N.lt_ge_cases k Ls); [exfalso; apply (NFs k); assumption | lia]).
      subst k.
      exists Ls. splits; try assumption; try reflexivity; try lia.
      all: first [left; exact BC | apply asr4; lia | destruct MD as [H|H]; rewrite H; [left|right]; reflexivity].
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X19-X21/X29/X30 are
   never written by wcscspn, wcschr or wcslen. *)
Theorem wcscspn_preserves_other_callee_saved:
  ∀ r, In r (R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcscspn_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
