(* wcspbrk -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcscspn)

   SEMANTICS
   ---------
   musl's src/string/wcspbrk.c (pointer syntax written with [] and s[0],
   since C pointer syntax would close this comment):
       wchar_t[] wcspbrk(const wchar_t s[], const wchar_t b[])
       {
           s += wcscspn(s, b);
           return s[0] ? s : NULL;
       }
   compiled with a 32-byte frame (stp x29,x30,[sp,#-32]!; X19 = s saved at
   sp-16), bl wcscspn (0x15fb44), then X1 = s + 4k, w0 = s[k], and
   csel x0,x1,xzr,ne.  wcscspn (with its inlined wcschr and wcslen) is
   re-verified here inside wcspbrk_prog = wcspbrk + wcscspn_prog against the
   same invariants as in wcscspn_proof.v (wcscspn_in_wcspbrk, callee id 0),
   and the call is composed with Picinae's perform_call.

   SPECIFICATION (man 3 wcspbrk, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t[] wcspbrk(const wchar_t wcs[], const wchar_t accept[]);
     DESCRIPTION
            The wcspbrk() function is the wide-character equivalent of the
            strpbrk(3) function.  It searches for the first occurrence in the
            wide-character string pointed to by wcs of any of the characters
            in the wide-character string pointed to by accept.
     RETURN VALUE
            The wcspbrk() function returns a pointer to the first occurrence
            in wcs of any of the characters listed in accept.  If wcs
            contains none of these characters, NULL is returned.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcspbrk at 0x5fdf0 (ELF vaddr); 0x15fdf0 in Ghidra (image base 0x100000);
            callees wcscspn 0x5fb44 / 0x15fb44, wcschr 0x5fab4 / 0x15fab4,
            wcslen 0x5fc18 / 0x15fc18
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcspbrk_armv8.v,
            ../lifted/wcscspn_armv8.v, ../lifted/wcschr_armv8.v and
            ../lifted/wcslen_armv8.v (combined as wcspbrk_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = c (the accept set), SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.  All wide
            characters are 4-byte little-endian words (mem Ⓓ[.]).
   PRECONDITION (wcspbrk_pre sp mem s c Ls Lc), stated explicitly:
            - s has wcslen Ls < 2^61 and s <> 0; c has wcslen Lc and c <> 0;
            - 80 <= sp < 2^64 and both strings including their terminators
              lie below sp-80, i.e. below wcspbrk's 32-byte frame and the
              48-byte frame of the wcscspn it calls (they are only read).
   Output:  On reaching wcspbrk's RET (0x15fe1c), wcspbrk_post holds: there
            is k <= Ls such that wide characters 0..k-1 of s are nonzero and
            equal none of the Lc set characters (cspn), and either wide
            character k is 0 and X0 = 0 (NULL), or it is nonzero, equals one
            of the set characters (winset) and X0 = s + 4k; memory is mem with
            wcspbrk's frame written (pbrk_frame) and possibly wcscspn's frame
            below it; SP = sp, X30 = raddr, X19, X20, X21, X29 restored.
            X22..X28 and Z8..Z15 are never written
            (wcspbrk_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcspbrk_armv8 wcscspn_armv8 wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcslen_proof wcscspn_proof.
Import ARM8Notations.
Open Scope N.

Definition wcspbrk_prog : program := updateall2 wcspbrk_armv8.wcspbrk_armv8 wcscspn_prog.

Theorem wcspbrk_prog_welltyped: welltyped_prog arm8typctx wcspbrk_prog.
Proof.
  intros s a. unfold wcspbrk_prog at 1, updateall2, updateall.
  destruct (wcscspn_prog s a) as [[sz q]|] eqn:T0.
    pose proof (wcscspn_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcspbrk_armv8.welltyped.
Qed.

Lemma wcspbrk_prog_mono: ∀ prog, wcspbrk_armv8.wcspbrk_armv8 ⊆2 prog -> wcscspn_armv8.wcscspn_armv8 ⊆2 prog ->
  wcschr_armv8.wcschr_armv8 ⊆2 prog -> wcslen_armv8.wcslen_armv8 ⊆2 prog -> wcspbrk_prog ⊆2 prog.
Proof.
  intros prog PD PA PB PC. unfold wcspbrk_prog.
  rewrite <- (updateall2_subset _ _ (wcscspn_prog_mono prog PA PB PC)). apply updateall2_mono. exact PD.
Qed.

(* wcspbrk's 32-byte frame: saved X29, X30, X19 *)
Definition pbrk_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp - 32 := x29] [Ⓠ sp - 24 := raddr] [Ⓠ sp - 16 := x19].

Definition wcspbrk_pre (sp mem s c Ls Lc : N) :=
  wcs_nilfree mem s Ls /\ mem Ⓓ[s + 4*Ls] = 0 /\ Ls < 2^61 /\
  wcs_nilfree mem c Lc /\ mem Ⓓ[c + 4*Lc] = 0 /\ 0 < c /\ 0 < s /\
  80 <= sp /\ sp < 2^64 /\ s + 4*Ls + 4 <= sp - 80 /\ c + 4*Lc + 4 <= sp - 80.

Definition wcspbrk_post (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N) (st:store) :=
  ∃ k, k <= Ls /\ cspn mem s c Lc k /\
  ((mem Ⓓ[s + 4*k] = 0 /\ st R_X0 = 0) \/
   (mem Ⓓ[s + 4*k] ≠ 0 /\ winset mem c Lc (mem Ⓓ[s + 4*k]) /\ st R_X0 = s + 4*k)) /\
  (st V_MEM64 = pbrk_frame sp mem raddr x19 x29 \/
   st V_MEM64 = cspn_frame (sp - 32) (pbrk_frame sp mem raddr x19 x29) 0x15fe04 s x20 x21 (sp - 32)) /\
  st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr s c x19 x20 x21 x29 Ls Lc : N).
  Definition binvs T (Inv Post: inv_type T) (NoInv:T) (st:store) (a:addr) : T :=
    match a with
    (* wcspbrk (id 1) *)
    | 0x15fdf0 => Inv 1 (st R_X0 = s /\ st R_X1 = c /\ st V_MEM64 = mem /\ st R_SP = sp /\ st R_X30 = raddr /\
                         st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29)
    | 0x15fe1c => Post 1 (wcspbrk_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    (* wcscspn with its inlined wcschr/wcslen (id 0), as in wcscspn_proof *)
    | 0x15fb44 => Inv 0 (st R_X0 = s /\ st R_X1 = c /\ st V_MEM64 = mem /\ st R_SP = sp /\ st R_X30 = raddr /\
                         st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29)
    (* general loop (set has >= 2 characters) *)
    | 0x15fb70 => Inv 0 (∃ k, k <= Ls /\ st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ cspn mem s c Lc k /\
                         st V_MEM64 = E0 sp mem raddr x19 x20 x21 x29 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48)
    (* wcschr's scan loop: called from the general loop (scan the set for s[k]) or
       from the one-character case (scan s for c[0]) *)
    | 0x15fae0 => Inv 0 ((∃ k j, k < Ls /\ j <= Lc /\ st R_X2 = c + 4*j /\ st R_X1 = mem Ⓓ[s + 4*k] /\
                         notin_upto mem c (mem Ⓓ[s + 4*k]) j /\
                         st R_X19 = s + 4*k /\ st R_X20 = c /\ st R_X21 = s /\ st R_X30 = 0x15fb80 /\ cspn mem s c Lc k /\
                         st V_MEM64 = E0 sp mem raddr x19 x20 x21 x29 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48) \/
                         (∃ i, i <= Ls /\ Lc = 1 /\ st R_X2 = s + 4*i /\ st R_X1 = mem Ⓓ[c] /\ mem Ⓓ[c] ≠ 0 /\
                         st R_X19 = s /\ st R_X20 = c /\ st R_X21 = s /\ st R_X30 = 0x15fb94 /\ cspn mem s c Lc i /\
                         st V_MEM64 = E0 sp mem raddr x19 x20 x21 x29 /\ st R_SP = sp - 48 /\ st R_X29 = sp - 48))
    (* tail call to wcslen: no character of s is in the set *)
    | 0x15fc18 => Inv 0 (∃ M, st V_MEM64 = M /\ (M = mem \/ M = E0 sp mem raddr x19 x20 x21 x29) /\ st R_X0 = s /\ cspn mem s c Lc Ls /\
                         st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr)
    | 0x15fc24 => Inv 0 (∃ M k, st V_MEM64 = M /\ (M = mem \/ M = E0 sp mem raddr x19 x20 x21 x29) /\ k <= Ls /\ st R_X0 = s /\ st R_X1 = s + 4*k /\
                         cspn mem s c Lc Ls /\
                         st R_SP = sp /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\ st R_X29 = x29 /\ st R_X30 = raddr)
    | 0x15fbcc => Post 0 (wcscspn_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    | 0x15fc34 => Post 0 (wcscspn_post sp mem raddr s c x19 x20 x21 x29 Ls Lc st)
    | _ => NoInv
    end.
  Definition bexits0 := make_exits 0 wcspbrk_prog binvs.
  Definition binvs0 := make_invs 0 wcspbrk_prog binvs.
  Definition bexits1 := make_exits 1 wcspbrk_prog binvs.
  Definition binvs1 := make_invs 1 wcspbrk_prog binvs.
End Invariants.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma cspn_ext: ∀ m1 m2 s c Lc k b, (∀ a, a + 4 <= b -> m1 Ⓓ[a] = m2 Ⓓ[a]) ->
  s + 4*k <= b -> c + 4*Lc + 4 <= b -> cspn m1 s c Lc k -> cspn m2 s c Lc k.
Proof.
  intros m1 m2 s c Lc k b EQ BS BC CS i I.
  destruct (CS i I) as [NZ NW]. rewrite EQ in NZ, NW by lia.
  split. exact NZ. intros (j & J & E). apply NW. exists j. split. exact J. rewrite EQ by lia. exact E.
Qed.

Lemma winset_ext: ∀ m1 m2 c Lc w b, (∀ a, a + 4 <= b -> m1 Ⓓ[a] = m2 Ⓓ[a]) ->
  c + 4*Lc + 4 <= b -> winset m1 c Lc w -> winset m2 c Lc w.
Proof.
  intros m1 m2 c Lc w b EQ BC (j & J & E). exists j. split. exact J. rewrite <- EQ by lia. exact E.
Qed.

Lemma nilfree_ext: ∀ m1 m2 p L b, (∀ a, a + 4 <= b -> m1 Ⓓ[a] = m2 Ⓓ[a]) ->
  p + 4*L + 4 <= b -> wcs_nilfree m2 p L -> wcs_nilfree m1 p L.
Proof. intros m1 m2 p L b EQ B NF i I. rewrite EQ by lia. apply NF; exact I. Qed.

Theorem wcscspn_in_wcspbrk:
  ∀ prog st sp mem raddr s c x19 x20 x21 x29 Ls Lc t xs'
    (P: wcspbrk_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fb44, st))
    (MDL: models arm8typctx st)
    (SP: st R_SP = sp) (MEM: st V_MEM64 = mem) (X30: st R_X30 = raddr)
    (X0: st R_X0 = s) (X1: st R_X1 = c)
    (X19: st R_X19 = x19) (X20: st R_X20 = x20) (X21: st R_X21 = x21) (X29: st R_X29 = x29)
    (PRE0: wcscspn_pre sp mem s c Ls Lc),
  satisfies_all prog (binvs0 sp mem raddr s c x19 x20 x21 x29 Ls Lc)
                     (bexits0 sp mem raddr s c x19 x20 x21 x29 Ls Lc) (xs'::t).
Proof.
  intros.
  assert (B: x19 < 2^64 /\ x20 < 2^64 /\ x21 < 2^64 /\ x29 < 2^64 /\ raddr < 2^64).
  { subst. splits; first [apply (MDL R_X19 64 eq_refl) | apply (MDL R_X20 64 eq_refl) | apply (MDL R_X21 64 eq_refl)
                         | apply (MDL R_X29 64 eq_refl) | apply (MDL R_X30 64 eq_refl)]. }
  eapply satisfies_all_pmono with (p1:=wcspbrk_prog).
    exact P.
    intros a s1 t1 EXIT NOCODE. unfold binvs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 PRE0 B START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcspbrk_prog_welltyped. intro MDL1.
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
Theorem wcspbrk_partial_correctness:
  ∀ prog st sp mem raddr s c x19 x20 x21 x29 Ls Lc t xs'
    (PD: wcspbrk_armv8.wcspbrk_armv8 ⊆2 prog)
    (PA: wcscspn_armv8.wcscspn_armv8 ⊆2 prog) (PB: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (PC: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fdf0, st))
    (MDL: models arm8typctx st)
    (SP: st R_SP = sp) (MEM: st V_MEM64 = mem) (X30: st R_X30 = raddr)
    (X0: st R_X0 = s) (X1: st R_X1 = c)
    (X19: st R_X19 = x19) (X20: st R_X20 = x20) (X21: st R_X21 = x21) (X29: st R_X29 = x29)
    (PRE0: wcspbrk_pre sp mem s c Ls Lc),
  satisfies_all prog (binvs1 sp mem raddr s c x19 x20 x21 x29 Ls Lc)
                     (bexits1 sp mem raddr s c x19 x20 x21 x29 Ls Lc) (xs'::t).
Proof.
  intros.
  assert (B: x19 < 2^64 /\ x20 < 2^64 /\ x21 < 2^64 /\ x29 < 2^64 /\ raddr < 2^64 /\ s < 2^64 /\ c < 2^64).
  { subst. splits; first [apply (MDL R_X19 64 eq_refl) | apply (MDL R_X20 64 eq_refl) | apply (MDL R_X21 64 eq_refl)
                         | apply (MDL R_X29 64 eq_refl) | apply (MDL R_X30 64 eq_refl) | apply (MDL R_X0 64 eq_refl)
                         | apply (MDL R_X1 64 eq_refl)]. }
  eapply satisfies_all_pmono with (p1:=wcspbrk_prog).
    apply wcspbrk_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold binvs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 PRE0 B START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcspbrk_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 B. rename t1 into t.
  destruct B as (B19 & B20 & B21 & B29 & B30 & BSs & BCs).
  destruct PRE0 as (NFs & Zs & LsB & NFc & Zc & CP & SPos & SP80 & SPlt & BS & BCc).
  change (2^64) with 18446744073709551616 in *.
  change (2^61) with 2305843009213693952 in LsB.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  set (F := pbrk_frame sp mem raddr x19 x29).
  assert (FD: ∀ a, a + 4 <= sp - 32 -> F Ⓓ[a] = mem Ⓓ[a]).
  { intros a A. unfold F, pbrk_frame. memsimp. reflexivity. }
  destruct_inv 64 PRE.
  destruct PRE as (R0 & R1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
  do 5 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply wcspbrk_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply wcscspn_in_wcspbrk with (sp := sp - 32) (mem := F) (raddr := 0x15fe04) (s := s) (c := c)
     (x19 := s) (x20 := x20) (x21 := x21) (x29 := sp - 32) (Ls := Ls) (Lc := Lc).
  1: intros ? ? ? H; exact H.
  1: exact ENTRY.
  1: exact MDL2.
  all: try (unfold s2; simpl_stores; first [reflexivity | assumption | apply MS; lia | idtac]).
  1: unfold F, pbrk_frame; rewrite !MS by lia; reflexivity.
  1: { unfold wcscspn_pre. splits; try lia.
       eapply nilfree_ext. exact FD. lia. exact NFs.
       rewrite FD by lia. exact Zs.
       eapply nilfree_ext. exact FD. lia. exact NFc.
       rewrite FD by lia. exact Zc. }
  intros a' s' t2 ENTRY2 XP UT PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply wcspbrk_prog_welltyped.
  destruct_inv 64 PRE.
  all: destruct PRE as (k & KL & CS & HK & R0' & MEMD & SP' & X19' & X20' & X21' & X29' & X30').
  all: set (G := cspn_frame (sp - 32) F 0x15fe04 s x20 x21 (sp - 32)) in MEMD.
  all: assert (MR: ∀ a, a + 4 <= sp - 80 -> s' V_MEM64 Ⓓ[a] = mem Ⓓ[a])
         by (intros a A; destruct MEMD as [-> | ->]; [apply FD; lia | unfold G, cspn_frame; memsimp; apply FD; lia]).
  all: assert (MQ16: s' V_MEM64 Ⓠ[sp - 16] = x19)
         by (destruct MEMD as [-> | ->]; [|unfold G, cspn_frame; memsimp]; unfold F, pbrk_frame; memsimp; apply N.mod_small; L64).
  all: assert (MQ32: s' V_MEM64 Ⓠ[sp - 32] = x29)
         by (destruct MEMD as [-> | ->]; [|unfold G, cspn_frame; memsimp]; unfold F, pbrk_frame; memsimp; apply N.mod_small; L64).
  all: assert (MQ24: s' V_MEM64 Ⓠ[sp - 24] = raddr)
         by (destruct MEMD as [-> | ->]; [|unfold G, cspn_frame; memsimp]; unfold F, pbrk_frame; memsimp; apply N.mod_small; L64).
  all: repeat arm8_step.
  all: assert (SH: k << 2 = 4*k) by (rewrite N.shiftl_mul_pow2; change (2^2) with 4; lia).
  all: rewrite ?SH in *.
  all: rewrite MR in BC by lia.
  all: assert (FK: F Ⓓ[s + 4*k] = mem Ⓓ[s + 4*k]) by (apply FD; lia).
  all: rewrite FK in HK.
  all: exists k; splits; try assumption; try lia.
  all: first
  [ eapply cspn_ext; [exact FD | lia | lia | exact CS]
  | apply N.eqb_eq in BC; left; split; [exact BC | reflexivity]
  | apply N.eqb_neq in BC; right; splits;
    [ exact BC
    | destruct HK as [HK|HK]; [contradiction | eapply winset_ext; [exact FD | lia | exact HK]]
    | rewrite N.mod_small by L64; reflexivity ]
  | destruct MEMD as [H|H]; rewrite H; [left|right]; reflexivity
  | replace (16 + (sp - 32)) with (sp - 16) by lia; exact MQ16
  | replace (8 + (sp - 32)) with (sp - 24) by lia; exact MQ24 ].
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X19-X21/X29/X30 are
   never written by wcspbrk, wcscspn, wcschr or wcslen. *)
Theorem wcspbrk_preserves_other_callee_saved:
  ∀ r, In r (R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcspbrk_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
