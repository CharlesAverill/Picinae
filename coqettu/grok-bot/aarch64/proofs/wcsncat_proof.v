(* wcsncat -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcslen)

   SEMANTICS
   ---------
   musl's src/string/wcsncat.c:
       wchar_t *wcsncat(wchar_t *restrict d, const wchar_t *restrict s, size_t n) {
           wchar_t *a = d;
           d += wcslen(d);
           while (n && *s) n--, *d++ = *s++;
           *d++ = 0;
           return a;
       }
   compiled as a 48-byte frame (stp x29,x30,[sp,#-48]! / str x21 / stp x19,x20),
   bl wcslen (0x15fc18, re-proved here inside wcsncat_prog), add x0,x21,x0,lsl #2,
   an inline 4-byte loop (0x15fd04..0x15fd18; X19 counts n down, X20 walks src,
   str w1,[x0],#4), str wzr,[x0], and the frame restore.  wchar_t is 4 bytes.

   SPECIFICATION (man 3 wcsncat, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcsncat(wchar_t dest[restrict .n],
                             const wchar_t src[restrict .n], size_t n);
     DESCRIPTION
            The wcsncat() function is the wide-character equivalent of the
            strncat(3) function.  It copies at most n wide characters from the
            wide-character string pointed to by src to the end of the
            wide-character string pointed to by dest, and adds a terminating
            null wide character (L'\0').
            The strings may not overlap.
            The programmer must ensure that there is room for at least
            wcslen(dest)+n+1 wide characters at dest.
     RETURN VALUE
            wcsncat() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcsncat at 0x5fcdc (ELF vaddr); 0x15fcdc in Ghidra (image base 0x100000);
            callee wcslen at 0x5fc18 / 0x15fc18
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcsncat_armv8.v and
            ../lifted/wcslen_armv8.v (combined as wcsncat_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest (d), X1 = src (q), X2 = n, SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.
   PRECONDITION (wcsncat_pre sp mem d q n Ld K), stated explicitly
   (all element reads/writes are 4-byte little-endian words):
            - d holds a wide string of length Ld: words at d+4i (i < Ld) are
              nonzero and the word at d+4Ld is 0;
            - words at q+4i (i < K) are nonzero, K <= n < 2^64, and either
              K = n or the word at q+4K is 0 (so K = min(n, wcsnlen(q, n)),
              the number of wide characters copied);
            - 48 <= sp < 2^64 and both byte ranges d..d+4Ld+4K+3 and
              q..q+4K+3 lie below sp-48, i.e. below wcsncat's own stack
              frame (sp-48..sp);
            - the written range d+4Ld..d+4Ld+4K+3 and the read range
              q..q+4K+3 do not overlap (q+4K+4 <= d+4Ld or d+4Ld+4K+4 <= q).
            Justification: the C standard makes copying between overlapping
            objects undefined behaviour (restrict; the man page says the
            strings may not overlap), and a destination that overlaps
            wcsncat's own stack frame is not caller-owned memory, so the
            precondition only excludes undefined behaviour.  It is needed
            because wcsncat reloads X30 and X19-X21 from its frame after the copy.
   Output:  If execution reaches the RET (0x15fd30), with
            C = mem with x29, raddr, x21, x19, x20 stored at sp-48, sp-40,
            sp-16, sp-32, sp-24 (the saved frame):
            memory = (wcpy C (d+4Ld) q K) with the 4-byte word at d+4Ld+4K
            set to 0 (words q[0..K-1] copied in order to d+4Ld.., then the
            terminator; wcpy is defined in wcscpy_proof.v), X0 = d, SP = sp,
            X19 = x19, X20 = x20, X21 = x21, X29 = x29, X30 = raddr.
            Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsncat_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcscpy_proof wcslen_proof.
From Grok.proofs Require wcschr_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsncat_prog : program := updateall2 wcsncat_armv8.wcsncat_armv8 wcslen_armv8.wcslen_armv8.

Theorem wcsncat_prog_welltyped: welltyped_prog arm8typctx wcsncat_prog.
Proof.
  intros s a. unfold wcsncat_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcsncat_armv8.welltyped.
Qed.

Lemma wcsncat_prog_mono: ∀ prog, wcsncat_armv8.wcsncat_armv8 ⊆2 prog -> wcslen_armv8.wcslen_armv8 ⊆2 prog -> wcsncat_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold wcsncat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* reads disjoint from the 4-byte copy writes of wcpy are unaffected *)
Lemma wcpy_read_above: ∀ m e q k len a, e + 4 * N.of_nat k <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (wcpy m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H0 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [wcpy]. rewrite getmem_setmem_below by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Lemma wcpy_read_below: ∀ m e q k len a, a + len <= e -> e + 4 * N.of_nat k <= 2^64 ->
  getmem 64 LittleE len (wcpy m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [wcpy]. rewrite getmem_setmem_above by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Definition ncat_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20].

Definition wcsncat_pre (sp mem d q n Ld K : N) :=
  wcs_nilfree mem d Ld /\ mem Ⓓ[d + 4*Ld] = 0 /\ K <= n /\ n < 2^64 /\ wcs_nilfree mem q K /\
  (K = n \/ mem Ⓓ[q + 4*K] = 0) /\
  48 <= sp /\ sp < 2^64 /\ d + 4*Ld + 4*K + 4 <= sp - 48 /\ q + 4*K + 4 <= sp - 48 /\
  (q + 4*K + 4 <= d + 4*Ld \/ d + 4*Ld + 4*K + 4 <= q).

Definition wcsncat_post (sp mem raddr d q x19 x20 x21 x29 Ld K : N) (s:store) :=
  s V_MEM64 = setmem 64 LittleE 4 (wcpy (ncat_frame sp mem raddr x19 x20 x21 x29) (d + 4*Ld) q (N.to_nat K)) (d + 4*Ld + 4*K) 0 /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x20 x21 x29 Ld K : N).
  Definition XS (s:store) := s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsncat *)
    | 0x15fcdc => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fd08 => Inv 1 (∃ k, k <= K /\ s R_X0 = d + 4*Ld + 4*k /\ s R_X19 = n - k /\ s R_X20 = q + 4*k /\ s R_X21 = d /\
                         s V_MEM64 = wcpy (ncat_frame sp mem raddr x19 x20 x21 x29) (d + 4*Ld) q (N.to_nat k) /\
                         s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15fd30 => Post 1 (wcsncat_post sp mem raddr d q x19 x20 x21 x29 Ld K s)
    (* wcslen callee (string at d) *)
    | 0x15fc18 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = d /\ s R_X1 = d ⊕ 4*k /\
                         wcs_nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc34 => Post 0 (wcslen_proof.wcslen_post sp mem raddr d s /\ XS s)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsncat_prog invs.
  Definition invs0 := make_invs 0 wcsncat_prog invs.
  Definition exits1 := make_exits 1 wcsncat_prog invs.
  Definition invs1 := make_invs 1 wcsncat_prog invs.
End Invariants.

Theorem wcslen_correct_in_wcsncat:
  ∀ prog s t xs'
    (P: wcsncat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s),
  ∀ q n Ld K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (x29 := s R_X29). set (x19 := s R_X19). set (x20 := s R_X20). set (x21 := s R_X21).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  assert (X20: s R_X20 = x20) by reflexivity. assert (X21: s R_X21 = x21) by reflexivity.
  clearbody sp mem raddr p x29 x19 x20 x21.
  eapply satisfies_all_pmono with (p1:=wcsncat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 X20 X21 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
    arm8_step. arm8_step.
    + arm8_step.
      apply cbnz32_true in BC; [|apply dword_lt32].
      destruct (N.lt_ge_cases (k+1) (2^62)) as [LT|GE].
      * exists (k+1). repeat split; try assumption.
        f_equal. lia.
        intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
          replace i with k by lia. exact BC.
      * exists 0. repeat split; try assumption.
        assert (E: 4 + p + 4*k = p + 2^64) by lia. rewrite E, add_wrap_full. f_equal; lia.
        intros i Hi. destruct i; discriminate.
    + arm8_step. arm8_step.
      apply cbnz32_false in BC; [|apply dword_lt32].
      split; [|repeat split; assumption].
      exists k. repeat split; assumption.
Qed.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma first_zero_unique: ∀ (f g: N -> N) L1 L2,
  (∀ i, i < L1 -> f i ≠ 0) -> f L1 = 0 -> (∀ i, i < L2 -> g i ≠ 0) -> g L2 = 0 ->
  (∀ i, i <= L1 -> g i = f i) -> L1 = L2.
Proof.
  intros f g L1 L2 F1 F0 G1 G0 E.
  destruct (N.lt_trichotomy L1 L2) as [H|[H|H]]; [|exact H|].
  - exfalso. apply (G1 L1 H). rewrite E by lia. exact F0.
  - exfalso. apply (F1 L2 H). rewrite <- E by lia. exact G0.
Qed.

Lemma add_mod_inj: ∀ q k K, k < 2^64 -> K < 2^64 -> (q + k) mod 2^64 = (q + K) mod 2^64 -> k = K.
Proof.
  intros q k K Hk HK E.
  pose proof (N.div_mod (q+k) (2^64) ltac:(discriminate)) as A.
  pose proof (N.div_mod (q+K) (2^64) ltac:(discriminate)) as B.
  rewrite E in A. set (r := (q + K) mod 2^64) in *.
  set (a := (q+k)/2^64) in *. set (b := (q+K)/2^64) in *. change (2^64) with 18446744073709551616 in *. nia.
Qed.

Theorem wcsncat_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x20 x21 x29 Ld K t xs'
    (PRE0: wcsncat_pre sp mem d q n Ld K)
    (P1: wcsncat_armv8.wcsncat_armv8 ⊆2 prog) (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fcdc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr d q n x19 x20 x21 x29 Ld K) (exits1 sp mem raddr d q n x19 x20 x21 x29 Ld K) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  assert (PP: wcsncat_prog ⊆2 prog) by (apply wcsncat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=wcsncat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X21 X29 START PRE0 W19 W20 W21 W29 W30.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W29 W30. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    do 8 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply wcsncat_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply wcslen_correct_in_wcsncat with (q:=q) (n:=n) (Ld:=Ld) (K:=K); first [ exact (fun _ _ _ H => H) | eassumption ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply wcsncat_prog_welltyped.
    clearbody s2.
    clear - PRE MDL' PRE0 W19 W20 W21 W29 W30.
    rename MDL' into MDL. rename s' into s0.
    destruct_inv 64 PRE.
    destruct PRE as ((L & LLT & R0 & NF & ZL & MEM & SP & X30) & X29 & X19 & X20 & X21).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 4 <= sp - 48 -> C Ⓓ[a] = mem Ⓓ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> wcpy C (d+4*Ld) q (N.to_nat i) Ⓓ[q+4*i] = mem Ⓓ[q+4*i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply wcpy_read_below; rewrite ?N2Nat.id; L64.
      - apply wcpy_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 4 (wcpy C (d+4*Ld) q (N.to_nat j)) (d+4*Ld+4*j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply wcpy_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    rewrite !(MS sp) in * by lia.
    change (mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20]) with C in *.
    assert (LE: Ld = L).
    { apply (first_zero_unique (fun i => mem Ⓓ[d+4*i]) (fun i => C Ⓓ[d+4*i])); cbv beta; try assumption.
      intros i I. apply CB. change (2^62) with 4611686018427387904 in *. lia. }
    subst L.
    assert (E: (d + (ashiftr 64 (4*Ld) 2 << 2)) mod 18446744073709551616 = d + 4*Ld).
    { change 18446744073709551616 with (2^64).
      rewrite <- (N.Div0.add_mod_idemp_r d ((ashiftr 64 (4*Ld) 2) << 2)), wcschr_proof.ashiftr2_shl2.
      apply N.mod_small. L64. change (2^62) with 4611686018427387904 in *. L64. rewrite N.mul_comm. apply N.Div0.mod_mul. }
    repeat arm8_step.
    exists 0. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r. splits; try assumption; try reflexivity; try lia.
  - destruct PRE as (k & KK & X0 & X19 & X20 & X21 & MEM & SP & X29).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 4 <= sp - 48 -> C Ⓓ[a] = mem Ⓓ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> wcpy C (d+4*Ld) q (N.to_nat i) Ⓓ[q+4*i] = mem Ⓓ[q+4*i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply wcpy_read_below; rewrite ?N2Nat.id; L64.
      - apply wcpy_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 4 (wcpy C (d+4*Ld) q (N.to_nat j)) (d+4*Ld+4*j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply wcpy_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    repeat grok_step.
    + (* k = n *)
      apply N.eqb_eq in BC. assert (EK: k = K) by lia. clear BC. subst k.
      try unfold wcsncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
    + (* copy one more wide character *)
      apply N.eqb_neq in BC.
      apply cbnz32_true in BC0; [|apply dword_lt32]. rewrite RD in BC0 by lia.
      assert (KLT: k < K).
      { destruct (N.eq_dec k K) as [->|NE]; [|lia]. destruct ZK as [ZK|ZK]; [lia|contradiction]. }
      exists (k+1). rewrite (MS (n-k) 1) by lia. splits; try reflexivity; try lia.
      all: first [ (rewrite N.mod_small by L64; lia)
                 | (replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy]; rewrite ?N2Nat.id; reflexivity) ].
    + (* NUL found *)
      apply cbnz32_false in BC0; [|apply dword_lt32]. rewrite RD in BC0 by lia.
      assert (k = K).
      { destruct (N.lt_ge_cases k K) as [H|H]; [|lia]. exfalso. exact (NFq k H BC0). }
      subst k.
      try unfold wcsncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
Qed.
