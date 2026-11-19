(* strcspn -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls memset, strchrnul)

   SEMANTICS
   ---------
   musl's src/string/strcspn.c (casts dropped and pointer dereferences
   written with [0] so this comment stays well formed):
       #define BITOP(a,b,op) \
        ((a)[(size_t)(b)/(8*sizeof *(a))] op (size_t)1<<((size_t)(b)%(8*sizeof *(a))))
       size_t strcspn(const char *s, const char *c) {
           const char *a = s;
           size_t byteset[32/sizeof(size_t)];
           if (!c[0] || !c[1]) return __strchrnul(s, c[0])-a;
           memset(byteset, 0, sizeof byteset);
           for (; c[0] && BITOP(byteset, c[0], |=); c++);
           for (; s[0] && !BITOP(byteset, s[0], &); s++);
           return s-a;
       }
   compiled with an 80-byte frame (stp x29,x30,[sp,#-0x50]! / str x19,[sp,#16]),
   the 32-byte table at sp0-32, x5/x3 spilled to sp0-48/sp0-40 around
   bl memset (0x118400, n = 32, stepped through symbolically inside cs_prog),
   a table-building loop (0x15ed4c: ubfx word index, lsl bit, ldr/orr/str)
   and a scan loop (0x15ed78: ldr word, lsr, tbz).  The short-set path
   (c[0] = 0 or c[1] = 0, bl __strchrnul 0x15ebf4) is NOT covered: the
   precondition requires strlen(c) >= 2.

   SPECIFICATION (man 3 strcspn, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            size_t strcspn(const char *s, const char *reject);
     DESCRIPTION
            The strcspn() function calculates the length of the initial
            segment of s which consists entirely of bytes not in reject.
     RETURN VALUE
            The strcspn() function returns the number of bytes in the
            initial segment of s which are not in the string reject.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strcspn at 0x5ecf0 (ELF vaddr); 0x15ecf0 in Ghidra (image base 0x100000);
            callee memset at 0x18400 / 0x118400 (strchrnul 0x5ebf4 / 0x15ebf4
            is on the excluded path)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strcspn_armv8.v and
            ../lifted/memset_armv8.v (combined as cs_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = reject (c), SP = sp, X30 = raddr, X19 = x19,
            X29 = x29; memory mem.
   PRECONDITION (cs_pre sp mem p c Ks Lc), stated explicitly:
            - Ks = strlen(p): bytes p..p+Ks-1 nonzero, byte p+Ks = 0;
            - Lc = strlen(c): bytes c..c+Lc-1 nonzero, byte c+Lc = 0;
            - 2 <= Lc (restriction: excludes the strchrnul path);
            - 4176 <= sp < 2^64 (the memset target sp-32 is >= 4096, memset's
              precondition); p+Ks+81 <= sp and c+Lc+81 <= sp (both strings,
              including their NULs, lie below strcspn's 80-byte frame).
   Output:  If execution reaches the RET (0x15ed28), with M the final memory:
            X0 = K for some K <= Ks such that no byte p[i], i < K, occurs in
            c[0..Lc), and either K = Ks (stopped at the NUL) or p[K] occurs in
            c[0..Lc) (cs_in) -- i.e. K = strcspn(p, c);
            SP = sp, X19 = x19, X29 = x29, X30 = raddr;
            M[a] = mem[a] for every address a outside the frame sp-80..sp-1
            (cs_post).  X20..X28 and Z8..Z15 are never written
            (strcspn_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import strcspn_defs.
Import ARM8Notations.
Open Scope N.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Ltac nrm := repeat match goal with
  | H: negb ((?b >> 0) mod 2^32 =? 0) = true |- _ => apply cbnz32_true in H; [|apply byte_lt32]
  | H: negb ((?b >> 0) mod 2^32 =? 0) = false |- _ => apply cbnz32_false in H; [|apply byte_lt32]
  | H: negb (_ =? _) = true |- _ => apply Bool.negb_true_iff, N.eqb_neq in H
  | H: negb (_ =? _) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Lemma zero_q: ∀ M a, a + 8 <= 2^64 -> (∀ i, i < 8 -> M Ⓑ[a+i] = 0) -> M Ⓠ[a] = 0.
Proof.
  intros M a A H. transitivity ((M [Ⓠ a := 0]) Ⓠ[a]).
  - apply getmem_ext. intros i I. rewrite H by lia. rewrite read_in by L64.
    unfold byte. rewrite N.shiftr_0_l. reflexivity.
  - rewrite getmem_setmem by L64. reflexivity.
Qed.

Lemma div64: ∀ w k, k < 64 -> (64 * w + k) / 64 = w /\ (64 * w + k) mod 64 = k.
Proof. intros w k K. split; symmetry; [apply N.div_unique with k | apply N.mod_unique with w]; lia. Qed.

Lemma pow_lt64: ∀ b, 2 ^ (b mod 64) < 2^64.
Proof. intro b. apply N.pow_lt_mono_r. lia. apply N.mod_lt. discriminate. Qed.

Lemma bset_lt: ∀ mem c j w, bset mem c j w < 2^64.
Proof.
  intros mem c j w. induction j as [|j IH]; cbn [bset].
  - L64.
  - destruct (_ =? w); [apply lor_bound; [exact IH | apply pow_lt64] | exact IH].
Qed.

Lemma bset_bit: ∀ mem c j w k, k < 64 ->
  (N.testbit (bset mem c j w) k = true <-> ∃ i, i < N.of_nat j /\ mem Ⓑ[c + i] = 64 * w + k).
Proof.
  intros mem c j w k K. induction j as [|j IH]; cbn [bset].
  - rewrite N.bits_0. split; [discriminate | intros (i & I & _); lia].
  - rewrite Nat2N.inj_succ. set (b := mem Ⓑ[c + N.of_nat j]).
    pose proof (N.div_mod b 64 ltac:(discriminate)) as DM.
    pose proof (N.mod_lt b 64 ltac:(discriminate)) as ML.
    destruct (N.eqb_spec (b / 64) w) as [E|E].
    + rewrite N.lor_spec, N.pow2_bits_eqb, Bool.orb_true_iff, IH, N.eqb_eq. split.
      * intros [(i & I & EI)|EK]. exists i. split; [lia | exact EI].
        exists (N.of_nat j). split; [lia|]. fold b. rewrite DM at 1. rewrite E, EK. reflexivity.
      * intros (i & I & EI). destruct (N.lt_ge_cases i (N.of_nat j)) as [LT|GE].
        left. exists i. split; [exact LT | exact EI].
        right. assert (i = N.of_nat j) by lia. subst i. fold b in EI.
        rewrite EI. apply div64. exact K.
    + rewrite IH. split.
      * intros (i & I & EI). exists i. split; [lia | exact EI].
      * intros (i & I & EI). destruct (N.lt_ge_cases i (N.of_nat j)) as [LT|GE].
        exists i. split; [exact LT | exact EI].
        exfalso. assert (i = N.of_nat j) by lia. subst i. fold b in EI. apply E.
        rewrite EI. apply div64. exact K.
Qed.

Lemma b_idx: ∀ b, b >> 6 << 3 = 8 * (b / 64).
Proof. intro b. rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^6) with 64. change (2^3) with 8. lia. Qed.

Lemma b_div_lt: ∀ (m:memory) a, m Ⓑ[a] / 64 < 4.
Proof.
  intros m a. assert (B: m Ⓑ[a] < 2^8) by (apply getmem_lt; discriminate).
  apply N.div_lt_upper_bound. discriminate. change (2^8) with 256 in B. lia.
Qed.

Lemma cm_out: ∀ sp mem raddr x19 x29 c j M a,
  cs_mem sp mem raddr x19 x29 c j M -> 4096 + 80 <= sp -> sp < 2^64 ->
  a < 2^64 -> (a < sp - 80 \/ sp <= a) -> M Ⓑ[a] = mem Ⓑ[a].
Proof.
  intros sp mem raddr x19 x29 c j M a [F _] S1 S2 A O.
  rewrite F by (change (2^64) with 18446744073709551616 in *; lia).
  unfold cs_frame. rewrite !(msub_small 64 sp) by L64.
  repeat rd1; first [reflexivity | exfalso; L64].
Qed.

Lemma cm_q: ∀ sp mem raddr x19 x29 c j M,
  cs_mem sp mem raddr x19 x29 c j M -> 4096 + 80 <= sp -> sp < 2^64 ->
  x19 < 2^64 -> x29 < 2^64 -> raddr < 2^64 ->
  M Ⓠ[sp ⊖ 64] = x19 /\ M Ⓠ[sp ⊖ 80] = x29 /\ M Ⓠ[sp ⊖ 72] = raddr.
Proof.
  intros sp mem raddr x19 x29 c j M [F _] S1 S2 W19 W29 W30.
  assert (FQ: ∀ a v, sp - 80 <= a -> a + 8 <= sp - 32 -> cs_frame sp mem raddr x19 x29 c Ⓠ[a] = v -> M Ⓠ[a] = v).
  { intros a v A1 A2 E. rewrite <- E. apply getmem_ext. intros i I. apply F; L64. }
  rewrite !(msub_small 64 sp) by L64.
  splits; apply FQ; try L64; unfold cs_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; assumption.
Qed.

Lemma cm_test: ∀ sp mem raddr x19 x29 c L M (b:N),
  cs_mem sp mem raddr x19 x29 c L M -> b / 64 < 4 ->
  (((M Ⓠ[sp - 32 + (b >> 6 << 3)] >> b mod 64) mod 2 =? 0) = true -> ~ cs_in mem c L b) /\
  (((M Ⓠ[sp - 32 + (b >> 6 << 3)] >> b mod 64) mod 2 =? 0) = false -> cs_in mem c L b).
Proof.
  intros sp mem raddr x19 x29 c L M b [_ B] BL.
  rewrite b_idx, B by exact BL. rewrite N.shiftr_div_pow2, <- N.testbit_spec'.
  pose proof (N.div_mod b 64 ltac:(discriminate)) as DM.
  pose proof (N.mod_lt b 64 ltac:(discriminate)) as ML.
  pose proof (bset_bit mem c (N.to_nat L) (b / 64) (b mod 64) ML) as BB.
  rewrite N2Nat.id, <- DM in BB. unfold cs_in. split; intro H.
  - intro IN. apply BB in IN. rewrite IN in H. simpl in H. discriminate.
  - apply BB. destruct N.testbit; [reflexivity | discriminate].
Qed.

Lemma cm_step: ∀ sp mem raddr x19 x29 c j M (b:N),
  cs_mem sp mem raddr x19 x29 c j M -> 4096 + 80 <= sp -> sp < 2^64 ->
  mem Ⓑ[c + j] = b -> b / 64 < 4 ->
  cs_mem sp mem raddr x19 x29 c (j + 1)
    (M [Ⓠ sp - 32 + (b >> 6 << 3) := 1 << b mod 64 .| M Ⓠ[sp - 32 + (b >> 6 << 3)] ]).
Proof.
  intros sp mem raddr x19 x29 c j M b [F B] S1 S2 EB BL.
  rewrite b_idx. split.
  - intros a A O. rewrite read_out by L64. apply F; assumption.
  - intros w W. rewrite N.add_1_r, N2Nat.inj_succ. cbn [bset]. rewrite N2Nat.id, EB.
    destruct (N.eqb_spec (b / 64) w) as [E|E].
    + subst w. rewrite getmem_setmem by L64. rewrite B by exact W.
      rewrite N.shiftl_1_l, N.lor_comm. apply N.mod_small. apply lor_bound; [apply bset_lt | apply pow_lt64].
    + rewrite <- B by exact W. destruct (N.lt_ge_cases w (b / 64)).
      * apply getmem_setmem_above; L64.
      * apply getmem_setmem_below; L64.
Qed.

Lemma cs_case_15ecf0: ∀ sp mem raddr p c x19 x29 Ks Lc (s1:store) (t:list (exit*store)),
  cs_pre sp mem p c Ks Lc ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr p c x19 x29 Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15ecf0 ->
  nextinv cs_prog (invs1 sp mem raddr p c x19 x29 Ks Lc) (exits1 sp mem raddr p c x19 x29 Ks Lc) false ((Addr 0x15ecf0, s1) :: t).
Proof.
  intros sp mem raddr p c x19 x29 Ks Lc s1 t PRE0 W19 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X29).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & L2 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: try (match goal with |- False => idtac end; nrm;
         match goal with H: getmem _ _ _ _ _ = 0 |- _ =>
           rewrite !(msub_small 64 sp) in H by L64;
           repeat first [rewrite getmem_setmem_below in H by L64 | rewrite getmem_setmem_above in H by L64];
           first [ (apply (NFc 0); [lia | rewrite N.add_0_r; exact H]) | (apply (NFc 1); [lia | rewrite N.add_comm; exact H]) ] end).
  exists 0. splits; try reflexivity; try lia.
  all: try (rewrite N.add_0_r; reflexivity).
  all: try (symmetry; apply msub_small; L64).
  all: try (apply msub_small; L64).
  change (mem [Ⓠ sp ⊖ 80 := x29] [Ⓠ sp ⊖ 72 := raddr] [Ⓠ sp ⊖ 64 := x19] [Ⓠ sp ⊖ 48 := sp ⊖ 32] [Ⓠ sp ⊖ 40 := c])
      with (cs_frame sp mem raddr x19 x29 c).
    rewrite !(msub_small 64 sp) by L64. split.
    - intros a A O. repeat rd1; first [reflexivity | exfalso; L64].
    - intros w W. change (bset _ _ (N.to_nat 0) _) with 0. apply zero_q; [L64|]. intros i I.
      repeat rd1; first [unfold byte; rewrite N.shiftr_0_l; reflexivity | exfalso; L64].
Qed.

Lemma cs_case_15ed4c: ∀ sp mem raddr p c x19 x29 Ks Lc (s1:store) (t:list (exit*store)),
  cs_pre sp mem p c Ks Lc ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr p c x19 x29 Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15ed4c ->
  nextinv cs_prog (invs1 sp mem raddr p c x19 x29 Ks Lc) (exits1 sp mem raddr p c x19 x29 Ks Lc) false ((Addr 0x15ed4c, s1) :: t).
Proof.
  intros sp mem raddr p c x19 x29 Ks Lc s1 t PRE0 W19 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (j & JL & X0 & X3 & X5 & X19 & SP & CM).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & L2 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: nrm.
  all: assert (CJ: c + j + 81 <= sp) by lia.
  all: rewrite (cm_out sp mem raddr x19 x29 c j (s1 V_MEM64) (c + j)) in * by first [exact CM | L64 | (left; L64)].
  - assert (j = Lc) by (destruct (N.lt_ge_cases j Lc) as [LT|GE]; [exfalso; apply (NFc j LT); assumption | lia]). subst j.
    exists 0. splits; first [lia | (rewrite N.add_0_r; reflexivity) | sassumption | reflexivity | exact CM | (intros; lia)].
  - assert (JL2: j < Lc) by (destruct (N.lt_ge_cases j Lc) as [LT|GE]; [exact LT | exfalso; assert (j = Lc) by lia; subst j; contradiction]).
    exists (j + 1). splits; first [lia | reflexivity | sassumption |
      (match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; lia end) |
      (apply cm_step; [exact CM | L64 | L64 | reflexivity | apply b_div_lt]) ].
Qed.

Lemma cs_case_15ed78: ∀ sp mem raddr p c x19 x29 Ks Lc (s1:store) (t:list (exit*store)),
  cs_pre sp mem p c Ks Lc ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr p c x19 x29 Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15ed78 ->
  nextinv cs_prog (invs1 sp mem raddr p c x19 x29 Ks Lc) (exits1 sp mem raddr p c x19 x29 Ks Lc) false ((Addr 0x15ed78, s1) :: t).
Proof.
  intros sp mem raddr p c x19 x29 Ks Lc s1 t PRE0 W19 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & KK & X3 & X5 & X19 & SP & NI & CM).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & L2 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: nrm.
  all: assert (CJ: p + k + 81 <= sp) by lia.
  all: rewrite (cm_out sp mem raddr x19 x29 c Lc (s1 V_MEM64) (p + k)) in * by first [exact CM | L64 | (left; L64)].
  all: pose proof (cm_test sp mem raddr x19 x29 c Lc (s1 V_MEM64) (mem Ⓑ[p + k]) CM (b_div_lt _ _)) as [T1 T2].
  all: pose proof (cm_q sp mem raddr x19 x29 c Lc (s1 V_MEM64) CM SPlo SPhi W19 W29 W30) as (Q1 & Q2 & Q3).
  all: try (assert (KK2: k < Ks) by (destruct (N.lt_ge_cases k Ks) as [LT|GE]; [exact LT | exfalso; assert (k = Ks) by lia; subst k; contradiction])).
  all: try (assert (k = Ks) by (destruct (N.lt_ge_cases k Ks) as [LT|GE]; [exfalso; apply (NFp k LT); assumption | lia]); subst k).
  all: try match goal with H: _ = 0 |- _ => specialize (T1 (proj2 (N.eqb_eq _ _) H)) end.
  all: try match goal with H: _ <> 0 |- _ => specialize (T2 (proj2 (N.eqb_neq _ _) H)) end.
  all: splits.
  all: try (eexists; splits; [| match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; reflexivity end | | ]).
  all: try (exists (k + 1); splits).
  all: try first [ lia | reflexivity | sassumption | exact NI | (left; reflexivity) | (right; exact T2) |
      (match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; lia end) |
      (intros a A O; apply (cm_out sp mem raddr x19 x29 c Lc (s1 V_MEM64) a CM SPlo SPhi A); L64) |
      (intros i I; destruct (N.lt_ge_cases i k); [apply NI; lia | replace i with k by lia; exact T1]) ].
Qed.

Theorem strcspn_partial_correctness:
  ∀ prog s sp mem raddr p c x19 x29 Ks Lc t xs'
    (PRE0: cs_pre sp mem p c Ks Lc)
    (P1: strcspn_armv8.strcspn_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ecf0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p c x19 x29 Ks Lc) (exits1 sp mem raddr p c x19 x29 Ks Lc) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  assert (PP: cs_prog ⊆2 prog) by (apply cs_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=cs_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X29 START PRE0 W19 W29 W30 W0 W1.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cs_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0 W1. rename t1 into t.
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W29, W30, W0, W1. clear WW.
  destruct_inv 64 PRE.
  - eapply cs_case_15ecf0; eassumption.
  - eapply cs_case_15ed4c; eassumption.
  - eapply cs_case_15ed78; eassumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorem: strcspn and memset never write X20..X28 or Z8..Z15.     *)
Theorem strcspn_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates cs_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
