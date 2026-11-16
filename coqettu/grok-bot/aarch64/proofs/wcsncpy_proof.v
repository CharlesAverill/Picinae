(* wcsncpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wmemset)

   SEMANTICS
   ---------
   musl's src/string/wcsncpy.c:
       wchar_t *wcsncpy(wchar_t *restrict d, const wchar_t *restrict s, size_t n) {
           wchar_t *a = d;
           while (n && *s) n--, *d++ = *s++;
           wmemset(d, 0, n);
           return a;
       }
   compiled as a 32-byte frame (stp x29,x30,[sp,#-32]! / str x19), an inline
   4-byte copy loop (0x15fd84..0x15fd98; X2 counts n down, str w3,[x0],#4),
   mov w1,#0 and bl wmemset (0x160294, re-proved here inside wcsncpy_prog),
   then the frame restore.  wchar_t is 4 bytes.

   SPECIFICATION (man 3 wcsncpy, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcsncpy(wchar_t dest[restrict .n],
                             const wchar_t src[restrict .n], size_t n);
     DESCRIPTION
            The wcsncpy() function is the wide-character equivalent of the
            strncpy(3) function.  It copies at most n wide characters from the
            wide-character string pointed to by src, including the terminating
            null wide character (L'\0'), to the array pointed to by dest.
            Exactly n wide characters are written at dest.  If the length
            wcslen(src) is smaller than n, the remaining wide characters in the
            array pointed to by dest are filled with null wide characters.  If
            the length wcslen(src) is greater than or equal to n, the string
            pointed to by dest will not be terminated by a null wide character.
            The strings may not overlap.
            The programmer must ensure that there is room for at least n wide
            characters at dest.
     RETURN VALUE
            wcsncpy() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcsncpy at 0x5fd70 (ELF vaddr); 0x15fd70 in Ghidra (image base 0x100000);
            callee wmemset at 0x60294 / 0x160294
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcsncpy_armv8.v and
            ../lifted/wmemset_armv8.v (combined as wcsncpy_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest (d), X1 = src (q), X2 = n, SP = sp, X30 = raddr,
            X19/X29 = x19/x29; memory mem.
   PRECONDITION (wcsncpy_pre sp mem d q n K), stated explicitly
   (all element reads/writes are 4-byte little-endian words):
            - words at q+4i (i < K) are nonzero, K <= n < 2^64, and either
              K = n or the word at q+4K is 0 (so K = min(n, wcslen(q)), the
              number of wide characters copied);
            - 32 <= sp < 2^64, the destination array d..d+4n-1 and the source
              bytes q..q+4K+3 lie below sp-32, i.e. below wcsncpy's own stack
              frame (sp-32..sp);
            - the copied destination range d..d+4K-1 and the read range
              q..q+4K+3 do not overlap (q+4K+4 <= d or d+4K <= q).
            Justification: the C standard makes copying between overlapping
            objects undefined behaviour (restrict; the man page says the
            strings may not overlap), and a destination that overlaps
            wcsncpy's own stack frame is not caller-owned memory, so the
            precondition only excludes undefined behaviour.  It is needed
            because wcsncpy reloads X30, X29 and X19 from its frame after the
            copy and the wmemset fill.
   Output:  If execution reaches the RET (0x15fdb0), with
            C = mem with x29, raddr, x19 stored at sp-32, sp-24, sp-16
            (the saved frame):
            memory = wset (wcpy C d q K) (d+4K) 0 (n-K), i.e. words q[0..K-1]
            copied in order to d.., then n-K zero words at d+4K..d+4n-1
            (wcpy in wcscpy_proof.v, wset in wmemset_proof.v), X0 = d,
            SP = sp, X19 = x19, X29 = x29, X30 = raddr.
            Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsncpy_armv8 wmemset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcslen_proof wcscpy_proof wmemset_proof.
From Grok.proofs Require wcsncat_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsncpy_prog : program := updateall2 wcsncpy_armv8.wcsncpy_armv8 wmemset_armv8.wmemset_armv8.

Theorem wcsncpy_prog_welltyped: welltyped_prog arm8typctx wcsncpy_prog.
Proof.
  intros s a. unfold wcsncpy_prog, updateall2, updateall.
  destruct (wmemset_armv8.wmemset_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wmemset_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcsncpy_armv8.welltyped.
Qed.

Lemma wcsncpy_prog_mono: ∀ prog, wcsncpy_armv8.wcsncpy_armv8 ⊆2 prog -> wmemset_armv8.wmemset_armv8 ⊆2 prog -> wcsncpy_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold wcsncpy_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* reads above the words written by wset are unaffected *)
Lemma wset_read_above: ∀ m e v k len a, e + 4 * N.of_nat k <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (wset m e v k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H0 H2. reflexivity.
  cbn [wset]. rewrite N.shiftl_mul_pow2. change (2^2) with 4.
  change (2^64) with 18446744073709551616 in *.
  rewrite getmem_setmem_below by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Definition ncpy_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp - 32 := x29] [Ⓠ sp - 24 := raddr] [Ⓠ sp - 16 := x19].

Definition wcsncpy_pre (sp mem d q n K : N) :=
  K <= n /\ n < 2^64 /\ wcs_nilfree mem q K /\ (K = n \/ mem Ⓓ[q + 4*K] = 0) /\
  32 <= sp /\ sp < 2^64 /\ d + 4*n <= sp - 32 /\ q + 4*K + 4 <= sp - 32 /\
  (q + 4*K + 4 <= d \/ d + 4*K <= q).

Definition wcsncpy_post (sp mem raddr d q n x19 x29 K : N) (s:store) :=
  s V_MEM64 = wset (wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat K)) (d + 4*K) 0 (N.to_nat (n - K)) /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x29 K : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsncpy *)
    | 0x15fd70 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x15fd8c => Inv 1 (∃ k, k <= K /\ s R_X0 = d + 4*k /\ s R_X1 = q + 4*k /\ s R_X2 = n - k /\ s R_X19 = d /\
                         s V_MEM64 = wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat k) /\
                         s R_SP = sp - 32 /\ s R_X29 = sp - 32)
    | 0x15fd9c => Inv 1 (s R_X0 = d + 4*K /\ s R_X2 = n - K /\ s R_X19 = d /\
                         s V_MEM64 = wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat K) /\
                         s R_SP = sp - 32 /\ s R_X29 = sp - 32)
    | 0x15fdb0 => Post 1 (wcsncpy_post sp mem raddr d q n x19 x29 K s)
    (* wmemset callee: X0 = d, X1 = q (fill value), X2 = n (count) *)
    | 0x160294 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x1602a4 => Inv 0 (∃ k, k <= n /\ s R_X3 = k /\ s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = wset mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x1602ac => Post 0 (s R_X0 = d /\ s V_MEM64 = wset mem d q (N.to_nat n) /\ s R_SP = sp /\ s R_X30 = raddr /\
                          s R_X19 = x19 /\ s R_X29 = x29)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsncpy_prog invs.
  Definition invs0 := make_invs 0 wcsncpy_prog invs.
  Definition exits1 := make_exits 1 wcsncpy_prog invs.
  Definition invs1 := make_invs 1 wcsncpy_prog invs.
End Invariants.

Theorem wmemset_correct_in_wcsncpy:
  ∀ prog s t xs'
    (P: wcsncpy_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x160294, s))
    (MDL: models arm8typctx s),
  ∀ K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X29) K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X29) K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (c := s R_X1). set (n := s R_X2). set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X1: s R_X1 = c) by reflexivity. assert (X2: s R_X2 = n) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p c n x29 x19.
  eapply satisfies_all_pmono with (p1:=wcsncpy_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
    repeat arm8_step.
    exists 0. repeat split; try assumption; try lia.
  - destruct PRE as (k & KLE & X3 & X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    all: destruct (n =? k) eqn:E; try discriminate.
    + apply N.eqb_eq in E. rewrite <- E in MEM. repeat split; assumption.
    + apply N.eqb_neq in E. exists (k+1). repeat split; try assumption; try lia.
      all: first
        [ rewrite N.add_comm; apply N.mod_small; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wset];
          rewrite N2Nat.id, (N.add_comm p); reflexivity ].
Qed.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Theorem wcsncpy_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x29 K t xs'
    (PRE0: wcsncpy_pre sp mem d q n K)
    (P1: wcsncpy_armv8.wcsncpy_armv8 ⊆2 prog) (P0: wmemset_armv8.wmemset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fd70, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr d q n x19 x29 K) (exits1 sp mem raddr d q n x19 x29 K) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  assert (PP: wcsncpy_prog ⊆2 prog) by (apply wcsncpy_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=wcsncpy_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X29 START PRE0 W19 W29 W30 W0 W1.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0 W1. rename t1 into t.
  destruct PRE0 as (KN & N64 & NFq & ZK & SP32 & SPlt & BD & BQ & DISJ).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W29, W30, W0, W1. clear WW.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  set (C := ncpy_frame sp mem raddr x19 x29).
  assert (CB: ∀ a, a + 4 <= sp - 32 -> C Ⓓ[a] = mem Ⓓ[a]).
  { intros a A. unfold C, ncpy_frame. memsimp. reflexivity. }
  assert (RD: ∀ i, i <= K -> wcpy C d q (N.to_nat i) Ⓓ[q+4*i] = mem Ⓓ[q+4*i]).
  { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
    - apply wcsncat_proof.wcpy_read_below; rewrite ?N2Nat.id; L64.
    - apply wcsncat_proof.wcpy_read_above; rewrite ?N2Nat.id; L64. }
  assert (FR: ∀ a, sp - 32 <= a -> a + 8 <= sp ->
     (wset (wcpy C d q (N.to_nat K)) (d+4*K) 0 (N.to_nat (n-K))) Ⓠ[a] = C Ⓠ[a]).
  { intros a A1 A2. rewrite wset_read_above by (rewrite ?N2Nat.id; L64).
    apply wcsncat_proof.wcpy_read_above; rewrite ?N2Nat.id; L64. }
  assert (Q32: C Ⓠ[sp - 32] = x29) by (unfold C, ncpy_frame; memsimp; apply N.mod_small; L64).
  assert (Q24: C Ⓠ[sp - 24] = raddr) by (unfold C, ncpy_frame; memsimp; apply N.mod_small; L64).
  assert (Q16: C Ⓠ[sp - 16] = x19) by (unfold C, ncpy_frame; memsimp; apply N.mod_small; L64).
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
    repeat arm8_step.
    exists 0. rewrite !(MS sp) by lia. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r.
    splits; try assumption; try reflexivity; try lia.
  - destruct PRE as (k & KK & X0 & X1 & X2 & X19 & MEM & SP & X29).
    repeat grok_step.
    + (* n exhausted: k = n = K *)
      apply N.eqb_eq in BC. assert (EK: k = K) by lia. clear BC. subst k.
      splits; first [assumption | reflexivity].
    + (* copy one more wide character *)
      apply N.eqb_neq in BC.
      apply cbnz32_true in BC0; [|apply dword_lt32]. rewrite RD in BC0 by lia.
      assert (KLT: k < K).
      { destruct (N.eq_dec k K) as [->|NE]; [|lia]. destruct ZK as [ZK|ZK]; [lia|contradiction]. }
      exists (k+1). rewrite (MS (n-k) 1) by lia. splits; try reflexivity; try lia.
      all: first [ (rewrite N.mod_small by L64; lia)
                 | (replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy]; rewrite ?N2Nat.id; reflexivity) ].
    + (* NUL found: k = K *)
      apply cbnz32_false in BC0; [|apply dword_lt32]. rewrite RD in BC0 by lia.
      assert (k = K).
      { destruct (N.lt_ge_cases k K) as [H|H]; [|lia]. exfalso. exact (NFq k H BC0). }
      subst k. splits; first [assumption | reflexivity].
  - destruct PRE as (X0 & X2 & X19 & MEM & SP & X29).
    do 2 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply wcsncpy_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply wmemset_correct_in_wcsncpy with (K:=K); first [ exact (fun _ _ _ H => H) | eassumption ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply wcsncpy_prog_welltyped.
    clearbody s2.
    clear - PRE MDL' KN N64 NFq ZK SP32 SPlt BD BQ DISJ W19 W29 W30 W0 W1 MS C FR Q32 Q24 Q16 X0 X2 X19 MEM SP X29.
    rename MDL' into MDL. rename s' into s0.
    destruct_inv 64 PRE.
    destruct PRE as (R0 & MEM0 & SP0 & R30 & R19 & R29).
    rewrite X0 in R0. rewrite X0, X2, MEM in MEM0. rewrite SP in SP0. rewrite X19 in R19. rewrite X29 in R29.
    clear X0 X2 X19 MEM SP X29.
    repeat arm8_step.
    try unfold wcsncpy_post. change (ncpy_frame sp mem raddr x19 x29) with C.
    repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
    replace (16 + (sp - 32)) with (sp - 16) by lia.
    replace (8 + (sp - 32)) with (sp - 24) by lia.
    replace (32 + (sp - 32)) with sp by lia.
    rewrite !FR by L64. rewrite Q32, Q24, Q16.
    splits; reflexivity.
Qed.
