(* strncasecmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls tolower)

   SEMANTICS
   ---------
   musl's src/string/strncasecmp.c:
       int strncasecmp(const char *_l, const char *_r, size_t n) {
           const unsigned char *l = [cast] _l, *r = [cast] _r;
           if (!n--) return 0;
           for (; *l && *r && n && ( *l == *r || tolower( *l) == tolower( *r)); l++, r++, n--);
           return tolower( *l) - tolower( *r);
       }
   compiled as: cbz x2 (n = 0 returns 0 at 0x15f0ac without a frame), else a
   64-byte frame (x29, x30, x19-x23), a byte loop that keeps X21 = n-1 and
   X22 = l and tests k = n-1 with cmn/ccmp, four bl tolower sites (0x11f2d0,
   the C-locale tolower of tolower_proof.v; its code is part of
   strncasecmp_prog and is executed symbolically at each call),
   sub w0,w19,w0 and the frame restore (RET 0x15f0a4).

   SPECIFICATION (man 3 strncasecmp, Linux man-pages 6.9.1)
   --------------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            int strncasecmp(const char s1[.n], const char s2[.n], size_t n);
     DESCRIPTION
            The strcasecmp() function performs a byte-by-byte comparison of
            the strings s1 and s2, ignoring the case of the characters.
            The strncasecmp() function is similar, except that it compares no
            more than n bytes of s1 and s2.
     RETURN VALUE
            The strcasecmp() and strncasecmp() functions return an integer
            less than, equal to, or greater than zero if s1 is, after ignoring
            case, found to be less than, to match, or be greater than s2,
            respectively.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strncasecmp at 0x5f004 (ELF vaddr); 0x15f004 in Ghidra (image base 0x100000);
            callee tolower at 0x1f2d0 / 0x11f2d0
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strncasecmp_armv8.v and
            ../lifted/tolower_armv8.v (combined as strncasecmp_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 (p), X1 = s2 (q), X2 = n, SP = sp, X30 = raddr,
            X19-X23/X29 = x19-x23/x29; memory mem.
   PRECONDITION (strncasecmp_pre sp mem p q Lp Lq), stated explicitly:
            - p holds a string of length Lp (bytes p..p+Lp-1 nonzero, byte
              p+Lp = 0) and q a string of length Lq (likewise);
            - 64 <= sp < 2^64 and both strings, terminators included, lie
              strictly below sp-64, i.e. below strncasecmp's own stack frame
              (sp-64..sp).
            Justification: as for strcasecmp, the arguments must be valid
            objects and memory at or above sp-64 is the callee's stack, which
            no caller-owned object may occupy under AAPCS64 (no red zone); so
            the precondition only excludes undefined behaviour.  It is needed
            because the frame is stored before the strings are read.  (The
            musl loop reads both bytes at the stop index even when that index
            is n-1, so the strings, not just n bytes, are required.)
   Output:  If execution reaches the RET at 0x15f0ac: n = 0, X0 = 0, memory,
            SP, X19-X23, X29 and X30 unchanged (strncasecmp_post0).
            If execution reaches the RET at 0x15f0a4: there is a k < n with
            - for all i < k: bytes p+i and q+i are nonzero and equal after
              tolower_spec (ceq, from strcasecmp_proof.v);
            - at k: byte p+k = 0, or byte q+k = 0, or k+1 = n, or the
              tolower_spec values differ (nstop);
            - X0 = msub 32 (tolower_spec mem[p+k]) (tolower_spec mem[q+k]);
            and memory = mem with the saved frame (x29, raddr, x19, x20, x21,
            x22, x23 at sp-64, sp-56, ..., sp-16), SP = sp, X19-X23 = x19-x23,
            X29 = x29, X30 = raddr.  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strncasecmp_armv8 tolower_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import tolower_proof.
From Grok.proofs Require Import strcasecmp_proof.
Import ARM8Notations.
Open Scope N.

Definition strncasecmp_prog : program := updateall2 strncasecmp_armv8.strncasecmp_armv8 tolower_armv8.tolower_armv8.

Theorem strncasecmp_prog_welltyped: welltyped_prog arm8typctx strncasecmp_prog.
Proof.
  intros s a. unfold strncasecmp_prog, updateall2, updateall.
  destruct (tolower_armv8.tolower_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (tolower_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strncasecmp_armv8.welltyped.
Qed.

Lemma strncasecmp_prog_mono: ∀ prog, strncasecmp_armv8.strncasecmp_armv8 ⊆2 prog -> tolower_armv8.tolower_armv8 ⊆2 prog -> strncasecmp_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold strncasecmp_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* stop condition at index k for strncasecmp with bound n *)
Definition nstop (m:memory) (p q n k:N) :=
  m Ⓑ[p+k] = 0 \/ m Ⓑ[q+k] = 0 \/ k + 1 = n \/ tolower_spec (m Ⓑ[p+k]) <> tolower_spec (m Ⓑ[q+k]).

Definition ncase_frame (sp mem raddr x19 x20 x21 x22 x23 x29 : N) :=
  mem [Ⓠ sp - 64 := x29] [Ⓠ sp - 56 := raddr] [Ⓠ sp - 48 := x19] [Ⓠ sp - 40 := x20]
      [Ⓠ sp - 32 := x21] [Ⓠ sp - 24 := x22] [Ⓠ sp - 16 := x23].

Definition strncasecmp_pre (sp mem p q Lp Lq : N) :=
  nilfree mem p Lp /\ mem Ⓑ[p + Lp] = 0 /\ nilfree mem q Lq /\ mem Ⓑ[q + Lq] = 0 /\
  64 <= sp /\ sp < 2^64 /\ p + Lp < sp - 64 /\ q + Lq < sp - 64.

Definition strncasecmp_post (sp mem raddr p q n x19 x20 x21 x22 x23 x29 : N) (s:store) :=
  ∃ k, k < n /\ ceq mem p q k /\ nstop mem p q n k /\
  s R_X0 = msub 32 (tolower_spec (mem Ⓑ[p+k])) (tolower_spec (mem Ⓑ[q+k])) /\
  s V_MEM64 = ncase_frame sp mem raddr x19 x20 x21 x22 x23 x29 /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X22 = x22 /\ s R_X23 = x23 /\
  s R_X29 = x29 /\ s R_X30 = raddr.

Definition strncasecmp_post0 (sp mem raddr n x19 x20 x21 x22 x23 x29 : N) (s:store) :=
  n = 0 /\ s R_X0 = 0 /\ s V_MEM64 = mem /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X22 = x22 /\ s R_X23 = x23 /\
  s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr p q n x19 x20 x21 x22 x23 x29 : N).
  Definition D0 := ncase_frame sp mem raddr x19 x20 x21 x22 x23 x29.
  Definition ninvs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f004 => Inv 1 (s R_X0 = p /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X22 = x22 /\ s R_X23 = x23 /\ s R_X29 = x29)
    | 0x15f038 => Inv 1 (∃ k, k < n /\ s R_X19 = p + k /\ s R_X20 = q + k /\ s R_X21 = n - 1 /\ s R_X22 = p /\
                         ceq mem p q k /\ s V_MEM64 = D0 /\ s R_SP = sp - 64 /\ s R_X29 = sp - 64)
    | 0x15f064 => Inv 1 (∃ k, k + 1 < n /\ s R_X19 = p + k /\ s R_X20 = q + k /\ s R_X21 = n - 1 /\ s R_X22 = p /\
                         ceq mem p q k /\ mem Ⓑ[p+k] ≠ 0 /\ mem Ⓑ[q+k] ≠ 0 /\ s R_X0 = tolower_spec (mem Ⓑ[p+k]) /\
                         s V_MEM64 = D0 /\ s R_SP = sp - 64 /\ s R_X29 = sp - 64)
    | 0x15f070 => Inv 1 (∃ k, k + 1 < n /\ s R_X19 = p + k /\ s R_X20 = q + k /\ s R_X21 = n - 1 /\ s R_X22 = p /\
                         ceq mem p q k /\ mem Ⓑ[p+k] ≠ 0 /\ mem Ⓑ[q+k] ≠ 0 /\ s R_X23 = tolower_spec (mem Ⓑ[p+k]) /\
                         s R_X0 = tolower_spec (mem Ⓑ[q+k]) /\
                         s V_MEM64 = D0 /\ s R_SP = sp - 64 /\ s R_X29 = sp - 64)
    | 0x15f084 => Inv 1 (∃ k, k < n /\ s R_X20 = q + k /\ ceq mem p q k /\ nstop mem p q n k /\
                         s R_X0 = tolower_spec (mem Ⓑ[p+k]) /\ s V_MEM64 = D0 /\ s R_SP = sp - 64 /\ s R_X29 = sp - 64)
    | 0x15f090 => Inv 1 (∃ k, k < n /\ ceq mem p q k /\ nstop mem p q n k /\
                         s R_X19 = tolower_spec (mem Ⓑ[p+k]) /\ s R_X0 = tolower_spec (mem Ⓑ[q+k]) /\
                         s V_MEM64 = D0 /\ s R_SP = sp - 64 /\ s R_X29 = sp - 64)
    | 0x15f0a4 => Post 1 (strncasecmp_post sp mem raddr p q n x19 x20 x21 x22 x23 x29 s)
    | 0x15f0ac => Post 1 (strncasecmp_post0 sp mem raddr n x19 x20 x21 x22 x23 x29 s)
    | _ => NoInv
    end.
  Definition nexits1 := make_exits 1 strncasecmp_prog ninvs.
  Definition ninvs1 := make_invs 1 strncasecmp_prog ninvs.
End Invariants.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].
Ltac nprep CB :=
  repeat match goal with H: context [D0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 Ⓑ[?a]] |- _ => rewrite (CB a) in H by L64 end;
  repeat match goal with |- context [D0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 Ⓑ[?a]] => rewrite (CB a) by L64 end;
  repeat match goal with
  | H: (26 <=? msub 32 _ 65) = true |- _ => apply TLF in H; [|apply byte_lt32]
  | H: (26 <=? msub 32 _ 65) = false |- _ => apply TLT in H; [|apply byte_lt32]
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end;
  rewrite ?TL32 in *.
Ltac ncloser :=
  first [ assumption | reflexivity | congruence
        | (left; assumption) | (right; left; assumption) | (right; right; left; lia) | (right; right; right; congruence)
        | (apply ceq_succ; try assumption; congruence)
        | (rewrite N.mod_small by L64; lia) | lia ].

Theorem strncasecmp_partial_correctness:
  ∀ prog s sp mem raddr p q n x19 x20 x21 x22 x23 x29 Lp Lq t xs'
    (PRE0: strncasecmp_pre sp mem p q Lp Lq)
    (P1: strncasecmp_armv8.strncasecmp_armv8 ⊆2 prog) (P0: tolower_armv8.tolower_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f004, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X22: s R_X22 = x22) (X23: s R_X23 = x23)
    (X29: s R_X29 = x29),
  satisfies_all prog (ninvs1 sp mem raddr p q n x19 x20 x21 x22 x23 x29) (nexits1 sp mem raddr p q n x19 x20 x21 x22 x23 x29) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X22 64 eq_refl) as W22. rewrite X22 in W22. simpl in W22.
  pose proof (MDL R_X23 64 eq_refl) as W23. rewrite X23 in W23. simpl in W23.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  pose proof (MDL R_X2 64 eq_refl) as W2. rewrite X2 in W2. simpl in W2.
  assert (PP: strncasecmp_prog ⊆2 prog) by (apply strncasecmp_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strncasecmp_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold ninvs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X21 X22 X23 X29 START PRE0 W19 W20 W21 W22 W23 W29 W30 W0 W1 W2.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncasecmp_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W22 W23 W29 W30 W0 W1 W2. rename t1 into t.
  destruct PRE0 as (NFp & Zp & NFq & Zq & SP64 & SPlt & BP & BQ).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W20, W21, W22, W23, W29, W30, W0, W1, W2. clear WW.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  assert (CB: ∀ a, a < sp - 64 -> D0 sp mem raddr x19 x20 x21 x22 x23 x29 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold D0, ncase_frame. memsimp. reflexivity. }
  assert (KB: ∀ k, ceq mem p q k -> k <= Lp /\ k <= Lq).
  { intros k CE. split; destruct (N.le_gt_cases k Lp) as [H|H]; try destruct (N.le_gt_cases k Lq) as [H'|H'];
      try lia; exfalso; first [ exact (proj1 (CE Lp H) Zp) | exact (proj1 (proj2 (CE Lq H')) Zq) ]. }
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X21 & X22 & X23 & X29).
    repeat grok_step.
    + apply N.eqb_eq in BC. splits; first [assumption | reflexivity].
    + apply N.eqb_neq in BC. exists 0. rewrite !(MS sp) by lia. rewrite (MS n) by lia. rewrite !N.add_0_r.
      splits; try reflexivity; try lia. unfold ceq. intros i I. lia.
  - destruct PRE as (k & KN & X19 & X20 & X21 & X22 & CE & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat grok_step.
    all: nprep CB.
    all: first [ (exists k; solve [splits; ncloser]) | (exists (k+1); solve [splits; ncloser]) ].
  - destruct PRE as (k & KN & X19 & X20 & X21 & X22 & CE & NZ1 & NZ2 & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat grok_step.
    all: nprep CB.
    all: first [ (exists k; solve [splits; ncloser]) | (exists (k+1); solve [splits; ncloser]) ].
  - destruct PRE as (k & KN & X19 & X20 & X21 & X22 & CE & NZ1 & NZ2 & X23 & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat grok_step.
    all: nprep CB.
    all: first [ (exists k; solve [splits; ncloser]) | (exists (k+1); solve [splits; ncloser]) ].
  - destruct PRE as (k & KN & X20 & CE & ST & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat grok_step.
    all: nprep CB.
    all: first [ (exists k; solve [splits; ncloser]) | (exists (k+1); solve [splits; ncloser]) ].
  - destruct PRE as (k & KN & CE & ST & X19 & X0 & MEM & SP & X29).
    repeat grok_step.
    exists k.
    replace (8 + (sp - 64)) with (sp - 56) by lia. replace (16 + (sp - 64)) with (sp - 48) by lia.
    replace (24 + (sp - 64)) with (sp - 40) by lia. replace (32 + (sp - 64)) with (sp - 32) by lia.
    replace (40 + (sp - 64)) with (sp - 24) by lia. replace (48 + (sp - 64)) with (sp - 16) by lia.
    unfold D0, ncase_frame.
    splits; try first [assumption | reflexivity | lia]; memsimp; apply N.mod_small; L64.
Qed.
