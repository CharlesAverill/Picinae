(* strcasecmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls tolower)

   SEMANTICS
   ---------
   musl's src/string/strcasecmp.c:
       int strcasecmp(const char *_l, const char *_r) {
           const unsigned char *l = [cast] _l, *r = [cast] _r;
           for (; *l && *r && ( *l == *r || tolower( *l) == tolower( *r)); l++, r++);
           return tolower( *l) - tolower( *r);
       }
   compiled as a 48-byte frame (stp x29,x30,[sp,#-48]! / stp x19,x20 / str x21),
   a byte loop with four bl tolower sites (0x11f2d0, the C-locale tolower
   proved in tolower_proof.v; here its code is part of strcasecmp_prog and is
   executed symbolically at each call), sub w0,w20,w0 and the frame restore.

   SPECIFICATION (man 3 strcasecmp, Linux man-pages 6.9.1)
   -------------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            int strcasecmp(const char *s1, const char *s2);
     DESCRIPTION
            The strcasecmp() function performs a byte-by-byte comparison of
            the strings s1 and s2, ignoring the case of the characters.  It
            returns an integer less than, equal to, or greater than zero if s1
            is found, respectively, to be less than, to match, or be greater
            than s2.
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
            strcasecmp at 0x5ea9c (ELF vaddr); 0x15ea9c in Ghidra (image base 0x100000);
            callee tolower at 0x1f2d0 / 0x11f2d0
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strcasecmp_armv8.v and
            ../lifted/tolower_armv8.v (combined as strcasecmp_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1 (p), X1 = s2 (q), SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.
   PRECONDITION (strcasecmp_pre sp mem p q Lp Lq), stated explicitly:
            - p holds a string of length Lp (bytes p..p+Lp-1 nonzero, byte
              p+Lp = 0) and q a string of length Lq (likewise);
            - 48 <= sp < 2^64 and both strings, terminators included, lie
              strictly below sp-48, i.e. below strcasecmp's own stack frame
              (sp-48..sp).
            Justification: the strings must be valid C strings (otherwise the
            behaviour is undefined), and memory at or above sp-48 is the
            callee's stack, which no caller-owned object may occupy under
            AAPCS64 (no red zone); so the precondition only excludes undefined
            behaviour.  It is needed because strcasecmp stores its frame
            (x29, raddr, x19, x20, x21) before reading the strings.
   Output:  If execution reaches the RET (0x15eb1c), there is a k with
            - for all i < k: bytes p+i and q+i are nonzero and
              tolower_spec of them are equal (ceq);
            - at k: byte p+k = 0, or byte q+k = 0, or their tolower_spec
              values differ (cstop);
            - X0 = msub 32 (tolower_spec mem[p+k]) (tolower_spec mem[q+k]),
              i.e. the 32-bit int tolower( *l) - tolower( *r);
            and memory = mem with the saved frame (x29, raddr, x19, x20, x21
            at sp-48, sp-40, sp-32, sp-24, sp-16), SP = sp, X19 = x19,
            X20 = x20, X21 = x21, X29 = x29, X30 = raddr.  tolower_spec is
            defined in tolower_proof.v.  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcasecmp_armv8 tolower_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import tolower_proof.
Import ARM8Notations.
Open Scope N.

Definition strcasecmp_prog : program := updateall2 strcasecmp_armv8.strcasecmp_armv8 tolower_armv8.tolower_armv8.

Theorem strcasecmp_prog_welltyped: welltyped_prog arm8typctx strcasecmp_prog.
Proof.
  intros s a. unfold strcasecmp_prog, updateall2, updateall.
  destruct (tolower_armv8.tolower_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (tolower_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strcasecmp_armv8.welltyped.
Qed.

Lemma strcasecmp_prog_mono: ∀ prog, strcasecmp_armv8.strcasecmp_armv8 ⊆2 prog -> tolower_armv8.tolower_armv8 ⊆2 prog -> strcasecmp_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold strcasecmp_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

Lemma tolower_lt32: ∀ c, tolower_spec c < 2^32.
Proof.
  intro c. unfold tolower_spec. pose proof (N.mod_lt c (2^32) ltac:(discriminate)).
  destruct (_ && _) eqn:E; [|assumption].
  apply andb_prop in E. destruct E as [_ E]. apply N.leb_le in E. change (2^32) with 4294967296 in *. lia.
Qed.

(* the first k byte pairs are nonzero and equal after tolower *)
Definition ceq (m:memory) (p q k:N) :=
  ∀ i, i < k -> m Ⓑ[p+i] ≠ 0 /\ m Ⓑ[q+i] ≠ 0 /\ tolower_spec (m Ⓑ[p+i]) = tolower_spec (m Ⓑ[q+i]).

Definition cstop (m:memory) (p q k:N) :=
  m Ⓑ[p+k] = 0 \/ m Ⓑ[q+k] = 0 \/ tolower_spec (m Ⓑ[p+k]) <> tolower_spec (m Ⓑ[q+k]).

Lemma ceq_succ: ∀ m p q k, ceq m p q k -> m Ⓑ[p+k] ≠ 0 -> m Ⓑ[q+k] ≠ 0 ->
  tolower_spec (m Ⓑ[p+k]) = tolower_spec (m Ⓑ[q+k]) -> ceq m p q (k+1).
Proof.
  intros m p q k C A B E i I. destruct (N.lt_ge_cases i k) as [H|H].
  - apply C. exact H.
  - replace i with k by lia. auto.
Qed.

Definition case_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20] [Ⓠ sp - 16 := x21].

Definition strcasecmp_pre (sp mem p q Lp Lq : N) :=
  nilfree mem p Lp /\ mem Ⓑ[p + Lp] = 0 /\ nilfree mem q Lq /\ mem Ⓑ[q + Lq] = 0 /\
  48 <= sp /\ sp < 2^64 /\ p + Lp < sp - 48 /\ q + Lq < sp - 48.

Definition strcasecmp_post (sp mem raddr p q x19 x20 x21 x29 : N) (s:store) :=
  ∃ k, ceq mem p q k /\ cstop mem p q k /\
  s R_X0 = msub 32 (tolower_spec (mem Ⓑ[p+k])) (tolower_spec (mem Ⓑ[q+k])) /\
  s V_MEM64 = case_frame sp mem raddr x19 x20 x21 x29 /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr p q x19 x20 x21 x29 : N).
  Definition C0 := case_frame sp mem raddr x19 x20 x21 x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcasecmp *)
    | 0x15ea9c => Inv 1 (s R_X0 = p /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    | 0x15eac0 => Inv 1 (∃ k, s R_X20 = p + k /\ s R_X19 = q + k /\ ceq mem p q k /\ s V_MEM64 = C0 /\ s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15eae0 => Inv 1 (∃ k, s R_X20 = p + k /\ s R_X19 = q + k /\ ceq mem p q k /\
                         mem Ⓑ[p+k] ≠ 0 /\ mem Ⓑ[q+k] ≠ 0 /\ s R_X0 = tolower_spec (mem Ⓑ[p+k]) /\ s V_MEM64 = C0 /\ s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15eaec => Inv 1 (∃ k, s R_X20 = p + k /\ s R_X19 = q + k /\ ceq mem p q k /\
                         mem Ⓑ[p+k] ≠ 0 /\ mem Ⓑ[q+k] ≠ 0 /\ s R_X21 = tolower_spec (mem Ⓑ[p+k]) /\
                         s R_X0 = tolower_spec (mem Ⓑ[q+k]) /\ s V_MEM64 = C0 /\ s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15eb00 => Inv 1 (∃ k, s R_X19 = q + k /\ ceq mem p q k /\ cstop mem p q k /\
                         s R_X0 = tolower_spec (mem Ⓑ[p+k]) /\ s V_MEM64 = C0 /\ s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15eb0c => Inv 1 (∃ k, ceq mem p q k /\ cstop mem p q k /\
                         s R_X20 = tolower_spec (mem Ⓑ[p+k]) /\ s R_X0 = tolower_spec (mem Ⓑ[q+k]) /\ s V_MEM64 = C0 /\ s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15eb1c => Post 1 (strcasecmp_post sp mem raddr p q x19 x20 x21 x29 s)
    | _ => NoInv
    end.
  Definition exits1 := make_exits 1 strcasecmp_prog invs.
  Definition invs1 := make_invs 1 strcasecmp_prog invs.
End Invariants.

Lemma TLF: ∀ x, x < 2^32 -> (26 <=? msub 32 x 65) = true -> tolower_spec x = x.
Proof.
  intros x X H. apply N.leb_le in H. unfold tolower_spec. rewrite N.mod_small by exact X.
  destruct (65 <=? x) eqn:L1, (x <=? 90) eqn:L2; try reflexivity.
  apply N.leb_le in L1, L2. exfalso. assert (msub 32 x 65 < 26) by (apply msub32_range; cbn; [lia|lia|rewrite N.mod_small by exact X; lia]). lia.
Qed.

Lemma TLT: ∀ x, x < 2^32 -> (26 <=? msub 32 x 65) = false -> tolower_spec x = x .| 32.
Proof.
  intros x X H. apply N.leb_gt in H. rewrite (msub32_range x 65 26) in H by (cbn; lia).
  rewrite N.mod_small in H by exact X. unfold tolower_spec. rewrite N.mod_small by exact X.
  rewrite (proj2 (N.leb_le 65 _)), (proj2 (N.leb_le _ 90)) by lia. cbn [andb].
  symmetry. apply or32_range. lia.
Qed.

Lemma TL32: ∀ c, tolower_spec c mod 2^32 = tolower_spec c.
Proof. intro c. apply N.mod_small, tolower_lt32. Qed.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Ltac prep CB KB :=
  repeat match goal with H: context [C0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 Ⓑ[?a]] |- _ => rewrite (CB a) in H by L64 end;
  repeat match goal with |- context [C0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 Ⓑ[?a]] => rewrite (CB a) by L64 end;
  repeat match goal with
  | H: (26 <=? msub 32 _ 65) = true |- _ => apply TLF in H; [|apply byte_lt32]
  | H: (26 <=? msub 32 _ 65) = false |- _ => apply TLT in H; [|apply byte_lt32]
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end;
  rewrite ?TL32 in *.
Ltac closer :=
  first [ assumption | reflexivity | congruence
        | (left; assumption) | (right; left; assumption) | (right; right; congruence)
        | (apply ceq_succ; try assumption; congruence)
        | (rewrite N.mod_small by L64; lia) | lia ].

Theorem strcasecmp_partial_correctness:
  ∀ prog s sp mem raddr p q x19 x20 x21 x29 Lp Lq t xs'
    (PRE0: strcasecmp_pre sp mem p q Lp Lq)
    (P1: strcasecmp_armv8.strcasecmp_armv8 ⊆2 prog) (P0: tolower_armv8.tolower_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ea9c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p q x19 x20 x21 x29) (exits1 sp mem raddr p q x19 x20 x21 x29) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  assert (PP: strcasecmp_prog ⊆2 prog) by (apply strcasecmp_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strcasecmp_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X21 X29 START PRE0 W19 W20 W21 W29 W30.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasecmp_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W29 W30. rename t1 into t.
  destruct PRE0 as (NFp & Zp & NFq & Zq & SP48 & SPlt & BP & BQ).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W19, W20, W21, W29, W30. clear WW.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  assert (CB: ∀ a, a < sp - 48 -> C0 sp mem raddr x19 x20 x21 x29 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold C0, case_frame. memsimp. reflexivity. }
  assert (Q48: C0 sp mem raddr x19 x20 x21 x29 Ⓠ[sp - 48] = x29) by (unfold C0, case_frame; memsimp; apply N.mod_small; L64).
  assert (Q40: C0 sp mem raddr x19 x20 x21 x29 Ⓠ[sp - 40] = raddr) by (unfold C0, case_frame; memsimp; apply N.mod_small; L64).
  assert (Q32: C0 sp mem raddr x19 x20 x21 x29 Ⓠ[sp - 32] = x19) by (unfold C0, case_frame; memsimp; apply N.mod_small; L64).
  assert (Q24: C0 sp mem raddr x19 x20 x21 x29 Ⓠ[sp - 24] = x20) by (unfold C0, case_frame; memsimp; apply N.mod_small; L64).
  assert (Q16: C0 sp mem raddr x19 x20 x21 x29 Ⓠ[sp - 16] = x21) by (unfold C0, case_frame; memsimp; apply N.mod_small; L64).
  (* bounds on k: ceq forces k <= Lp, Lq *)
  assert (KB: ∀ k, ceq mem p q k -> k <= Lp /\ k <= Lq).
  { intros k CE. split; destruct (N.le_gt_cases k Lp) as [H|H]; try destruct (N.le_gt_cases k Lq) as [H'|H'];
      try lia; exfalso; first [ exact (proj1 (CE Lp H) Zp) | exact (proj1 (proj2 (CE Lq H')) Zq) ]. }
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    repeat arm8_step.
    exists 0. rewrite !(MS sp) by lia. rewrite !N.add_0_r.
    splits; try reflexivity. unfold ceq. intros i I. lia.
  - destruct PRE as (k & X20 & X19 & CE & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat arm8_step.
    all: prep CB KB.
    all: first [ (exists k; solve [splits; closer]) | (exists (k+1); solve [splits; closer]) ].
  - destruct PRE as (k & X20 & X19 & CE & NZ1 & NZ2 & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat arm8_step.
    all: prep CB KB.
    all: first [ (exists k; solve [splits; closer]) | (exists (k+1); solve [splits; closer]) ].
  - destruct PRE as (k & X20 & X19 & CE & NZ1 & NZ2 & X21 & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat arm8_step.
    all: prep CB KB.
    all: first [ (exists k; solve [splits; closer]) | (exists (k+1); solve [splits; closer]) ].
  - destruct PRE as (k & X19 & CE & ST & X0 & MEM & SP & X29).
    destruct (KB k CE) as [KP KQ].
    repeat arm8_step.
    all: prep CB KB.
    all: first [ (exists k; solve [splits; closer]) | (exists (k+1); solve [splits; closer]) ].
  - destruct PRE as (k & CE & ST & X20 & X0 & MEM & SP & X29).
    repeat arm8_step.
    exists k.
    replace (16 + (sp - 48)) with (sp - 32) by lia. replace (24 + (sp - 48)) with (sp - 24) by lia.
    replace (32 + (sp - 48)) with (sp - 16) by lia. replace (8 + (sp - 48)) with (sp - 40) by lia.
    splits; first [assumption | reflexivity | lia].
Qed.
