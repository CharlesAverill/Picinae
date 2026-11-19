(* strcspn, short reject-set path -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64,
   compiled C (calls __strchrnul, which calls strlen when c[0] = 0)

   SEMANTICS
   ---------
   musl's src/string/strcspn.c, first line of the body:
       if (!c[0] || !c[1]) return __strchrnul(s, c[0])-a;     (a = s)
   compiled as: stp x29,x30,[sp,#-0x50]!; mov x3,x1; mov x29,sp;
   str x19,[sp,#16]; mov x19,x0; ldrb w1,[x1]; cbz w1,0x15ed14;
   ldrb w0,[x3,#1]; cbnz w0,0x15ed2c (long path, strcspn_proof.v);
   0x15ed14: mov x0,x19; bl __strchrnul (0x15ebf4); sub x0,x0,x19;
   ldr x19,[sp,#16]; ldp x29,x30,[sp],#0x50; ret.
   This file covers exactly the reject sets with strlen(c) < 2 (the
   complement of strcspn_proof.v's precondition 2 <= strlen(c)).  The
   whole __strchrnul + strlen proof (strchrnul_proof.v) is reused through
   lib/GrokCall.v (satisfies_all_transfer); X19 = s is carried across the
   call by lib/GrokKeep.v (satisfies_all_keep: strchrnul and strlen never
   assign X19, so every transferred invariant is strengthened with X19 = s).

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
            strcspn at 0x5ecf0 (ELF vaddr); 0x15ecf0 in Ghidra (image base 0x100000)
            __strchrnul at 0x5ebf4; 0x15ebf4 in Ghidra
            strlen at 0x5efa8; 0x15efa8 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strcspn_armv8.v,
            ../lifted/strchrnul_armv8.v, ../lifted/strlen_armv8.v
            (combined as css_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = reject (c), SP = sp, X30 = raddr, X19 = x19,
            X29 = x29; memory mem.
   PRECONDITION (css_pre sp mem p c Ks Lc):
            - Ks = strlen(p): bytes p..p+Ks-1 nonzero, byte p+Ks = 0;
            - Lc = strlen(c) < 2: bytes c..c+Lc-1 nonzero, byte c+Lc = 0;
            - 112 <= sp < 2^64; p+Ks+113 <= sp and c+Lc+113 <= sp (both
              strings lie below strcspn's 80-byte frame and __strchrnul's
              32-byte frame).
   Output:  If execution reaches the RET (0x15ed28), with M the final memory
            (css_post):
            X0 = K for some K <= Ks such that no byte p[i], i < K, occurs in
            c[0..Lc), and either K = Ks or p[K] occurs in c[0..Lc)
            (strcspn_defs.cs_in) -- i.e. K = strcspn(p, c);
            SP = sp, X19 = x19, X29 = x29, X30 = raddr;
            M[a] = mem[a] for every address a outside sp-112..sp-1.
            X20..X28 and Z8..Z15 are never written
            (strcspn_short_preserves_other_callee_saved).  Partial correctness.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall GrokKeep.
From Grok.proofs Require strcspn_defs strchrnul_proof.
From Grok.proofs Require Import strcspn_short_defs.
Import ARM8Notations.
Open Scope N.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Theorem css_prog_welltyped: welltyped_prog arm8typctx css_prog.
Proof.
  intros s a. unfold css_prog, updateall2, updateall.
  destruct (strchrnul_proof.strchrnul_prog s a) as [[sz q]|] eqn:T0.
    pose proof (strchrnul_proof.strchrnul_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strcspn_armv8.welltyped.
Qed.

Lemma sc_contains: strchrnul_proof.strchrnul_prog ⊆2 css_prog.
Proof. apply subset_updateall2. Qed.

Lemma css_contains: strcspn_armv8.strcspn_armv8 ⊆2 css_prog.
Proof.
  intros s a insn SC. unfold css_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall,
    strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma css_prog_mono: ∀ prog, strcspn_armv8.strcspn_armv8 ⊆2 prog -> strchrnul_armv8.strchrnul_armv8 ⊆2 prog ->
  strlen_armv8.strlen_armv8 ⊆2 prog -> css_prog ⊆2 prog.
Proof.
  intros prog P2 P1 P0 s a insn H. unfold css_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall in H.
  destruct (strlen_armv8.strlen_armv8 s a) eqn:E0; [inversion H; subst; apply P0; exact E0|].
  destruct (strchrnul_armv8.strchrnul_armv8 s a) eqn:E1; [inversion H; subst; apply P1; exact E1|].
  apply P2; exact H.
Qed.

Lemma sc_noassign_x19: prog_noassign R_X19 strchrnul_proof.strchrnul_prog.
Proof. prove_noassign. Qed.

Lemma css_F_shape: ∀ sp mem raddr p c x19 x29 s a b m,
  strchrnul_proof.invs (sp ⊖ 80) (css_frame sp mem raddr x19 x29) 0x15ed1c p (mem Ⓑ[c]) (sp ⊖ 80)
    (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) ->
  m <= 1 /\ (b = true -> m = 1 -> a = 0x15ec40 \/ a = 0x15eca0) /\
  css_F sp mem raddr p c x19 x29 Prop (fun _ P => P) (fun _ P => P) False s a =
  (strchrnul_proof.invs (sp ⊖ 80) (css_frame sp mem raddr x19 x29) 0x15ed1c p (mem Ⓑ[c]) (sp ⊖ 80)
    Prop (fun _ P => P) (fun _ P => P) False s a /\ s R_X19 = p).
Proof.
  intros sp mem raddr p c x19 x29 s a b m H.
  unfold css_F. unfold strchrnul_proof.invs in *.
  destruct a as [|q]; [discriminate H|].
  repeat (destruct q as [q|q|]; try discriminate H);
  injection H as <- <-; (split; [lia | split; [intros B M; first [discriminate B | discriminate M | (left; reflexivity) | (right; reflexivity)] | reflexivity]]).
Qed.

Theorem strchrnul_correct_in_strcspn:
  ∀ s t xs' (ENTRY: startof t xs' = (Addr 0x15ebf4, s)) (MDL: models arm8typctx s)
    sp mem raddr p c x19 x29 Ks Lc
    (SP: s R_SP = sp ⊖ 80) (MEM: s V_MEM64 = css_frame sp mem raddr x19 x29) (X30: s R_X30 = 0x15ed1c)
    (X0: s R_X0 = p) (X1: s R_X1 = mem Ⓑ[c]) (X19: s R_X19 = p) (X29: s R_X29 = sp ⊖ 80),
  satisfies_all css_prog (css_invs1 sp mem raddr p c x19 x29 Ks Lc) (css_exits1 sp mem raddr p c x19 x29 Ks Lc) (xs'::t).
Proof.
  intros.
  set (SCI := strchrnul_proof.invs (sp ⊖ 80) (css_frame sp mem raddr x19 x29) 0x15ed1c p (mem Ⓑ[c]) (sp ⊖ 80)).
  assert (NOT: ∀ s0 a insn, strchrnul_proof.strchrnul_prog s0 a = Some insn -> (a =? 0x15ecf0) = false /\ (a =? 0x15ed28) = false).
  { intros s0 a insn IL. split.
    - destruct (N.eqb_spec a 0x15ecf0) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity].
    - destruct (N.eqb_spec a 0x15ed28) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity]. }
  assert (EM: ∀ s0 a, css_F sp mem raddr p c x19 x29 (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s0 a =
                      SCI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s0 a) by reflexivity.
  assert (XE: css_exits1 sp mem raddr p c x19 x29 Ks Lc = make_exits 1 strchrnul_proof.strchrnul_prog SCI).
  { extensionality tt. destruct tt as [|[[a|i] s0] t0]; try reflexivity.
    unfold css_exits1, make_exits. destruct (strchrnul_proof.strchrnul_prog s0 a) as [insn|] eqn:IL.
    - rewrite (sc_contains _ _ _ IL). destruct (NOT _ _ _ IL) as [E1 E2].
      unfold css_invs. rewrite E1, E2. cbv iota. rewrite EM. reflexivity.
    - destruct (css_prog s0 a) eqn:IL2; [|reflexivity].
      unfold css_invs. destruct (a =? 0x15ecf0); [reflexivity|]. destruct (a =? 0x15ed28); [reflexivity|].
      rewrite EM.
      destruct (SCI _ _ _ _ s0 a) as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 1); [|reflexivity]. subst m.
      apply css_F_shape in F. destruct F as (_ & PA & _).
      destruct (PA eq_refl eq_refl) as [E|E]; subst a; vm_compute in IL; discriminate IL. }
  unfold css_invs1. rewrite XE.
  apply satisfies_all_transfer with (p1 := strchrnul_proof.strchrnul_prog)
    (I1 := keep_invs (make_invs 1 strchrnul_proof.strchrnul_prog SCI) R_X19 p).
  - exact sc_contains.
  - intros a s0 t0 _ N0. unfold keep_invs, make_invs. rewrite N0. reflexivity.
  - intros a s0 t0 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s0 t0 insn IL. unfold keep_invs, make_invs. rewrite (sc_contains _ _ _ IL), IL.
    destruct (NOT _ _ _ IL) as [E1 E2]. unfold css_invs. rewrite E1, E2. cbv iota. rewrite EM.
    destruct (SCI _ _ _ _ s0 a) as [[b m]|] eqn:F; [|reflexivity].
    destruct (css_F_shape _ _ _ _ _ _ _ _ _ _ _ F) as (ML & _ & EQ).
    destruct (m ?= 1) eqn:CMP.
    + rewrite EQ. reflexivity.
    + reflexivity.
    + exfalso. apply N.compare_gt_iff in CMP. lia.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keep _ _ _ R_X19 p sc_noassign_x19 xs' t).
    + match goal with |- snd ?x _ = _ => replace x with (Addr 0x15ebf4, s) by (symmetry; exact ENTRY) end. exact X19.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15ebf4, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strchrnul_proof.strchrnul_partial_correctness; try eassumption.
      * exact strchrnul_proof.strchrnul_prog_contains.
      * apply subset_updateall2.
Qed.

Lemma css_cs_in: ∀ mem c Lc b, Lc < 2 -> strcspn_defs.cs_in mem c Lc b -> Lc = 1 /\ b = mem Ⓑ[c].
Proof.
  intros mem c Lc b L (i & I & E). split; [lia|]. assert (i = 0) by lia. subst i. rewrite N.add_0_r in E. auto.
Qed.

Lemma css_K: ∀ mem M p c Ks Lc r,
  nilfree mem p Ks -> mem Ⓑ[p + Ks] = 0 -> nilfree mem c Lc -> mem Ⓑ[c + Lc] = 0 -> Lc < 2 -> p + Ks < 2^64 ->
  (∀ i, i <= Ks -> M Ⓑ[p + i] = mem Ⓑ[p + i]) ->
  strchrnul_proof.strchrnul_spec M p (mem Ⓑ[c] mod 2^8) r ->
  ∃ K, K <= Ks /\ r = p + K /\ (∀ i, i < K -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
       (K = Ks \/ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K])).
Proof.
  intros mem M p c Ks Lc r NFp Zp NFc Zc L PB AG (k & KL & SC & EN & R).
  rewrite (N.mod_small (mem Ⓑ[c])) in SC, EN by apply byte_lt8.
  assert (KK: k <= Ks).
  { destruct (N.le_gt_cases k Ks) as [H|H]; [exact H|]. exfalso.
    destruct (SC Ks H) as [N0 _]. apply N0. rewrite AG by lia. exact Zp. }
  exists k. split; [exact KK|]. split.
  { rewrite R. unfold "⊕". apply N.mod_small. lia. }
  split.
  - intros i I CI. apply css_cs_in in CI; [|exact L]. destruct CI as [_ E].
    destruct (SC i I) as [_ NC]. apply NC. rewrite AG by lia. exact E.
  - rewrite AG in EN by lia.
    assert (EZ: mem Ⓑ[p + k] = 0 -> k = Ks).
    { intro Z. destruct (N.lt_ge_cases k Ks) as [H|H]; [|lia]. exfalso. exact (NFp k H Z). }
    destruct EN as [Z|E]; [left; exact (EZ Z)|].
    destruct (N.eq_dec Lc 0) as [L0|L0].
    + left. apply EZ. rewrite E. subst Lc. rewrite N.add_0_r in Zc. exact Zc.
    + right. exists 0. split; [lia|]. rewrite N.add_0_r. symmetry. exact E.
Qed.

Lemma msub_addK: ∀ p K, p < 2^64 -> K < 2^64 -> msub 64 (p + K) p = K.
Proof.
  intros p K P KL. unfold msub. rewrite (N.mod_small p) by exact P.
  replace (p + K + (2^64 - p)) with (K + 1 * 2^64) by lia.
  rewrite N.Div0.mod_add. apply N.mod_small. exact KL.
Qed.

Ltac nrm := repeat match goal with
  | H: negb ((?b >> 0) mod 2^32 =? 0) = true |- _ => apply cbnz32_true in H; [|apply byte_lt32]
  | H: negb ((?b >> 0) mod 2^32 =? 0) = false |- _ => apply cbnz32_false in H; [|apply byte_lt32]
  | H: negb (_ =? _) = true |- _ => apply Bool.negb_true_iff, N.eqb_neq in H
  | H: negb (_ =? _) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Theorem strcspn_short_partial_correctness:
  ∀ prog s sp mem raddr p c x19 x29 Ks Lc t xs'
    (PRE0: css_pre sp mem p c Ks Lc)
    (P2: strcspn_armv8.strcspn_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ecf0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (css_invs2 sp mem raddr p c x19 x29 Ks Lc) (css_exits2 sp mem raddr p c x19 x29 Ks Lc) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  assert (PP: css_prog ⊆2 prog) by (apply css_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=css_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold css_invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X29 START PRE0 W19 W29 W30 W0 W1.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply css_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0 W1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X29).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & L2 & S1 & S2 & BP & BC).
  assert (CB: ∀ a, a + 1 <= sp - 80 -> css_frame sp mem raddr x19 x29 Ⓑ[a] = mem Ⓑ[a])
    by (intros a A; unfold css_frame; rewrite !(msub_small 64 sp) by L64; memsimp; reflexivity).
  do 7 arm8_step.
  all: change (mem [Ⓠ sp ⊖ 80 := x29] [Ⓠ sp ⊖ 72 := raddr] [Ⓠ sp ⊖ 64 := x19]) with (css_frame sp mem raddr x19 x29) in *.
  all: rewrite (CB c) in * by L64.
  all: nrm.
  2: assert (L1: Lc = 1) by (destruct (N.eq_dec Lc 0) as [E|E]; [subst Lc; rewrite N.add_0_r in Zc; contradiction | lia]).
  2: do 2 arm8_step.
  2: (exfalso; rewrite CB in BC1 by (subst Lc; L64); nrm; apply BC1; rewrite N.add_comm; subst Lc; exact Zc).
  2: do 2 arm8_step.
  1: do 2 arm8_step.
  all: match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  all: eapply models_after_steps; [eassumption | apply css_prog_welltyped | intro MDL2].
  all: eapply (perform_call 1); [reflexivity | | reflexivity | ].
  1,3: intros; eapply strchrnul_correct_in_strcspn with (sp:=sp) (mem:=mem) (raddr:=raddr) (p:=p) (c:=c) (x19:=x19) (x29:=x29) (Ks:=Ks) (Lc:=Lc);
       [ eassumption | eassumption | unfold s2; reflexivity .. ].
  all: intros a' s' t2 ST XP UT PRE; clearbody s2; clear MDL2 ST XP UT.
  all: destruct_inv 64 PRE.
  all: destruct PRE as ((RSP & R30 & R29 & ALT) & R19).
  all: assert (MM: ∃ M', s' V_MEM64 = M' /\ (∀ a, a < 2^64 -> (a < sp - 112 \/ sp - 80 <= a) -> M' Ⓑ[a] = css_frame sp mem raddr x19 x29 Ⓑ[a]) /\
                    strchrnul_proof.strchrnul_spec M' p (mem Ⓑ[c] mod 2^8) (s' R_X0))
    by (destruct ALT as [(M' & CNZ & SPEC) | (M' & CZ & SPEC)];
        [ exists (css_frame sp mem raddr x19 x29); split; [exact M' | split; [reflexivity | exact SPEC]]
        | eexists; split; [exact M' | split;
            [ intros a A O; unfold strchrnul_proof.frame_mem; rewrite !(msub_small 64 sp), !(msub_small 64 (sp - 80)) by L64; destruct O as [O|O]; memsimp; reflexivity
            | unfold strchrnul_proof.c8 in CZ; rewrite CZ; exact SPEC ]] ]).
  all: clear ALT; destruct MM as (M & MEQ & MO & SPEC).
  all: repeat arm8_step.
  all: rewrite !(msub_small 64 sp) by L64.
  all: assert (FQ: ∀ a v, sp - 80 <= a -> a + 8 <= sp -> css_frame sp mem raddr x19 x29 Ⓠ[a] = v -> M Ⓠ[a] = v)
         by (intros a v A1 A2 E; rewrite <- E; apply getmem_ext; intros i I; apply MO; L64).
  all: assert (AGp: ∀ i, i <= Ks -> M Ⓑ[p + i] = mem Ⓑ[p + i]) by (intros i I; rewrite MO by L64; apply CB; L64).
  all: destruct (css_K mem M p c Ks Lc (s' R_X0) NFp Zp NFc Zc L2 ltac:(L64) AGp SPEC) as (K & KK & R & NI & KE).
  all: splits; [ exists K; splits; [exact KK | rewrite R; apply msub_addK; L64 | exact NI | exact KE]
               | reflexivity
               | apply FQ; [L64 | L64 | unfold css_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64] ..
               | intros a A O; rewrite MO by (destruct O; L64); unfold css_frame; rewrite !(msub_small 64 sp) by L64;
                 destruct O as [O|O]; memsimp; reflexivity ].
Qed.

(* Frame: strcspn's short path, __strchrnul and strlen never write X20..X28, Z8..Z15. *)
Theorem strcspn_short_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates css_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
