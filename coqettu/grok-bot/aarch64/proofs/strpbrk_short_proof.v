(* strpbrk, short accept-set path -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64,
   compiled C (calls strcspn, which calls __strchrnul, which may call strlen)

   SEMANTICS
   ---------
   musl's src/string/strpbrk.c:
       char *strpbrk(const char *s, const char *b) {
           s += strcspn(s, b);
           return s[0] ? (char * )s : 0;
       }
   compiled with a 32-byte frame (stp x29,x30,[sp,#-32]! / str x19,[sp,#16]),
   mov x19,x0; bl strcspn (0x15ecf0); add x1,x19,x0; ldrb w0,[x19,x0];
   csel x0,x1,xzr,ne; restore; ret.  This file covers accept sets with
   strlen(b) < 2, for which strcspn takes its __strchrnul path; the whole
   strcspn_short proof (strcspn_short_proof.v) is reused through
   lib/GrokCall.v (satisfies_all_transfer).  strpbrk_proof.v covers
   strlen(b) >= 2; together the two theorems cover every accept set.

   SPECIFICATION (man 3 strpbrk, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            char *strpbrk(const char *s, const char *accept);
     DESCRIPTION
            The strpbrk() function locates the first occurrence in the string
            s of any of the bytes in the string accept.
     RETURN VALUE
            The strpbrk() function returns a pointer to the byte in s that
            matches one of the bytes in accept, or NULL if no such byte is
            found.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strpbrk at 0x5f1f8 (ELF vaddr); 0x15f1f8 in Ghidra (image base 0x100000);
            callees strcspn 0x5ecf0 / 0x15ecf0, __strchrnul 0x5ebf4 / 0x15ebf4,
            strlen 0x5efa8 / 0x15efa8
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strpbrk_armv8.v,
            ../lifted/strcspn_armv8.v, ../lifted/strchrnul_armv8.v and
            ../lifted/strlen_armv8.v (combined as pbs_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = accept (c), SP = sp, X30 = raddr, X19 = x19,
            X29 = x29; memory mem.
   PRECONDITION (pbs_pre sp mem p c Ks Lc):
            - Ks = strlen(p), Lc = strlen(c) (nonzero bytes then a NUL);
            - Lc < 2;
            - 144 <= sp < 2^64; p+Ks+145 <= sp and c+Lc+145 <= sp (both
              strings lie below the three stack frames, sp-144..sp-1).
   Output:  If execution reaches the RET (0x15f224), with M the final memory:
            for some K <= Ks such that no p[i], i < K, occurs in c[0..Lc):
              either K = Ks and X0 = 0 (no byte found), or K < Ks, p[K]
              occurs in c[0..Lc) and X0 = p + K;
            SP = sp, X19 = x19, X29 = x29, X30 = raddr;
            M[a] = mem[a] for every address a outside sp-144..sp-1 (pbs_post).
            X20..X28 and Z8..Z15 are never written
            (strpbrk_short_preserves_other_callee_saved).  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strpbrk_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall.
From Grok.proofs Require strcspn_defs strchrnul_proof.
From Grok.proofs Require Import strcspn_short_defs strcspn_short_proof.
From Grok.proofs Require Import strpbrk_short_defs.
Import ARM8Notations.
Open Scope N.


Theorem pbs_prog_welltyped: welltyped_prog arm8typctx pbs_prog.
Proof.
  intros s a. unfold pbs_prog, updateall2, updateall.
  destruct (css_prog s a) as [[sz q]|] eqn:T0.
    pose proof (css_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strpbrk_armv8.welltyped.
Qed.

Lemma sc_in_css: strchrnul_armv8.strchrnul_armv8 ⊆2 css_prog.
Proof. intros s a i H. apply sc_contains. apply strchrnul_proof.strchrnul_prog_contains. exact H. Qed.

Lemma sl_in_css: strlen_armv8.strlen_armv8 ⊆2 css_prog.
Proof. intros s a i H. apply sc_contains. apply subset_updateall2. exact H. Qed.

Lemma pbs_prog_contains: strpbrk_armv8.strpbrk_armv8 ⊆2 pbs_prog.
Proof.
  intros s a insn SC. unfold pbs_prog, css_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall, strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8, strcspn_armv8.strcspn_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma pbs_CB: ∀ sp mem raddr x19 x29 a, 32 <= sp -> sp < 2^64 -> a + 1 <= sp - 32 ->
  pbs_frame sp mem raddr x19 x29 Ⓑ[a] = mem Ⓑ[a].
Proof. intros. unfold pbs_frame. rewrite !(msub_small 64 sp) by L64. memsimp. reflexivity. Qed.

Lemma pbs_css_pre: ∀ sp mem raddr x19 x29 p c Ks Lc, pbs_pre sp mem p c Ks Lc ->
  css_pre (sp ⊖ 32) (pbs_frame sp mem raddr x19 x29) p c Ks Lc.
Proof.
  intros sp mem raddr x19 x29 p c Ks Lc (NFp & Zp & NFc & Zc & L2 & S1 & S2 & BP & BC).
  unfold css_pre. rewrite (msub_small 64 sp) by L64.
  splits; try (intros i I; rewrite pbs_CB by L64; first [apply NFp, I | apply NFc, I]);
    try (rewrite pbs_CB by L64; assumption); try L64.
Qed.

Lemma pbs_cs_in: ∀ sp mem raddr x19 x29 c Lc b, 32 <= sp -> sp < 2^64 -> c + Lc + 33 <= sp ->
  (strcspn_defs.cs_in (pbs_frame sp mem raddr x19 x29) c Lc b <-> strcspn_defs.cs_in mem c Lc b).
Proof.
  intros sp mem raddr x19 x29 c Lc b S1 S2 BC. unfold strcspn_defs.cs_in. split; intros (i & I & E); exists i; split; try exact I.
  - rewrite <- E. symmetry. apply pbs_CB; L64.
  - rewrite <- E. apply pbs_CB; L64.
Qed.

Lemma css_post_addr: ∀ sp mem raddr p c x19 x29 Ks Lc s a,
  css_invs sp mem raddr p c x19 x29 Ks Lc (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,2) -> a = 0x15ed28.
Proof.
  intros sp mem raddr p c x19 x29 Ks Lc s a H.
  unfold css_invs in H.
  destruct (N.eqb_spec a 0x15ecf0); [discriminate H|].
  destruct (N.eqb_spec a 0x15ed28) as [E|E]; [exact E|].
  apply css_F_shape in H. lia.
Qed.

Theorem strcspn_short_correct_in_strpbrk:
  ∀ s t xs' (ENTRY: startof t xs' = (Addr 0x15ecf0, s)) (MDL: models arm8typctx s)
    sp mem raddr p c Ks Lc x19 x29 (PRE0: pbs_pre sp mem p c Ks Lc)
    (SP: s R_SP = sp ⊖ 32) (MEM: s V_MEM64 = pbs_frame sp mem raddr x19 x29) (X30: s R_X30 = 0x15f20c)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X19: s R_X19 = p) (X29: s R_X29 = sp ⊖ 32),
  satisfies_all pbs_prog (pbs_invs2 sp mem raddr p c Ks Lc x19 x29) (pbs_exits2 sp mem raddr p c Ks Lc x19 x29) (xs'::t).
Proof.
  intros.
  assert (NOT: ∀ s0 a insn, css_prog s0 a = Some insn -> (a =? 0x15f1f8) = false /\ (a =? 0x15f224) = false).
  { intros s0 a insn IL. split.
    - destruct (N.eqb_spec a 0x15f1f8) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity].
    - destruct (N.eqb_spec a 0x15f224) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity]. }
  assert (XE: pbs_exits2 sp mem raddr p c Ks Lc x19 x29 = make_exits 2 css_prog (pbs_F sp mem raddr p c Ks Lc x19 x29)).
  { extensionality tt. destruct tt as [|[[a|i] s0] t0]; try reflexivity.
    unfold pbs_exits2, make_exits. destruct (css_prog s0 a) as [insn|] eqn:IL.
    - rewrite (subset_updateall2 css_prog strpbrk_armv8.strpbrk_armv8 _ _ _ IL : pbs_prog s0 a = Some insn). destruct (NOT _ _ _ IL) as [E1 E2].
      unfold pbs_invs. rewrite E1, E2. reflexivity.
    - destruct (pbs_prog s0 a) eqn:IL2; [|reflexivity].
      unfold pbs_invs. destruct (a =? 0x15f1f8); [reflexivity|]. destruct (a =? 0x15f224); [reflexivity|].
      destruct (pbs_F sp mem raddr p c Ks Lc x19 x29 _ _ _ _ s0 a) as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 2); [|reflexivity]. subst m.
      apply css_post_addr in F. subst a. vm_compute in IL. discriminate IL. }
  unfold pbs_invs2. rewrite XE.
  apply satisfies_all_transfer with (p1 := css_prog) (I1 := make_invs 2 css_prog (pbs_F sp mem raddr p c Ks Lc x19 x29)).
  - apply subset_updateall2.
  - intros a s0 t0 _ N0. unfold make_invs. rewrite N0. reflexivity.
  - intros a s0 t0 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s0 t0 insn IL. unfold make_invs. rewrite (subset_updateall2 css_prog strpbrk_armv8.strpbrk_armv8 _ _ _ IL : pbs_prog s0 a = Some insn), IL.
    destruct (NOT _ _ _ IL) as [E1 E2]. unfold pbs_invs. rewrite E1, E2. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros xs1 t1 START. rewrite ENTRY in START.
    eapply strcspn_short_partial_correctness; try eassumption.
    + apply pbs_css_pre. exact PRE0.
    + apply css_contains.
    + apply sc_in_css.
    + apply sl_in_css.
Qed.

Theorem strpbrk_short_partial_correctness:
  ∀ prog s sp mem raddr p c Ks Lc x19 x29 t xs'
    (PRE0: pbs_pre sp mem p c Ks Lc)
    (P3: strpbrk_armv8.strpbrk_armv8 ⊆2 prog) (P2: strcspn_armv8.strcspn_armv8 ⊆2 prog)
    (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f1f8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (pbs_invs3 sp mem raddr p c Ks Lc x19 x29) (pbs_exits3 sp mem raddr p c Ks Lc x19 x29) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  assert (PP: pbs_prog ⊆2 prog).
  { unfold pbs_prog. rewrite <- (updateall2_subset _ _ (css_prog_mono prog P2 P1 P0)). apply updateall2_mono. exact P3. }
  eapply satisfies_all_pmono with (p1:=pbs_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold pbs_invs3, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X29 START PRE0 W19 W29 W30 W0.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply pbs_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X29).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & L2 & S1 & S2 & BP & BC).
  do 5 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply pbs_prog_welltyped. intro MDL2.
  eapply (perform_call 2). reflexivity.
  intros. eapply strcspn_short_correct_in_strpbrk with (sp:=sp) (mem:=mem) (raddr:=raddr) (x19:=x19) (x29:=x29);
    first [ eassumption | reflexivity | (unfold s2; simpl_stores; first [ sassumption | reflexivity ]) ].
  reflexivity.
  intros.
  clearbody s2. rename s' into s3.
  destruct_inv 64 PRE.
  destruct PRE as ((K & KK & R0 & NI & KE) & RSP & R19 & R29 & R30 & MO).
  clear MDL1 MDL2.
  rewrite (msub_small 64 sp 32) in MO by L64.
  assert (FB: ∀ a, a < 2^64 -> (a < sp - 144 \/ sp - 32 <= a) -> s3 V_MEM64 Ⓑ[a] = pbs_frame sp mem raddr x19 x29 Ⓑ[a]).
  { intros a A O. apply MO; [exact A | L64]. }
  clear MO.
  assert (PK: s3 V_MEM64 Ⓑ[p + K] = mem Ⓑ[p + K]) by (rewrite FB by L64; apply pbs_CB; L64).
  assert (NI': ∀ i, i < K -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])).
  { intros i I C. apply (NI i I). rewrite pbs_CB by L64. apply pbs_cs_in; [L64 | L64 | L64 | exact C]. }
  assert (KE': K = Ks \/ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K])).
  { destruct KE as [E|C]; [left; exact E | right]. rewrite pbs_CB in C by L64. apply (pbs_cs_in sp mem raddr x19 x29); [L64 | L64 | L64 | exact C]. }
  clear NI KE.
  assert (FQ: ∀ a v, sp - 32 <= a -> a + 8 <= sp -> pbs_frame sp mem raddr x19 x29 Ⓠ[a] = v -> s3 V_MEM64 Ⓠ[a] = v).
  { intros a v A1 A2 E. rewrite <- E. apply getmem_ext. intros i I. apply FB; L64. }
  assert (Q16: pbs_frame sp mem raddr x19 x29 Ⓠ[sp - 16] = x19) by (unfold pbs_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q32: pbs_frame sp mem raddr x19 x29 Ⓠ[sp - 32] = x29) by (unfold pbs_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q24: pbs_frame sp mem raddr x19 x29 Ⓠ[sp - 24] = raddr) by (unfold pbs_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (OUT: ∀ a, a < 2^64 -> (a < sp - 144 \/ sp <= a) -> s3 V_MEM64 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A O. rewrite FB by L64. unfold pbs_frame. rewrite !(msub_small 64 sp) by L64. destruct O as [O|O]; memsimp; reflexivity. }
  clear FB.
  repeat arm8_step.
  all: match goal with H: (_ =? 0) = _ |- _ => rewrite PK in H end.
  all: nrm.
  all: rewrite !(msub_small 64 sp) by L64.
  all: splits; [| reflexivity | apply FQ; first [exact Q16 | L64] | apply FQ; first [exact Q32 | L64] | apply FQ; first [exact Q24 | L64] | exact OUT].
  all: match type of KK with ?k <= _ => set (KV := k) in * end.
  - assert (EK: KV = Ks) by (destruct (N.lt_ge_cases KV Ks) as [LT|GE]; [exfalso; apply (NFp KV LT); sassumption | L64]).
    exists KV. splits; [L64 | exact NI' | left; split; [exact EK | reflexivity]].
  - assert (KL: KV < Ks) by (destruct (N.lt_ge_cases KV Ks) as [LT|GE]; [exact LT | exfalso; assert (EK: KV = Ks) by L64; rewrite EK in *;
        match goal with H: ~ (_ = 0) |- _ => exact (H Zp) end]).
    exists KV. splits; [L64 | exact NI' |]. right. splits; [exact KL | | ].
    + destruct KE' as [E|C]; [exfalso; L64 | exact C].
    + apply N.mod_small. L64.
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorem: strpbrk, strcspn, __strchrnul and strlen never write X20..X28, Z8..Z15. *)
Theorem strpbrk_short_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates pbs_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
