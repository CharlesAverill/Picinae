(* strsep -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strcspn)

   SEMANTICS
   ---------
   musl's src/string/strsep.c:
       char *strsep(char **str, const char *sep) {
           char *s = *str, *end;
           if (!s) return NULL;
           end = s + strcspn(s, sep);
           if ( *end) *end++ = 0;
           else end = 0;
           *str = end;
           return s;
       }
   compiled as: ldr x2,[x0]; cbz x2 -> return x2 (= 0); else 32-byte frame
   (stp x29,x30,[sp,#-32]!), s and str spilled at sp-16 / sp-8, bl strcspn
   (0x15ecf0), reload, ldrb w4,[x2,x0]; if nonzero: x1 = s+K+1 and
   strb wzr,[x2,x0], else x1 = 0; str x1,[x3]; return s.  The whole strcspn
   proof is reused through lib/GrokCall.v (satisfies_all_transfer).

   SPECIFICATION (man 3 strsep, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            char *strsep(char **restrict stringp, const char *restrict delim);
     DESCRIPTION
            If *stringp is NULL, the strsep() function returns NULL and does
            nothing else.  Otherwise, this function finds the first token in
            the string *stringp, that is delimited by one of the bytes in the
            string delim.  This token is terminated by overwriting the
            delimiter with a null byte ('\0'), and *stringp is updated to point
            past the token.  In case no delimiter was found, the token is taken
            to be the entire string *stringp, and *stringp is made NULL.
     RETURN VALUE
            The strsep() function returns a pointer to the token, that is, it
            returns the original value of *stringp.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strsep at 0x5f258 (ELF vaddr); 0x15f258 in Ghidra (image base 0x100000);
            callees strcspn at 0x5ecf0 / 0x15ecf0 and memset at 0x18400 / 0x118400
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strsep_armv8.v,
            ../lifted/strcspn_armv8.v and ../lifted/memset_armv8.v (combined as
            se_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = stringp (q), X1 = delim (c), SP = sp, X30 = raddr, X19 = x19,
            X29 = x29; memory mem; p = mem[q..q+8) (= *stringp).
   PRECONDITION (se_pre sp mem q p c Ks Lc), stated explicitly:
            mem Ⓠ[q] = p, and either p = 0, or:
            - Ks = strlen(p), Lc = strlen(c);
            - 2 <= Lc (inherited from the restricted strcspn proof: the
              strchrnul path for a 0- or 1-byte delimiter set is not covered);
            - 4208 <= sp < 2^64; p+Ks+113 <= sp, c+Lc+113 <= sp and
              q+8+112 <= sp (strings and *stringp lie below the two stack frames).
   Output:  If p = 0: at the RET 0x15f2a8, X0 = 0, memory unchanged, SP = sp,
            X30 = raddr.
            Otherwise at the RET 0x15f2a0 (se_post): X0 = p, SP = sp, X19 = x19,
            X29 = x29, X30 = raddr, and for some K <= Ks such that no p[i], i < K,
            occurs in c[0..Lc), with M the final memory, for every address a
            outside sp-112..sp-1:
              either K = Ks and M[a] = mem[Ⓠ q := 0][a]   ( *stringp := NULL ),
              or K < Ks, p[K] occurs in c[0..Lc) and
                 M[a] = mem[Ⓑ p+K := 0][Ⓠ q := p+K+1][a]   (token cut, *stringp advanced).
            X20..X28 and Z8..Z15 are never written
            (strsep_preserves_other_callee_saved).  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strsep_armv8 strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall.
From Grok.proofs Require Import strcspn_defs strcspn_proof strsep_defs.
Import ARM8Notations.
Open Scope N.


Theorem se_prog_welltyped: welltyped_prog arm8typctx se_prog.
Proof.
  intros s a. unfold se_prog, updateall2, updateall.
  destruct (cs_prog s a) as [[sz q]|] eqn:T0.
    pose proof (cs_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strsep_armv8.welltyped.
Qed.

Lemma cs_contains: strcspn_armv8.strcspn_armv8 ⊆2 cs_prog.
Proof.
  intros s a insn SC. unfold cs_prog, updateall2, updateall, memset_armv8.memset_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma ms_contains: memset_armv8.memset_armv8 ⊆2 cs_prog.
Proof. apply subset_updateall2. Qed.

Lemma se_prog_contains: strsep_armv8.strsep_armv8 ⊆2 se_prog.
Proof.
  intros s a insn SC. unfold se_prog, cs_prog, updateall2, updateall, memset_armv8.memset_armv8, strcspn_armv8.strcspn_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.



Lemma se_CB: ∀ sp mem raddr x29 p q a, 32 <= sp -> sp < 2^64 -> a + 1 <= sp - 32 ->
  se_frame sp mem raddr x29 p q Ⓑ[a] = mem Ⓑ[a].
Proof. intros. unfold se_frame. rewrite !(msub_small 64 sp) by L64. memsimp. reflexivity. Qed.

Lemma se_cs_pre: ∀ sp mem raddr x29 p q c Ks Lc,
  nilfree mem p Ks -> mem Ⓑ[p + Ks] = 0 -> nilfree mem c Lc -> mem Ⓑ[c + Lc] = 0 -> 2 <= Lc ->
  4096 + 112 <= sp -> sp < 2^64 -> p + Ks + 113 <= sp -> c + Lc + 113 <= sp ->
  cs_pre (sp ⊖ 32) (se_frame sp mem raddr x29 p q) p c Ks Lc.
Proof.
  intros sp mem raddr x29 p q c Ks Lc NFp Zp NFc Zc L2 S1 S2 BP BC.
  unfold cs_pre. rewrite (msub_small 64 sp) by L64.
  splits; try (intros i I; rewrite se_CB by L64; first [apply NFp, I | apply NFc, I]);
    try (rewrite se_CB by L64; assumption); try L64.
Qed.

Lemma se_cs_in: ∀ sp mem raddr x29 p q c Lc b, 32 <= sp -> sp < 2^64 -> c + Lc + 33 <= sp ->
  (cs_in (se_frame sp mem raddr x29 p q) c Lc b <-> cs_in mem c Lc b).
Proof.
  intros sp mem raddr x29 p q c Lc b S1 S2 BC. unfold cs_in. split; intros (i & I & E); exists i; split; try exact I.
  - rewrite <- E. symmetry. apply se_CB; L64.
  - rewrite <- E. apply se_CB; L64.
Qed.

Lemma set_pt: ∀ len m1 m2 b v a, b + len <= 2^64 -> a < 2^64 -> m1 Ⓑ[a] = m2 Ⓑ[a] ->
  (setmem 64 LittleE len m1 b v) Ⓑ[a] = (setmem 64 LittleE len m2 b v) Ⓑ[a].
Proof.
  intros len m1 m2 b v a B A E. destruct (N.le_gt_cases b a) as [H1|H1].
  - destruct (N.lt_ge_cases a (b + len)) as [H2|H2].
    + rewrite !read_in by L64. reflexivity.
    + rewrite !read_out by L64. exact E.
  - rewrite !read_out by L64. exact E.
Qed.

Lemma cs_post_addr: ∀ sp mem raddr p c x19 x29 Ks Lc s a,
  strcspn_defs.invs sp mem raddr p c x19 x29 Ks Lc (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,1) -> a = 0x15ed28.
Proof.
  intros sp mem raddr p c x19 x29 Ks Lc s a H.
  unfold strcspn_defs.invs in H.
  destruct a as [|r]; [discriminate H|].
  repeat (destruct r as [r|r|]; try discriminate H); first [reflexivity | discriminate H].
Qed.

Theorem strcspn_correct_in_strsep:
  ∀ s t xs' (ENTRY: startof t xs' = (Addr 0x15ecf0, s)) (MDL: models arm8typctx s)
    sp mem raddr q p c Ks Lc x19 x29
    (NFp: nilfree mem p Ks) (Zp: mem Ⓑ[p + Ks] = 0) (NFc: nilfree mem c Lc) (Zc: mem Ⓑ[c + Lc] = 0) (L2: 2 <= Lc)
    (S1: 4096 + 112 <= sp) (S2: sp < 2^64) (BP: p + Ks + 113 <= sp) (BC: c + Lc + 113 <= sp)
    (SP: s R_SP = sp ⊖ 32) (MEM: s V_MEM64 = se_frame sp mem raddr x29 p q) (X30: s R_X30 = 0x15f278)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X19: s R_X19 = x19) (X29: s R_X29 = sp ⊖ 32),
  satisfies_all se_prog (se_invs1 sp mem raddr q p c Ks Lc x19 x29) (se_exits1 sp mem raddr q p c Ks Lc x19 x29) (xs'::t).
Proof.
  intros.
  assert (NOT: ∀ s0 a insn, cs_prog s0 a = Some insn -> (a =? 0x15f258) = false /\ (a =? 0x15f2a0) = false /\ (a =? 0x15f2a8) = false).
  { intros s0 a insn IL. splits.
    - destruct (N.eqb_spec a 0x15f258) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity].
    - destruct (N.eqb_spec a 0x15f2a0) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity].
    - destruct (N.eqb_spec a 0x15f2a8) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity]. }
  assert (XE: se_exits1 sp mem raddr q p c Ks Lc x19 x29 = make_exits 1 cs_prog (se_F sp mem raddr q p c Ks Lc x19 x29)).
  { extensionality tt. destruct tt as [|[[a|i] s0] t0]; try reflexivity.
    unfold se_exits1, make_exits. destruct (cs_prog s0 a) as [insn|] eqn:IL.
    - rewrite (subset_updateall2 cs_prog strsep_armv8.strsep_armv8 _ _ _ IL : se_prog s0 a = Some insn). destruct (NOT _ _ _ IL) as (E1 & E2 & E3).
      unfold se_invs. rewrite E1, E2, E3. reflexivity.
    - destruct (se_prog s0 a) eqn:IL2; [|reflexivity].
      unfold se_invs. destruct (a =? 0x15f258); [reflexivity|]. destruct (a =? 0x15f2a0); [reflexivity|]. destruct (a =? 0x15f2a8); [reflexivity|].
      destruct (se_F sp mem raddr q p c Ks Lc x19 x29 _ _ _ _ s0 a) as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 1); [|reflexivity]. subst m.
      apply cs_post_addr in F. subst a. vm_compute in IL. discriminate IL. }
  unfold se_invs1. rewrite XE.
  apply satisfies_all_transfer with (p1 := cs_prog) (I1 := make_invs 1 cs_prog (se_F sp mem raddr q p c Ks Lc x19 x29)).
  - apply subset_updateall2.
  - intros a s0 t0 _ N0. unfold make_invs. rewrite N0. reflexivity.
  - intros a s0 t0 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s0 t0 insn IL. unfold make_invs. rewrite (subset_updateall2 cs_prog strsep_armv8.strsep_armv8 _ _ _ IL : se_prog s0 a = Some insn), IL.
    destruct (NOT _ _ _ IL) as (E1 & E2 & E3). unfold se_invs. rewrite E1, E2, E3. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros xs1 t1 START. rewrite ENTRY in START.
    eapply strcspn_partial_correctness; try eassumption.
    + apply se_cs_pre; assumption.
    + apply cs_contains.
    + apply ms_contains.
Qed.

Theorem strsep_partial_correctness:
  ∀ prog s sp mem raddr q p c Ks Lc x19 x29 t xs'
    (PRE0: se_pre sp mem q p c Ks Lc)
    (P2: strsep_armv8.strsep_armv8 ⊆2 prog) (P1: strcspn_armv8.strcspn_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f258, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = q) (X1: s R_X1 = c) (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (se_invs2 sp mem raddr q p c Ks Lc x19 x29) (se_exits2 sp mem raddr q p c Ks Lc x19 x29) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  assert (PP: se_prog ⊆2 prog).
  { unfold se_prog. rewrite <- (updateall2_subset _ _ (cs_prog_mono prog P1 P0)). apply updateall2_mono. exact P2. }
  eapply satisfies_all_pmono with (p1:=se_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold se_invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X29 START PRE0 W19 W29 W30 W0.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply se_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X29).
  destruct PRE0 as (QP & PRE0).
  do 2 arm8_step.
  all: match goal with H: (_ =? 0) = _ |- _ => rewrite QP in H end.
  all: rewrite QP.
  all: nrm.
  { (* *str = NULL *)
    repeat arm8_step. splits; first [reflexivity | assumption]. }
  destruct PRE0 as [P0 | (NFp & Zp & NFc & Zc & L2 & S1 & S2 & BP & BCl & BQ)].
  { exfalso. contradiction. }
  clear BC.
  do 6 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply se_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply strcspn_correct_in_strsep with (sp:=sp) (mem:=mem) (raddr:=raddr) (q:=q) (p:=p) (c:=c) (Ks:=Ks) (Lc:=Lc) (x19:=x19) (x29:=x29).
  exact ENTRY. exact MDL2. exact NFp. exact Zp. exact NFc. exact Zc. exact L2. exact S1. exact S2. exact BP. exact BCl.
  1-7: unfold s2; simpl_stores.
  reflexivity. unfold se_frame; reflexivity. reflexivity. reflexivity. exact X1. exact X19. reflexivity.
  reflexivity.
  intros.
  clearbody s2. rename s' into s3.
  destruct_inv 64 PRE.
  destruct PRE as ((K & KK & R0 & NI & KE) & RSP & R19 & R29 & R30 & MO).
  clear MDL1 MDL2.
  rewrite (msub_small 64 sp 32) in MO by L64.
  assert (FB: ∀ a, a < 2^64 -> (a < sp - 112 \/ sp - 32 <= a) -> s3 V_MEM64 Ⓑ[a] = se_frame sp mem raddr x29 p q Ⓑ[a]).
  { intros a A O. apply MO; [exact A | L64]. }
  clear MO.
  assert (PK: s3 V_MEM64 Ⓑ[p + K] = mem Ⓑ[p + K]) by (rewrite FB by L64; apply se_CB; L64).
  assert (NI': ∀ i, i < K -> ~ cs_in mem c Lc (mem Ⓑ[p + i])).
  { intros i I C. apply (NI i I). rewrite se_CB by L64. apply se_cs_in; [L64 | L64 | L64 | exact C]. }
  assert (KE': K = Ks \/ cs_in mem c Lc (mem Ⓑ[p + K])).
  { destruct KE as [E|C]; [left; exact E | right]. rewrite se_CB in C by L64. apply (se_cs_in sp mem raddr x29 p q); [L64 | L64 | L64 | exact C]. }
  clear NI KE.
  assert (FQ: ∀ a v, sp - 32 <= a -> a + 8 <= sp -> se_frame sp mem raddr x29 p q Ⓠ[a] = v -> s3 V_MEM64 Ⓠ[a] = v).
  { intros a v A1 A2 E. rewrite <- E. apply getmem_ext. intros i I. apply FB; L64. }
  assert (P16: s3 V_MEM64 Ⓠ[sp ⊖ 16] = p).
  { rewrite (msub_small 64 sp 16) by L64. apply FQ; [L64 | L64 |]. unfold se_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64. }
  assert (P8: s3 V_MEM64 Ⓠ[sp ⊖ 8] = q).
  { rewrite (msub_small 64 sp 8) by L64. apply FQ; [L64 | L64 |]. unfold se_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64. }
  assert (Q32: s3 V_MEM64 Ⓠ[sp - 32] = x29).
  { apply FQ; [L64 | L64 |]. unfold se_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64. }
  assert (Q24: s3 V_MEM64 Ⓠ[sp - 24] = raddr).
  { apply FQ; [L64 | L64 |]. unfold se_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64. }
  assert (OUT: ∀ a, a < 2^64 -> (a < sp - 112 \/ sp <= a) -> s3 V_MEM64 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A O. rewrite FB by L64. unfold se_frame. rewrite !(msub_small 64 sp) by L64. destruct O as [O|O]; memsimp; reflexivity. }
  clear FB FQ.
  repeat arm8_step.
  all: match goal with H: (_ =? 0) = _ |- _ => rewrite P16, PK in H end.
  all: rewrite !P16, !P8.
  all: nrm.
  all: rewrite !(msub_small 64 sp) by L64.
  all: splits; [reflexivity | reflexivity | assumption | | | ].
  all: try (rewrite <- Q32; apply getmem_ext; intros i I; rewrite !read_out by L64; reflexivity).
  all: try (rewrite <- Q24; apply getmem_ext; intros i I; rewrite !read_out by L64; reflexivity).
  - assert (EK: K = Ks) by (destruct (N.lt_ge_cases K Ks) as [LT|GE]; [exfalso; apply (NFp K LT); assumption | L64]).
    exists K. splits; [L64 | exact NI' | left; split; [exact EK |]].
    intros a A O. apply set_pt; [L64 | exact A | apply OUT; assumption].
  - assert (KL: K < Ks) by (destruct (N.lt_ge_cases K Ks) as [LT|GE]; [exact LT | exfalso; assert (EK: K = Ks) by L64;
        match goal with H: ~ (_ = 0) |- _ => apply H end; rewrite EK; exact Zp]).
    exists K. splits; [L64 | exact NI' |]. right. splits; [exact KL | |].
    + destruct KE' as [E|C]; [exfalso; L64 | exact C].
    + intros a A O. replace (1 + p + K) with (p + K + 1) by L64.
      apply set_pt; [L64 | exact A |]. apply set_pt; [L64 | exact A | apply OUT; assumption].
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorem: strsep, strcspn and memset never write X20..X28, Z8..Z15. *)
Theorem strsep_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates se_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
