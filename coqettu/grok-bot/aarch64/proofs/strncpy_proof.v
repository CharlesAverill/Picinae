(* strncpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls stpncpy)

   SEMANTICS
   ---------
   musl's src/string/strncpy.c:
       char *strncpy(char *restrict d, const char *restrict s, size_t n) {
           __stpncpy(d, s, n);
           return d;
       }
   compiled with a 32-byte frame (stp x29,x30,[sp,#-32]! / str x19,[sp,#16]),
   mov x19,x0; bl __stpncpy (0x15e9c0, which calls memset 0x118400);
   mov x0,x19; restore; ret.  The whole stpncpy proof (stpncpy_proof.v) is
   reused inside strncpy_prog through lib/GrokCall.v (satisfies_all_transfer)
   rather than re-proved.

   SPECIFICATION (man 3 strncpy, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            char *strncpy(char dst[restrict .dsize], const char *restrict src,
                          size_t dsize);
     DESCRIPTION
            These functions copy non-null bytes from the string pointed to by
            src into the array pointed to by dst.  If the source has too few
            non-null bytes to fill the destination, the functions pad the
            destination with trailing null bytes.  If the destination buffer,
            limited by its size, isn't large enough to hold the copy, the
            resulting character sequence is truncated.
     RETURN VALUE
            strncpy() returns dst.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strncpy at 0x5f14c (ELF vaddr); 0x15f14c in Ghidra (image base 0x100000);
            callees stpncpy at 0x5e9c0 / 0x15e9c0 and memset at 0x18400 / 0x118400
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strncpy_armv8.v,
            ../lifted/stpncpy_armv8.v and ../lifted/memset_armv8.v (combined as
            sn_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q), X2 = dsize (n), SP = sp,
            X30 = raddr, X19 = x19, X29 = x29; memory mem.
   PRECONDITION (sn_pre sp mem d q n K), stated explicitly:
            - K = strnlen(src, n): bytes q..q+K-1 nonzero, K <= n, byte q+K
              is 0 when K < n;
            - n - K < 160 and 4096 <= d (inherited from the memset proof:
              the zero fill must avoid memset's Nop-lifted DC ZVA path);
            - 64 <= sp < 2^64; d+n+64 <= sp and q+n+64 <= sp (both buffers
              below the two stack frames of strncpy and stpncpy);
            - no overlap between d..d+n-1 and q..q+n-1.
   Output:  If execution reaches the RET (0x15f16c), with M the final memory:
            X0 = d;
            M[d+i] = mem[q+i] for i < K; M[d+i] = 0 for K <= i < n;
            M[a] = sn_inner[a] for every other address a, where sn_inner is
            mem with strncpy's saved x29/raddr/x19 at sp-32/sp-24/sp-16 and
            stpncpy's saved frame at sp-64..sp-41 (scratch below sp);
            SP = sp, X19 = x19, X29 = x29, X30 = raddr (sn_post).
            X20..X28 and Z8..Z15 are never written
            (strncpy_preserves_other_callee_saved).  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strncpy_armv8 stpncpy_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall.
From Grok.proofs Require Import memset_proof memset_full_defs stpncpy_callees stpncpy_proof.
Import ARM8Notations.
Open Scope N.

Definition sn_prog : program := updateall2 strncpy_armv8.strncpy_armv8 stp_prog.

Lemma sn_prog_contains: strncpy_armv8.strncpy_armv8 ⊆2 sn_prog.
Proof.
  intros s a insn SC. unfold sn_prog, stp_prog, updateall2, updateall, memset_armv8.memset_armv8, stpncpy_armv8.stpncpy_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma stp_contains: stpncpy_armv8.stpncpy_armv8 ⊆2 stp_prog.
Proof.
  intros s a insn SC. unfold stp_prog, updateall2, updateall, memset_armv8.memset_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem sn_prog_welltyped: welltyped_prog arm8typctx sn_prog.
Proof.
  intros s a. unfold sn_prog, updateall2, updateall.
  destruct (stp_prog s a) as [[sz q]|] eqn:T0.
    pose proof (stp_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strncpy_armv8.welltyped.
Qed.

Definition sn_pre (sp mem d q n K : N) :=
  nilfree mem q K /\ K <= n /\ (K < n -> mem Ⓑ[q + K] = 0) /\ n - K < 160 /\ 4096 <= d /\
  64 <= sp /\ sp < 2^64 /\ d + n + 64 <= sp /\ q + n + 64 <= sp /\ (q + n <= d \/ d + n <= q).

(* memory as seen by stpncpy: strncpy's frame, then stpncpy's own frame below it *)
Definition sn_inner (sp mem raddr x19 x29 d : N) :=
  stp_frame (sp ⊖ 32) (stp_frame sp mem raddr x19 x29) 0x15f160 d (sp ⊖ 32).

Definition sn_post (sp mem raddr d q n x19 x29 K : N) (s:store) :=
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ i, i < K -> s V_MEM64 Ⓑ[d + i] = mem Ⓑ[q + i]) /\
  (∀ i, K <= i -> i < n -> s V_MEM64 Ⓑ[d + i] = 0) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = sn_inner sp mem raddr x19 x29 d Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr d q n x19 x29 K : N).
  Definition sn_F := stpncpy_callees.invs (sp ⊖ 32) (stp_frame sp mem raddr x19 x29) 0x15f160 d q n d (sp ⊖ 32) K 0 0 0 0.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f14c then
      Inv 2 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15f16c then Post 2 (sn_post sp mem raddr d q n x19 x29 K s)
    (* stpncpy (family 1) and memset (family 0) invariants *)
    else sn_F T Inv Post NoInv s a.
  Definition exits2 := make_exits 2 sn_prog invs.
  Definition invs2 := make_invs 2 sn_prog invs.
  Definition exits1 := make_exits 1 sn_prog invs.
  Definition invs1 := make_invs 1 sn_prog invs.
End Invariants.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma sn_CB: ∀ sp mem raddr x19 x29 a, 64 <= sp -> sp < 2^64 -> a + 1 <= sp - 32 ->
  stp_frame sp mem raddr x19 x29 Ⓑ[a] = mem Ⓑ[a].
Proof. intros. unfold stp_frame. rewrite !(msub_small 64 sp) by L64. memsimp. reflexivity. Qed.

Lemma sn_stp_pre: ∀ sp mem raddr x19 x29 d q n K, sn_pre sp mem d q n K ->
  stp_pre (sp ⊖ 32) (stp_frame sp mem raddr x19 x29) d q n K.
Proof.
  intros sp mem raddr x19 x29 d q n K (NF & KN & KZ & SM & LOW & S64 & SPL & BD & BQ & DJ).
  unfold stp_pre. rewrite (msub_small 64 sp) by L64.
  splits; try exact DJ; try (intros i I; rewrite sn_CB by L64; apply NF, I);
    try (intro H; rewrite sn_CB by L64; apply KZ, H); L64.
Qed.

Lemma stp_post_addr: ∀ sp mem raddr d q n x19 x29 K s a,
  stpncpy_callees.invs sp mem raddr d q n x19 x29 K 0 0 0 0 (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,1) -> a = 0x15ea90.
Proof.
  intros sp mem raddr d q n x19 x29 K s a H.
  unfold stpncpy_callees.invs, memset_full_defs.mf_invs in H.
  destruct a as [|p]; [discriminate H|].
  repeat (destruct p as [p|p|]; try discriminate H); first [reflexivity | discriminate H].
Qed.

Theorem stpncpy_correct_in_strncpy:
  ∀ s t xs' (ENTRY: startof t xs' = (Addr 0x15e9c0, s)) (MDL: models arm8typctx s)
    sp mem raddr d q n x19 x29 K (PRE0: sn_pre sp mem d q n K)
    (SP: s R_SP = sp ⊖ 32) (MEM: s V_MEM64 = stp_frame sp mem raddr x19 x29) (X30: s R_X30 = 0x15f160)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n) (X19: s R_X19 = d) (X29: s R_X29 = sp ⊖ 32),
  satisfies_all sn_prog (invs1 sp mem raddr d q n x19 x29 K) (exits1 sp mem raddr d q n x19 x29 K) (xs'::t).
Proof.
  intros.
  assert (NOT: ∀ s0 a insn, stp_prog s0 a = Some insn -> (a =? 0x15f14c) = false /\ (a =? 0x15f16c) = false).
  { intros s0 a insn IL. split.
    - destruct (N.eqb_spec a 0x15f14c) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity].
    - destruct (N.eqb_spec a 0x15f16c) as [E|E]; [rewrite E in IL; vm_compute in IL; discriminate IL | reflexivity]. }
  assert (XE: exits1 sp mem raddr d q n x19 x29 K = make_exits 1 stp_prog (sn_F sp mem raddr d q n x19 x29 K)).
  { extensionality tt. destruct tt as [|[[a|i] s0] t0]; try reflexivity.
    unfold exits1, make_exits. destruct (stp_prog s0 a) as [insn|] eqn:IL.
    - rewrite (subset_updateall2 stp_prog strncpy_armv8.strncpy_armv8 _ _ _ IL : sn_prog s0 a = Some insn). destruct (NOT _ _ _ IL) as [E1 E2].
      unfold invs. rewrite E1, E2. reflexivity.
    - destruct (sn_prog s0 a) eqn:IL2; [|reflexivity].
      unfold invs. destruct (a =? 0x15f14c); [reflexivity|]. destruct (a =? 0x15f16c); [reflexivity|].
      destruct (sn_F sp mem raddr d q n x19 x29 K _ _ _ _ s0 a) as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 1); [|reflexivity]. subst m.
      apply stp_post_addr in F. subst a. vm_compute in IL. discriminate IL. }
  unfold invs1. rewrite XE.
  apply satisfies_all_transfer with (p1 := stp_prog) (I1 := make_invs 1 stp_prog (sn_F sp mem raddr d q n x19 x29 K)).
  - apply subset_updateall2.
  - intros a s0 t0 _ N0. unfold make_invs. rewrite N0. reflexivity.
  - intros a s0 t0 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s0 t0 insn IL. unfold make_invs. rewrite (subset_updateall2 stp_prog strncpy_armv8.strncpy_armv8 _ _ _ IL : sn_prog s0 a = Some insn), IL.
    destruct (NOT _ _ _ IL) as [E1 E2]. unfold invs. rewrite E1, E2. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros xs1 t1 START. rewrite ENTRY in START.
    eapply stpncpy_partial_correctness; try eassumption.
    + apply sn_stp_pre. exact PRE0.
    + apply stp_contains.
    + apply subset_updateall2.
Qed.

Theorem strncpy_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x29 K t xs'
    (PRE0: sn_pre sp mem d q n K)
    (P2: strncpy_armv8.strncpy_armv8 ⊆2 prog) (P1: stpncpy_armv8.stpncpy_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f14c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X29: s R_X29 = x29),
  satisfies_all prog (invs2 sp mem raddr d q n x19 x29 K) (exits2 sp mem raddr d q n x19 x29 K) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  assert (PP: sn_prog ⊆2 prog).
  { unfold sn_prog. rewrite <- (updateall2_subset _ _ (stp_prog_mono prog P1 P0)). apply updateall2_mono. exact P2. }
  eapply satisfies_all_pmono with (p1:=sn_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X29 START PRE0 W19 W29 W30 W0.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sn_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W29 W30 W0. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
  pose proof PRE0 as (NF & KN & KZ & SM & LOW & S64 & SPL & BD & BQ & DJ).
  do 5 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply sn_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply stpncpy_correct_in_strncpy with (sp:=sp) (mem:=mem) (raddr:=raddr) (x19:=x19) (x29:=x29);
    first [ eassumption | reflexivity | (unfold s2; simpl_stores; first [ sassumption | reflexivity ]) ].
  reflexivity.
  intros.
  assert (MDL3: models arm8typctx s') by (eapply preservation_exec_prog; try eassumption; apply sn_prog_welltyped).
  clearbody s2. rename s' into s3.
  destruct_inv 64 PRE.
  destruct PRE as (R0 & RSP & R19 & R29 & R30 & M1 & M2 & M3).
  assert (FQ: ∀ a v, sp - 32 <= a -> a + 8 <= sp -> stp_frame sp mem raddr x19 x29 Ⓠ[a] = v -> s3 V_MEM64 Ⓠ[a] = v).
  { intros a v A1 A2 E. rewrite <- E. transitivity (sn_inner sp mem raddr x19 x29 d Ⓠ[a]).
    - apply getmem_ext. intros i I. apply M3; L64.
    - unfold sn_inner, stp_frame at 1. rewrite !(msub_small 64 (sp ⊖ 32)) by (rewrite msub_small by L64; L64).
      rewrite (msub_small 64 sp) by L64. memsimp. reflexivity. }
  assert (Q16: stp_frame sp mem raddr x19 x29 Ⓠ[sp - 16] = x19) by (unfold stp_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q32: stp_frame sp mem raddr x19 x29 Ⓠ[sp - 32] = x29) by (unfold stp_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q24: stp_frame sp mem raddr x19 x29 Ⓠ[sp - 24] = raddr) by (unfold stp_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  repeat arm8_step.
  unfold sn_post. splits.
  all: rewrite ?(msub_small 64 sp) by L64.
  all: try first [ sassumption | exact M2 | exact M3 ].
  1-2: reflexivity.
  - apply FQ; first [exact Q16 | L64].
  - apply FQ; first [exact Q32 | L64].
  - apply FQ; first [exact Q24 | L64].
  - intros i I. rewrite M1 by exact I. apply sn_CB; L64.
Qed.

Theorem strncpy_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates sn_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
