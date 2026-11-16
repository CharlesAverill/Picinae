(* strncat -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strlen)

   SEMANTICS
   ---------
   musl's src/string/strncat.c:
       char *strncat(char *restrict d, const char *restrict s, size_t n) {
           char *a = d;
           d += strlen(d);
           while (n && *s) n--, *d++ = *s++;
           *d++ = 0;
           return a;
       }
   compiled as a 48-byte frame (stp x29,x30,[sp,#-48]! / str x21 / stp x19,x20),
   bl strlen (0x15efa8, re-proved here inside strncat_prog), an inline byte
   loop (0x15f0e0..0x15f0f4, bounded by X2 = d+strlen(d)+n), strb wzr, and the
   frame restore.

   SPECIFICATION (man 3 strncat, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <string.h>
            char *strncat(char *restrict dst, const char src[restrict .ssize],
                          size_t ssize);
     DESCRIPTION
            This function catenates the input character sequence contained in
            a null-padded fixed-width buffer, into a string at the buffer
            pointed to by dst.  The programmer is responsible for allocating a
            destination buffer large enough, that is,
            strlen(dst) + strnlen(src, ssize) + 1.
     RETURN VALUE
            strncat() returns dst.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strncat at 0x5f0b4 (ELF vaddr); 0x15f0b4 in Ghidra (image base 0x100000);
            callee strlen at 0x5efa8 / 0x15efa8
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strncat_armv8.v and
            ../lifted/strlen_armv8.v (combined as strncat_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q), X2 = n, SP = sp, X30 = raddr,
            X19/X20/X21/X29 = x19/x20/x21/x29; memory mem.
   PRECONDITION (strncat_pre sp mem d q n Ld K), stated explicitly:
            - d holds a string of length Ld: bytes d..d+Ld-1 nonzero, byte d+Ld = 0;
            - bytes q..q+K-1 are nonzero, K <= n < 2^64, and either K = n or
              byte q+K = 0 (so K = min(n, strnlen(q, n)), the number of bytes copied);
            - 48 <= sp < 2^64 and both d..d+Ld+K and q..q+K lie strictly below
              sp-48, i.e. below strncat's own stack frame (sp-48..sp);
            - the written range d+Ld..d+Ld+K does not overlap the read range
              q..q+K (q+K < d+Ld or d+Ld+K < q).
            Justification: the C standard makes copying between overlapping
            objects undefined behaviour (restrict), and a destination that
            overlaps strncat's own stack frame is not caller-owned memory, so
            the precondition only excludes undefined behaviour.  It is needed
            because strncat reloads X30 and X19-X21 from its frame after the copy.
   Output:  If execution reaches the RET (0x15f10c), with
            C = mem with x29, raddr, x21, x19, x20 stored at sp-48, sp-40,
            sp-16, sp-32, sp-24 (the saved frame):
            memory = (bcp C (d+Ld) q K) with byte d+Ld+K set to 0
            (bytes q[0..K-1] copied in order to d+Ld.., then the terminator;
            see lib/GrokStr.v), X0 = d, SP = sp, X19 = x19, X20 = x20,
            X21 = x21, X29 = x29, X30 = raddr.  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strncat_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
Import ARM8Notations.
Open Scope N.

Definition strncat_prog : program := updateall2 strncat_armv8.strncat_armv8 strlen_armv8.strlen_armv8.

Theorem strncat_prog_welltyped: welltyped_prog arm8typctx strncat_prog.
Proof.
  intros s a. unfold strncat_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strncat_armv8.welltyped.
Qed.

Lemma strncat_prog_mono: ∀ prog, strncat_armv8.strncat_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> strncat_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold strncat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* the caller's memory after strncat's prologue (stp x29,x30,[sp,#-48]!; str x21,[sp,#32]; stp x19,x20,[sp,#16]) *)
Definition ncat_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20].

(* precondition: d is a string of length Ld; q has K nonzero bytes, and either K = n or q[K] = 0
   (so K = min(n, strnlen(q))); all bytes touched lie below the frame at sp-48; the written range
   [d+Ld, d+Ld+K] does not overlap the read range [q, q+K] (overlap is undefined behaviour in C). *)
Definition strncat_pre (sp mem d q n Ld K : N) :=
  nilfree mem d Ld /\ mem Ⓑ[d + Ld] = 0 /\ K <= n /\ n < 2^64 /\ nilfree mem q K /\ (K = n \/ mem Ⓑ[q + K] = 0) /\
  48 <= sp /\ sp < 2^64 /\ d + Ld + K + 1 <= sp - 48 /\ q + K + 1 <= sp - 48 /\
  (q + K < d + Ld \/ d + Ld + K < q).

Definition strncat_post (sp mem raddr d q x19 x20 x21 x29 Ld K : N) (s:store) :=
  s V_MEM64 = setmem 64 LittleE 1 (bcp (ncat_frame sp mem raddr x19 x20 x21 x29) (d + Ld) q (N.to_nat K)) (d + Ld + K) 0 /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x20 x21 x29 Ld K : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strncat *)
    | 0x15f0b4 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    | 0x15f0e4 => Inv 1 (∃ k, k <= K /\ s R_X0 = d + Ld + k /\ s R_X2 = (d + Ld + n) mod 2^64 /\ s R_X19 = q + k /\
                         s R_X20 = n /\ s R_X21 = d /\
                         s V_MEM64 = bcp (ncat_frame sp mem raddr x19 x20 x21 x29) (d + Ld) q (N.to_nat k) /\
                         s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15f10c => Post 1 (strncat_post sp mem raddr d q x19 x20 x21 x29 Ld K s)
    (* strlen (string at d) *)
    | 0x15efa8 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem d k /\ mem Ⓑ[d + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strncat_prog invs.
  Definition invs0 := make_invs 0 strncat_prog invs.
  Definition exits1 := make_exits 1 strncat_prog invs.
  Definition invs1 := make_invs 1 strncat_prog invs.
End Invariants.

Theorem strlen_correct_in_strncat:
  ∀ prog s t xs'
    (P: strncat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ q n Ld K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  set (x29 := s R_X29). set (x19 := s R_X19). set (x20 := s R_X20). set (x21 := s R_X21).
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  assert (X20: s R_X20 = x20) by reflexivity. assert (X21: s R_X21 = x21) by reflexivity.
  clearbody sp mem raddr p x29 x19 x20 x21.
  eapply satisfies_all_pmono with (p1:=strncat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 X20 X21 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + exists ((k+8) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
      pose proof (haszero_test_zero _ (qword_lt64 mem (p+k)) BC (i-k) ltac:(lia)) as H8.
      rewrite byte_of_qword in H8 by lia. replace (p + k + (i - k)) with (p + i) in H8 by lia.
      exact H8.
    + exists k. repeat split; assumption.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
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

Theorem strncat_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x20 x21 x29 Ld K t xs'
    (PRE0: strncat_pre sp mem d q n Ld K)
    (P1: strncat_armv8.strncat_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f0b4, s))
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
  assert (PP: strncat_prog ⊆2 prog) by (apply strncat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strncat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X21 X29 START PRE0 W19 W20 W21 W29 W30.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W29 W30. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    do 8 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply strncat_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply strlen_correct_in_strncat with (q:=q) (n:=n) (Ld:=Ld) (K:=K); first [ exact (fun _ _ _ H => H) | eassumption ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply strncat_prog_welltyped.
    clearbody s2.
    clear - PRE MDL' PRE0 W19 W20 W21 W29 W30.
    rename MDL' into MDL. rename s' into s0.
    destruct_inv 64 PRE.
    destruct PRE as (L & LLT & R0 & NF & ZL & MEM & SP & X30 & X29 & X19 & X20 & X21).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 1 <= sp - 48 -> C Ⓑ[a] = mem Ⓑ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> bcp C (d+Ld) q (N.to_nat i) Ⓑ[q+i] = mem Ⓑ[q+i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply bcp_read_below; rewrite ?N2Nat.id; L64.
      - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 1 (bcp C (d+Ld) q (N.to_nat j)) (d+Ld+j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    rewrite !(MS sp) in * by lia.
    change (mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20]) with C in *.
    assert (LE: Ld = L).
    { apply (first_zero_unique (fun i => mem Ⓑ[d+i]) (fun i => C Ⓑ[d+i])); cbv beta; try assumption.
      intros i I. apply CB. lia. }
    subst L.
    repeat arm8_step.
    exists 0. splits; try reflexivity; try lia.
    all: first [ (rewrite N.add_0_r; first [assumption | apply N.mod_small; L64]) | (rewrite MEM; reflexivity) | assumption ].
  - destruct PRE as (k & KK & X0 & X2 & X19 & X20 & X21 & MEM & SP & X29).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 1 <= sp - 48 -> C Ⓑ[a] = mem Ⓑ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> bcp C (d+Ld) q (N.to_nat i) Ⓑ[q+i] = mem Ⓑ[q+i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply bcp_read_below; rewrite ?N2Nat.id; L64.
      - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 1 (bcp C (d+Ld) q (N.to_nat j)) (d+Ld+j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    repeat grok_step.
    + (* k = n *)
      apply N.eqb_eq in BC. rewrite N.mod_small in BC by lia. assert (EK: k = K) by lia. clear BC. subst k.
      try unfold strncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
    + (* copy one more byte *)
      apply N.eqb_neq in BC. rewrite N.mod_small in BC by lia.
      apply cbnz32_true in BC0; [|apply byte_lt32]. rewrite RD in BC0 by lia.
      assert (KLT: k < K).
      { destruct (N.eq_dec k K) as [->|NE]; [|lia]. destruct ZK as [ZK|ZK]; [lia|contradiction]. }
      exists (k+1). splits; try reflexivity; try lia.
      all: first [ (rewrite N.mod_small by L64; lia) | (rewrite bcp_succ; reflexivity) ].
    + (* NUL found *)
      apply cbnz32_false in BC0; [|apply byte_lt32]. rewrite RD in BC0 by lia.
      assert (k = K).
      { destruct (N.lt_ge_cases k K) as [H|H]; [|lia]. exfalso. exact (NFq k H BC0). }
      subst k.
      try unfold strncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
Qed.
