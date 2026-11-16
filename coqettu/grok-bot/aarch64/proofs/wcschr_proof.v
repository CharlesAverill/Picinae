(* wcschr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcslen)

   SEMANTICS
   ---------
   musl's src/string/wcschr.c:
       if (!c) return s + wcslen(s);
       for (; *s && *s != c; s++);
       return *s ? s : 0;
   (casts to wchar_t pointer omitted here).  The binary tests the
   low 32 bits of c (cbnz w1).  If they are 0 it saves X29/X30 and s in a
   32-byte frame below SP, calls wcslen (0x15fc18, verified in the same file
   against the same invariant family, as callee id 0) and returns
   s + (len << 2).  Otherwise it scans 4-byte wide characters until one is
   0 (returns NULL) or equals c (returns its address).
   This file verifies the composition wcschr + wcslen (program
   wcschr_prog = both lifts) with Picinae's perform_call.

   SPECIFICATION (man 3 wcschr, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcschr(const wchar_t *wcs, wchar_t wc);

     DESCRIPTION
            The wcschr() function is the wide-character equivalent of the
            strchr(3) function.  It searches the first occurrence of wc in the
            wide-character string pointed to by wcs.

     RETURN VALUE
            The wcschr() function returns a pointer to the first occurrence of
            wc in the wide-character string pointed to by wcs, or NULL if wc
            does not occur in the string.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcschr at 0x5fab4 (ELF vaddr); 0x15fab4 in Ghidra (image base 0x100000)
            wcslen at 0x5fc18 (ELF vaddr); 0x15fc18 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcschr_armv8.v and
            ../lifted/wcslen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = p, X1 = c (wchar_t; only the low 32 bits matter, c32 =
            c mod 2^32); SP = sp; X30 = return address raddr; X29 = x29;
            m = memory on entry.
   Output:  If execution reaches any RET (0x15fad8, 0x15faf4, 0x15fafc):
            SP = sp, X30 = raddr, X29 = x29, and (wcschr_post) either
              - c32 <> 0, memory = m, and wcschr_spec m p c32 X0; or
              - c32 = 0, memory = frame_mem (m with x29, raddr, p stored at
                sp-32, sp-24, sp-8), and wcschr_spec frame_mem p 0 X0.
            wcschr_spec m p c r: either there is k < 2^62 such that wide chars
            0..k-1 are neither 0 nor c, wide char k equals c and r = p + 4k
            (mod 2^64); or there is such a k with wide char k = 0, c <> 0 and
            r = 0 (NULL).  (When the scan wraps all the way around the address
            space k restarts at 0, so k is the index since the last wrap.)
            X19..X28 and Z8..Z15 are never written
            (wcschr_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.proofs Require Import wcslen_proof.
Import ARM8Notations.
Open Scope N.

Definition wcschr_prog : program := updateall2 wcschr_armv8.wcschr_armv8 wcslen_armv8.wcslen_armv8.

Lemma wcschr_prog_contains: wcschr_armv8.wcschr_armv8 ⊆2 wcschr_prog.
Proof.
  intros s a insn SC. unfold wcschr_prog, updateall2, updateall, wcslen_armv8.wcslen_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem wcschr_prog_welltyped: welltyped_prog arm8typctx wcschr_prog.
Proof.
  intros s a. unfold wcschr_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply wcschr_armv8.welltyped.
Qed.
Lemma ashiftr2_shl2: ∀ x, x < 2^64 -> x mod 4 = 0 -> ((ashiftr 64 x 2) << 2) mod 2^64 = x.
Proof.
  intros x X M. unfold ashiftr, sbop1. set (z := toZ 64 x).
  assert (E: ofZ 64 z = x) by (unfold z; rewrite ofZ_toZ_bitcast by reflexivity; apply N.mod_small; exact X).
  unfold ofZ in *. rewrite N.shiftl_mul_pow2.
  apply N2Z.inj. rewrite N2Z.inj_mod, N2Z.inj_mul, Z2N.id by (apply Z.mod_pos_bound; lia).
  rewrite <- E. rewrite Z2N.id by (apply Z.mod_pos_bound; lia).
  change (Z.of_N (2^64)) with (2^64)%Z. change (Z.of_N (2^2)) with 4%Z.
  change (2^Z.of_N 64)%Z with (2^64)%Z. change (Z.of_N 2) with 2%Z.
  rewrite Z.shiftr_div_pow2 by lia. change (2^2)%Z with 4%Z.
  rewrite Z.mul_mod_idemp_l by lia.
  assert (Z4: (z mod 4 = 0)%Z).
  { apply (f_equal Z.of_N) in E. rewrite Z2N.id in E by (apply Z.mod_pos_bound; lia).
    assert (MZ: (Z.of_N x mod 4 = 0)%Z) by (change 4%Z with (Z.of_N 4); rewrite <- N2Z.inj_mod, M; reflexivity).
    apply (f_equal (fun a => a mod 4)%Z) in E. rewrite MZ in E.
    rewrite <- (Z.mod_mod_divide z (2^64) 4) by (exists (2^62)%Z; reflexivity). lia. }
  f_equal. rewrite Z.mul_comm. symmetry. apply Z.div_exact. lia. exact Z4.
Qed.

(* The first k wide characters at p are neither 0 nor c. *)
Definition wscan (m:memory) (p:addr) (c:N) (k:N) :=
  ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ 0 /\ m Ⓓ[p + 4*i] ≠ c.

Lemma wscan_0: ∀ m p c, wscan m p c 0.
Proof. intros m p c i H. destruct i; discriminate. Qed.

Lemma wscan_succ: ∀ m p c k, wscan m p c k -> m Ⓓ[p + 4*k] ≠ 0 -> m Ⓓ[p + 4*k] ≠ c ->
  wscan m p c (k+1).
Proof.
  intros m p c k W N0 NC i I. destruct (N.lt_ge_cases i k). apply W; assumption.
  replace i with k by lia. split; assumption.
Qed.

Lemma wscan_nilfree: ∀ m p k, wcs_nilfree m p k -> wscan m p 0 k.
Proof. intros m p k NF i I. split; apply NF; exact I. Qed.

(* wcschr result for wide character c (already reduced to 32 bits). *)
Definition wcschr_spec (m:memory) (p c r:N) :=
  (∃ k, k < 2^62 /\ wscan m p c k /\ m Ⓓ[p + 4*k] = c /\ r = p ⊕ 4*k) \/
  (∃ k, k < 2^62 /\ wscan m p c k /\ m Ⓓ[p + 4*k] = 0 /\ c ≠ 0 /\ r = 0).

Section Invariants.
  Variables (sp mem raddr p c x29 : N).
  (* wcschr's 32-byte frame (c = 0 path only): saved X29, X30 and s. *)
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 8 := p].
  Definition wcschr_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
    ((s V_MEM64 = mem /\ c mod 2^32 ≠ 0 /\ wcschr_spec mem p (c mod 2^32) (s R_X0)) \/
     (s V_MEM64 = frame_mem /\ c mod 2^32 = 0 /\ wcschr_spec frame_mem p 0 (s R_X0))).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcschr (s = p, c = c) *)
    | 0x15fab4 => Inv 1 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X29 = x29)
    | 0x15fae0 => Inv 1 (∃ k, k < 2^62 /\ s R_X2 = p ⊕ 4*k /\ s R_X1 = c /\ c mod 2^32 ≠ 0 /\
                         wscan mem p (c mod 2^32) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x15fad8 => Post 1 (wcschr_post s)
    | 0x15faf4 => Post 1 (wcschr_post s)
    | 0x15fafc => Post 1 (wcschr_post s)
    (* wcslen (s = p) *)
    | 0x15fc18 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = p /\ s R_X1 = p ⊕ 4*k /\
                         wcs_nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fc34 => Post 0 (wcslen_post sp mem raddr p s)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcschr_prog invs.
  Definition invs0 := make_invs 0 wcschr_prog invs.
  Definition exits1 := make_exits 1 wcschr_prog invs.
  Definition invs1 := make_invs 1 wcschr_prog invs.
End Invariants.

Theorem wcslen_correct_in_wcschr:
  ∀ prog s t xs'
    (P1: wcschr_armv8.wcschr_armv8 ⊆2 prog) (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s),
  ∀ c x29,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  clearbody sp mem raddr p.
  eapply satisfies_all_pmono with (p1:=wcschr_prog).
    unfold wcschr_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcschr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
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
      exists k. repeat split; assumption.
Qed.

Theorem wcschr_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P1: wcschr_armv8.wcschr_armv8 ⊆2 prog) (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fab4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p c x29) (exits1 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcschr_prog).
    unfold wcschr_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcschr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
    pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
    pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
    pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
    arm8_step. arm8_step; rewrite N.shiftr_0_r in BC.
    + (* c mod 2^32 <> 0: enter the scan loop with k = 0 *)
      apply Bool.negb_true_iff, N.eqb_neq in BC.
      exists 0. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact P64.
      splits; first [ reflexivity | assumption | apply wscan_0 | lia ].
    + (* c mod 2^32 = 0: call wcslen *)
      apply Bool.negb_false_iff, N.eqb_eq in BC.
      do 4 arm8_step.
      set (s2 := update _ _ _).
      eapply models_after_steps. eassumption. apply wcschr_prog_welltyped. intro MDL2.
      eapply (perform_call 0). reflexivity.
      intros. eapply wcslen_correct_in_wcschr with (c:=c) (x29:=x29);
        first [ exact wcschr_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
      reflexivity.
      intros.
      unfold s2 in PRE. psimpl in PRE.
      assert (MDL': models arm8typctx s').
        eapply preservation_exec_prog; try eassumption. apply wcschr_prog_welltyped.
      set (t' := t2++t0++_::t) in *. clearbody s2 t'.
      clear - PRE MDL' SP64 P64 R64 X2964 BC.
      rename MDL' into MDL. rename s' into s.
      destruct_inv 64 PRE.
      destruct PRE as (k & KLT & R0 & NF & Z & MEM & SP & X30).
      repeat arm8_step.
      splits; try (apply N.mod_small; assumption).
      right. splits. reflexivity. exact BC.
      left. exists k. splits. exact KLT. apply wscan_nilfree; exact NF. exact Z.
      rewrite <- add_mod_r, ashiftr2_shl2. reflexivity. lia.
      rewrite N.mul_comm. apply N.Div0.mod_mul.
  - (* loop *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & WS & MEM & SP & X30 & X29).
    repeat arm8_step.
    + (* terminator: return NULL *)
      apply N.eqb_eq in BC. splits; try assumption. left. splits. reflexivity. exact CNZ.
      right. exists k. splits; try assumption. reflexivity.
    + (* match: return the pointer *)
      apply N.eqb_eq in BC0. splits; try assumption. left. splits. reflexivity. exact CNZ.
      left. exists k. splits; try assumption. reflexivity.
    + (* advance (wrapping k to 0 after a full lap of the address space) *)
      apply N.eqb_neq in BC, BC0.
      destruct (N.lt_ge_cases (k+1) (2^62)) as [LT|GE].
      * exists (k+1). splits; try assumption; try reflexivity.
        f_equal. lia.
        apply wscan_succ; assumption.
      * exists 0. splits; try assumption; try reflexivity.
        assert (E: 4 + p + 4*k = p + 2^64) by lia. rewrite E, add_wrap_full. f_equal; lia.
        apply wscan_0.
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X29/X30 are never
   written by wcschr or wcslen. *)
Theorem wcschr_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcschr_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
