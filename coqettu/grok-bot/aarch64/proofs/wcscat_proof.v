(* wcscat -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcslen, wcscpy)

   SEMANTICS
   ---------
   musl's src/string/wcscat.c:
       wchar_t *wcscat(wchar_t *restrict dest, const wchar_t *restrict src) {
           wcscpy(dest + wcslen(dest), src);
           return dest;
       }
   compiled as a 48-byte frame (stp x29,x30 / str x19 / str x1 at sp+0x28),
   bl wcslen (0x15fc18) on dest, src reloaded from the frame,
   add x0,x19,x0,LSL #2, bl wcscpy (0x15fb2c), mov x0,x19 and the frame
   restore.  Both callees are re-proved inside the combined wcscat_prog.

   SPECIFICATION (man 3 wcscat, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcscat(wchar_t *restrict dest,
                            const wchar_t *restrict src);
     DESCRIPTION
            The wcscat() function is the wide-character equivalent of the
            strcat(3) function.  It copies the wide-character string pointed
            to by src, including the terminating null wide character (L'\0'),
            to the end of the wide-character string pointed to by dest.
            The strings may not overlap.
            The programmer must ensure that there is room for at least
            wcslen(dest)+wcslen(src)+1 wide characters at dest.
     RETURN VALUE
            wcscat() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcscat at 0x5fa80 (ELF vaddr); 0x15fa80 in Ghidra (image base 0x100000);
            callees wcslen 0x5fc18 / 0x15fc18, wcscpy 0x5fb2c / 0x15fb2c
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcscat_armv8.v,
            ../lifted/wcslen_armv8.v, ../lifted/wcscpy_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest (d), X1 = src (q), SP = sp, X29/X19 = x29/x19,
            X30 = return address raddr; memory mem.
   Output:  If execution reaches the RET (0x15fab0), with F = mem with x29,
            raddr, x19, q stored at sp-48, sp-40, sp-32, sp-8 (the frame) and
            e = d + 4L mod 2^64, there are L and k such that L < 2^62, the
            first L words at d in F are nonzero and the word at d+4L is 0
            (wcslen of dest), wnz F e q k and the source word read at q+4k is
            0 (wcscpy copied k+1 words to e), memory = wcpy F e q (k+1)
            (wcscpy_proof.v), X0 = d and SP = sp.  X29, X30, X19 are the
            8-byte values read back from sp-48, sp-40, sp-32 of the final
            memory (equal to the entry values when the copy does not overwrite
            the frame).  X20-X28 and Z8-Z15 are never written
            (wcscat_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcscat_armv8 wcscpy_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.proofs Require wcscpy_proof wcslen_proof wcschr_proof.
Import ARM8Notations.
Open Scope N.

Notation wcpy := wcscpy_proof.wcpy.
Notation wnz := wcscpy_proof.wnz.
Notation wcs_nilfree := wcslen_proof.wcs_nilfree.

Definition wcscat_prog : program :=
  updateall2 (updateall2 wcscat_armv8.wcscat_armv8 wcscpy_armv8.wcscpy_armv8) wcslen_armv8.wcslen_armv8.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma wcscat_prog_contains2: wcscat_armv8.wcscat_armv8 ⊆2 wcscat_prog.
Proof.
  intros s a insn SC. unfold wcscat_prog, updateall2, updateall, wcslen_armv8.wcslen_armv8, wcscpy_armv8.wcscpy_armv8.
  contains_tac SC.
Qed.

Lemma wcscat_prog_contains1: wcscpy_armv8.wcscpy_armv8 ⊆2 wcscat_prog.
Proof.
  intros s a insn SC. unfold wcscat_prog, updateall2, updateall, wcslen_armv8.wcslen_armv8.
  contains_tac SC.
Qed.

Lemma wcscat_prog_contains0: wcslen_armv8.wcslen_armv8 ⊆2 wcscat_prog.
Proof. apply subset_updateall2. Qed.

Theorem wcscat_prog_welltyped: welltyped_prog arm8typctx wcscat_prog.
Proof.
  intros s a. unfold wcscat_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
  destruct (wcscpy_armv8.wcscpy_armv8 s a) as [[sz q]|] eqn:TN.
    pose proof (wcscpy_armv8.welltyped s a) as WT. rewrite TN in WT. exact WT.
    apply wcscat_armv8.welltyped.
Qed.

Lemma wcscat_prog_mono: ∀ prog, wcscat_armv8.wcscat_armv8 ⊆2 prog -> wcscpy_armv8.wcscpy_armv8 ⊆2 prog ->
  wcslen_armv8.wcslen_armv8 ⊆2 prog -> wcscat_prog ⊆2 prog.
Proof.
  intros prog P2 P1 P0. unfold wcscat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P1). apply updateall2_mono. exact P2.
Qed.

Section Invariants.
  Variables (sp mem raddr d q x29 x19 : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 32 := x19] [Ⓠ sp ⊖ 8 := q].
  Definition wcscat_post (s:store) :=
    ∃ L k, L < 2^62 /\ wcs_nilfree frame_mem d L /\ frame_mem Ⓓ[d + 4*L] = 0 /\
         wnz frame_mem (d ⊕ 4*L) q k /\ wcpy frame_mem (d ⊕ 4*L) q (N.to_nat k) Ⓓ[q + 4*k] = 0 /\
         s V_MEM64 = wcpy frame_mem (d ⊕ 4*L) q (N.to_nat (k+1)) /\ s R_X0 = d /\ s R_SP = sp /\
         s R_X29 = wcpy frame_mem (d ⊕ 4*L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 48] /\
         s R_X30 = wcpy frame_mem (d ⊕ 4*L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 40] /\
         s R_X19 = wcpy frame_mem (d ⊕ 4*L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 32].
  Definition XS (s:store) := s R_X29 = x29 /\ s R_X19 = x19.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcscat *)
    | 0x15fa80 => Inv 2 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fab0 => Post 2 (wcscat_post s)
    (* wcscpy callee *)
    | 0x15fb2c => Inv 1 (s R_X0 = d /\ s R_X1 = q /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fb30 => Inv 1 (∃ k, s R_X2 = (4*k) mod 2^64 /\ s R_X0 = d /\ s R_X1 = q /\ wnz mem d q k /\
                         s V_MEM64 = wcpy mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fb40 => Post 1 (∃ k, wnz mem d q k /\ wcpy mem d q (N.to_nat k) Ⓓ[q + 4*k] = 0 /\
                          s V_MEM64 = wcpy mem d q (N.to_nat (k+1)) /\
                          s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    (* wcslen callee (string at d) *)
    | 0x15fc18 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = d /\ s R_X1 = d ⊕ 4*k /\
                         wcs_nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc34 => Post 0 (wcslen_proof.wcslen_post sp mem raddr d s /\ XS s)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcscat_prog invs.
  Definition invs0 := make_invs 0 wcscat_prog invs.
  Definition exits1 := make_exits 1 wcscat_prog invs.
  Definition invs1 := make_invs 1 wcscat_prog invs.
  Definition exits2 := make_exits 2 wcscat_prog invs.
  Definition invs2 := make_invs 2 wcscat_prog invs.
End Invariants.

Theorem wcslen_correct_in_wcscat:
  ∀ prog s t xs'
    (P: wcscat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s),
  ∀ q,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19))
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p x29 x19.
  eapply satisfies_all_pmono with (p1:=wcscat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
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
      split; [|repeat split; assumption].
      exists k. repeat split; assumption.
Qed.

Theorem wcscpy_correct_in_wcscat:
  ∀ prog s t xs'
    (P: wcscat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fb2c, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
    (exits1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (d := s R_X0).
  set (q := s R_X1). set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = d) by reflexivity.
  assert (X1: s R_X1 = q) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr d q x29 x19.
  eapply satisfies_all_pmono with (p1:=wcscat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    exists 0. repeat split; try assumption. unfold wnz, wcscpy_proof.wnz. intros. lia.
  - destruct PRE as (k & X2 & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 4 (wcpy mem d q (N.to_nat k)) (q + 4*k)) as B;
         change (2^(4*8)) with (2^32) in B;
         destruct (wcscpy_proof.test32 _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split.
      all: first
        [ assumption
        | apply wcscpy_proof.wnz_succ; assumption
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcscpy_proof.wcpy]; rewrite ?N2Nat.id; reflexivity
        | f_equal; lia ].
    + exists k. repeat split.
      all: first
        [ assumption
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcscpy_proof.wcpy]; rewrite ?N2Nat.id; reflexivity ].
Qed.

Theorem wcscat_partial_correctness:
  ∀ prog s sp mem raddr d q x29 x19 t xs'
    (P2: wcscat_armv8.wcscat_armv8 ⊆2 prog) (P1: wcscpy_armv8.wcscpy_armv8 ⊆2 prog)
    (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fa80, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs2 sp mem raddr d q x29 x19) (exits2 sp mem raddr d q x29 x19) (xs'::t).
Proof.
  intros.
  assert (PP: wcscat_prog ⊆2 prog) by (apply wcscat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=wcscat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  pose proof (MDL1 R_X1 64 eq_refl) as Q64. rewrite X1 in Q64. simpl in Q64.
  do 6 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply wcscat_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply wcslen_correct_in_wcscat with (q := q); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply wcscat_prog_welltyped.
  clearbody s2.
  clear - PRE MDL' SP64 D64 Q64 X0.
  rename MDL' into MDL. rename s' into s0.
  destruct_inv 64 PRE.
  destruct PRE as ((L & LLT & R0 & NF & ZL & MEM & SP & X30) & X29 & X19).
  rename SP into SP1. rename MEM into MEM1.
  do 4 arm8_step.
  assert (E: (d + (ashiftr 64 (4*L) 2 << 2)) mod 2^64 = (d + 4*L) mod 2^64).
  { rewrite <- (N.Div0.add_mod_idemp_r d ((ashiftr 64 (4*L) 2) << 2)), wcschr_proof.ashiftr2_shl2.
    reflexivity. lia. rewrite N.mul_comm. apply N.Div0.mod_mul. }
  rewrite (N.mod_small q) by exact Q64.
  set (s3 := update _ _ _).
  eapply models_after_steps. eassumption. apply wcscat_prog_welltyped. intro MDL3.
  eapply (perform_call 1). reflexivity.
  intros. eapply wcscpy_correct_in_wcscat; first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s3 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply wcscat_prog_welltyped.
  clearbody s3.
  clear - PRE MDL' SP64 D64 Q64 NF ZL LLT E SP1 MEM1.
  rename MDL' into MDL0. rename s' into s4.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X30 & X29 & X19).
  rewrite ?E in *.
  repeat arm8_step.
  exists L, k. psimpl. splits; try assumption; try reflexivity.
  apply N.mod_small. exact SP64.
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X19/X29/X30 are
   never written by wcscat, wcslen or wcscpy. *)
Theorem wcscat_preserves_other_callee_saved:
  ∀ r, In r (R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcscat_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
