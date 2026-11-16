From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsncat_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcscpy_proof wcslen_proof.
From Grok.proofs Require wcschr_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsncat_prog : program := updateall2 wcsncat_armv8.wcsncat_armv8 wcslen_armv8.wcslen_armv8.

Theorem wcsncat_prog_welltyped: welltyped_prog arm8typctx wcsncat_prog.
Proof.
  intros s a. unfold wcsncat_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcsncat_armv8.welltyped.
Qed.

Lemma wcsncat_prog_mono: ∀ prog, wcsncat_armv8.wcsncat_armv8 ⊆2 prog -> wcslen_armv8.wcslen_armv8 ⊆2 prog -> wcsncat_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold wcsncat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* reads disjoint from the 4-byte copy writes of wcpy are unaffected *)
Lemma wcpy_read_above: ∀ m e q k len a, e + 4 * N.of_nat k <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (wcpy m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H0 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [wcpy]. rewrite getmem_setmem_below by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Lemma wcpy_read_below: ∀ m e q k len a, a + len <= e -> e + 4 * N.of_nat k <= 2^64 ->
  getmem 64 LittleE len (wcpy m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [wcpy]. rewrite getmem_setmem_above by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Definition ncat_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20].

Definition wcsncat_pre (sp mem d q n Ld K : N) :=
  wcs_nilfree mem d Ld /\ mem Ⓓ[d + 4*Ld] = 0 /\ K <= n /\ n < 2^64 /\ wcs_nilfree mem q K /\
  (K = n \/ mem Ⓓ[q + 4*K] = 0) /\
  48 <= sp /\ sp < 2^64 /\ d + 4*Ld + 4*K + 4 <= sp - 48 /\ q + 4*K + 4 <= sp - 48 /\
  (q + 4*K + 4 <= d + 4*Ld \/ d + 4*Ld + 4*K + 4 <= q).

Definition wcsncat_post (sp mem raddr d q x19 x20 x21 x29 Ld K : N) (s:store) :=
  s V_MEM64 = setmem 64 LittleE 4 (wcpy (ncat_frame sp mem raddr x19 x20 x21 x29) (d + 4*Ld) q (N.to_nat K)) (d + 4*Ld + 4*K) 0 /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x20 x21 x29 Ld K : N).
  Definition XS (s:store) := s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsncat *)
    | 0x15fcdc => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fd08 => Inv 1 (∃ k, k <= K /\ s R_X0 = d + 4*Ld + 4*k /\ s R_X19 = n - k /\ s R_X20 = q + 4*k /\ s R_X21 = d /\
                         s V_MEM64 = wcpy (ncat_frame sp mem raddr x19 x20 x21 x29) (d + 4*Ld) q (N.to_nat k) /\
                         s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15fd30 => Post 1 (wcsncat_post sp mem raddr d q x19 x20 x21 x29 Ld K s)
    (* wcslen callee (string at d) *)
    | 0x15fc18 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = d /\ s R_X1 = d ⊕ 4*k /\
                         wcs_nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ XS s)
    | 0x15fc34 => Post 0 (wcslen_proof.wcslen_post sp mem raddr d s /\ XS s)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsncat_prog invs.
  Definition invs0 := make_invs 0 wcsncat_prog invs.
  Definition exits1 := make_exits 1 wcsncat_prog invs.
  Definition invs1 := make_invs 1 wcsncat_prog invs.
End Invariants.

Theorem wcslen_correct_in_wcsncat:
  ∀ prog s t xs'
    (P: wcsncat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s),
  ∀ q n Ld K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (x29 := s R_X29). set (x19 := s R_X19). set (x20 := s R_X20). set (x21 := s R_X21).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  assert (X20: s R_X20 = x20) by reflexivity. assert (X21: s R_X21 = x21) by reflexivity.
  clearbody sp mem raddr p x29 x19 x20 x21.
  eapply satisfies_all_pmono with (p1:=wcsncat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 X20 X21 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
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
