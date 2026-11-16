From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsnlen_armv8 wmemchr_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Definition wcsnlen_prog : program := updateall2 wcsnlen_armv8.wcsnlen_armv8 wmemchr_armv8.wmemchr_armv8.

Lemma wcsnlen_prog_contains: wcsnlen_armv8.wcsnlen_armv8 ⊆2 wcsnlen_prog.
Proof.
  intros s a insn SC. unfold wcsnlen_prog, updateall2, updateall, wmemchr_armv8.wmemchr_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem wcsnlen_prog_welltyped: welltyped_prog arm8typctx wcsnlen_prog.
Proof.
  intros s a. unfold wcsnlen_prog, updateall2, updateall.
  destruct (wmemchr_armv8.wmemchr_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (wmemchr_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply wcsnlen_armv8.welltyped.
Qed.

(* No wide character among the first k at p equals c. *)
Definition wnomatch (m:memory) (p:addr) (c:N) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ c.

Lemma wnomatch_0: ∀ m p c, wnomatch m p c 0.
Proof. unfold wnomatch. intros. lia. Qed.

Lemma wnomatch_succ: ∀ m p c k, wnomatch m p c k -> m Ⓓ[p + 4*k] ≠ c -> wnomatch m p c (k+1).
Proof.
  unfold wnomatch. intros m p c k NM B i I.
  destruct (N.lt_ge_cases i k). apply NM; assumption. replace i with k by lia. exact B.
Qed.

Lemma msub_add_cancel64: ∀ a x, a < 2^64 -> msub 64 ((a + x) mod 2^64) a = x mod 2^64.
Proof.
  intros a x A. unfold msub. rewrite (N.mod_small a) by exact A.
  rewrite N.Div0.add_mod_idemp_l.
  replace (a + x + (2^64 - a)) with (x + 1 * 2^64) by lia.
  apply N.Div0.mod_add.
Qed.

Section Invariants.
  Variables (sp mem raddr a1 a2 a3 x19 x20 x29 : N).
  (* Memory as seen by wmemchr and on return: wcsnlen's 32-byte frame (saved X29, X30,
     X19, X20) is stored just below the caller's SP. *)
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19] [Ⓠ sp ⊖ 8 := x20].
  Definition wcsnlen_post (m:memory) (s:N) (n:N) (r:N) :=
    (r = n /\ wnomatch m s 0 n) \/
    (∃ k, k < n /\ wnomatch m s 0 k /\ m Ⓓ[s + 4*k] = 0 /\
          (r = ashiftr 64 ((4*k) mod 2^64) 2 \/ (s ⊕ 4*k = 0 /\ r = n))).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsnlen *)
    | 0x15fdb4 => Inv 1 (s R_X0 = a1 /\ s R_X1 = a2 /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15fdec => Post 1 (s V_MEM64 = frame_mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29 /\
                         wcsnlen_post frame_mem a1 a2 (s R_X0))
    (* wmemchr (p = a1, c = a2, n = a3) *)
    | 0x1601d0 => Inv 0 (s R_X0 = a1 /\ s R_X1 = a2 /\ s R_X2 = a3 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x1601d8 => Inv 0 (∃ k, a3 < 2^64 /\ k <= a3 /\ s R_X0 = a1 ⊕ 4*k /\ s R_X2 = a3 - k /\ s R_X1 = a2 /\
                         wnomatch mem a1 (a2 mod 2^32) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x1601f4 => Post 0 (((∃ k, k < a3 /\ s R_X0 = a1 ⊕ 4*k /\ wnomatch mem a1 (a2 mod 2^32) k /\
                                 mem Ⓓ[a1 + 4*k] = a2 mod 2^32) \/
                           (s R_X0 = 0 /\ wnomatch mem a1 (a2 mod 2^32) a3)) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsnlen_prog invs.
  Definition invs0 := make_invs 0 wcsnlen_prog invs.
  Definition exits1 := make_exits 1 wcsnlen_prog invs.
  Definition invs1 := make_invs 1 wcsnlen_prog invs.
End Invariants.

Theorem wmemchr_correct_in_wcsnlen:
  ∀ prog s t xs'
    (P1: wcsnlen_armv8.wcsnlen_armv8 ⊆2 prog) (P0: wmemchr_armv8.wmemchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1601d0, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X20) (s R_X29))
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X20) (s R_X29))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (c := s R_X1). set (n := s R_X2). set (x19 := s R_X19). set (x20 := s R_X20). set (x29 := s R_X29).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X1: s R_X1 = c) by reflexivity. assert (X2: s R_X2 = n) by reflexivity.
  assert (X19: s R_X19 = x19) by reflexivity. assert (X20: s R_X20 = x20) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity.
  clearbody sp mem raddr p c n x19 x20 x29.
  eapply satisfies_all_pmono with (p1:=wcsnlen_prog).
    unfold wcsnlen_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsnlen_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X29).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X2 in N64. simpl in P64, N64.
    repeat arm8_step.
    exists 0. rewrite N.mul_0_r, N.add_0_r, N.sub_0_r, N.mod_small by assumption.
    splits; try assumption; try lia. apply wnomatch_0.
  - destruct PRE as (k & N64 & KLE & X0 & X2 & X1 & NM & MEM & SP & X30 & X19 & X20 & X29).
    repeat arm8_step.
    + apply N.eqb_eq in BC. split; [|splits; (reflexivity || assumption)].
      right. split. reflexivity. replace n with k by lia. exact NM.
    + apply N.eqb_eq in BC0. apply N.eqb_neq in BC. split; [|splits; (reflexivity || assumption)].
      left. exists k. splits; try assumption; try exact BC0; try reflexivity; lia.
    + apply N.eqb_neq in BC0, BC. exists (k+1).
      splits; try assumption; try reflexivity; try lia.
      all: first [ (f_equal; lia) | (rewrite msub_small by lia; lia) | (apply wnomatch_succ; assumption) ].
Qed.

Theorem wcsnlen_correct:
  ∀ prog s sp mem raddr a1 a2 x19 x20 x29 t xs'
    (P1: wcsnlen_armv8.wcsnlen_armv8 ⊆2 prog) (P0: wmemchr_armv8.wmemchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fdb4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a1) (X1: s R_X1 = a2)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr a1 a2 0 x19 x20 x29)
                     (exits1 sp mem raddr a1 a2 0 x19 x20 x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcsnlen_prog).
    unfold wcsnlen_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsnlen_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X20 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X1 64 eq_refl) as A264. rewrite X1 in A264. simpl in A264.
  pose proof (MDL1 R_X0 64 eq_refl) as A164. rewrite X0 in A164. simpl in A164.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X19 64 eq_refl) as X1964. rewrite X19 in X1964. simpl in X1964.
  pose proof (MDL1 R_X20 64 eq_refl) as X2064. rewrite X20 in X2064. simpl in X2064.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 8 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply wcsnlen_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply wmemchr_correct_in_wcsnlen;
    first [ exact wcsnlen_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply wcsnlen_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 A264 A164 R64 X1964 X2064 X2964.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (RES & MEM & SP & X30 & X19 & X20 & X29).
  change (0 mod 2^32) with 0 in RES.
  repeat arm8_step; (splits; [reflexivity|apply N.mod_small; assumption ..|]); unfold wcsnlen_post, frame_mem.
  - (* wmemchr returned NULL: result n *)
    apply N.eqb_eq in BC. destruct RES as [(k & K & R0 & NM & Z) | (R0 & NM)].
    + right. exists k. splits; try assumption. right. split. rewrite <- R0. exact BC. reflexivity.
    + left. split. reflexivity. exact NM.
  - (* wmemchr returned a non-NULL pointer *)
    apply N.eqb_neq in BC. destruct RES as [(k & K & R0 & NM & Z) | (R0 & NM)].
    + right. exists k. splits; try assumption. left. rewrite R0, msub_add_cancel64 by assumption. reflexivity.
    + contradiction.
Qed.

(* For any realistic length (k < 2^61 wide characters) the returned value is k. *)
Theorem wcsnlen_result_small:
  ∀ k, k < 2^61 -> ashiftr 64 ((4*k) mod 2^64) 2 = k.
Proof.
  intros k LT. rewrite N.mod_small by lia. rewrite ashiftr64_small by lia.
  rewrite N.shiftr_div_pow2. change (2^2) with 4. rewrite N.mul_comm, N.div_mul by discriminate.
  reflexivity.
Qed.
