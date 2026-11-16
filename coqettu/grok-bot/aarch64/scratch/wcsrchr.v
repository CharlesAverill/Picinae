From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsrchr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.proofs Require Import wcslen_proof.
From Grok.proofs Require wcschr_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsrchr_prog : program := updateall2 wcsrchr_armv8.wcsrchr_armv8 wcslen_armv8.wcslen_armv8.

Lemma wcsrchr_prog_contains: wcsrchr_armv8.wcsrchr_armv8 ⊆2 wcsrchr_prog.
Proof.
  intros s a insn SC. unfold wcsrchr_prog, updateall2, updateall, wcslen_armv8.wcslen_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem wcsrchr_prog_welltyped: welltyped_prog arm8typctx wcsrchr_prog.
Proof.
  intros s a. unfold wcsrchr_prog, updateall2, updateall.
  destruct (wcslen_armv8.wcslen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (wcslen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply wcsrchr_armv8.welltyped.
Qed.

(* No wide character at index j, i < j <= L, equals c. *)
Definition rscan (m:memory) (p c i L:N) := ∀ j, i < j -> j <= L -> m Ⓓ[p + 4*j] ≠ c.
(* No wide character at index j <= L equals c. *)
Definition allscan (m:memory) (p c L:N) := ∀ j, j <= L -> m Ⓓ[p + 4*j] ≠ c.

(* L is the wcslen of the string at p in m, and p + 4L does not wrap. *)
Definition wlen (m:memory) (p L:N) :=
  L < 2^62 /\ wcs_nilfree m p L /\ m Ⓓ[p + 4*L] = 0 /\ p + 4*L < 2^64.

Definition wcsrchr_spec (m:memory) (p c r:N) :=
  ∃ L, wlen m p L /\
    ((∃ i, i <= L /\ r = p + 4*i /\ m Ⓓ[p + 4*i] = c /\ rscan m p c i L) \/
     (r = 0 /\ allscan m p c L)).

Section Invariants.
  Variables (sp mem raddr p c x29 x19 x20 : N).
  Definition c32 := c mod 2^32.
  (* wcsrchr's 32-byte frame: saved X29, X30, X19, X20. *)
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19] [Ⓠ sp ⊖ 8 := x20].
  (* precondition: s is not near address 0 and the string does not wrap *)
  Definition wpre := 4 <= p /\ ∀ k, wcs_nilfree frame_mem p k -> p + 4*k < 2^64.
  Definition fbounds := sp < 2^64 /\ raddr < 2^64 /\ x29 < 2^64 /\ x19 < 2^64 /\ x20 < 2^64.
  Definition wcsrchr_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\
    s V_MEM64 = frame_mem /\ wcsrchr_spec frame_mem p c32 (s R_X0).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsrchr (s = p, c = c) *)
    | 0x15fe20 => Inv 1 (wpre /\ s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20)
    | 0x15fe44 => Inv 1 (∃ L, wpre /\ fbounds /\ wlen frame_mem p L /\
                         ((∃ i, i <= L /\ s R_X0 = p + 4*i /\ rscan frame_mem p c32 i L) \/
                          (s R_X0 = p - 4 /\ allscan frame_mem p c32 L)) /\
                         s R_X19 = p /\ s R_X20 = c32 /\ s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 32)
    | 0x15fe68 => Post 1 (wcsrchr_post s)
    (* wcslen (s = p), called with the caller's p in X19 and c32 in X20 *)
    | 0x15fc18 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = p /\ s R_X20 = c32)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = p /\ s R_X1 = p ⊕ 4*k /\
                         wcs_nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = p /\ s R_X20 = c32)
    | 0x15fc34 => Post 0 (wcslen_post sp mem raddr p s /\ s R_X19 = p /\ s R_X20 = c32)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsrchr_prog invs.
  Definition invs0 := make_invs 0 wcsrchr_prog invs.
  Definition exits1 := make_exits 1 wcsrchr_prog invs.
  Definition invs1 := make_invs 1 wcsrchr_prog invs.
End Invariants.

Theorem wcslen_correct_in_wcsrchr:
  ∀ prog s t xs'
    (P1: wcsrchr_armv8.wcsrchr_armv8 ⊆2 prog) (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s),
  ∀ c x29 x19 x20 (X19: s R_X19 = s R_X0) (X20: s R_X20 = c mod 2^32),
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29 x19 x20)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29 x19 x20)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  clearbody sp mem raddr p.
  eapply satisfies_all_pmono with (p1:=wcsrchr_prog).
    unfold wcsrchr_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X19 X20 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. unfold c32. rewrite X0 in X19. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsrchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30 & X19 & X20).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X19 & X20).
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
      split; [|split; assumption].
      exists k. repeat split; assumption.
Qed.

Theorem wcsrchr_partial_correctness:
  ∀ prog s sp mem raddr p c x29 x19 x20 t xs'
    (P1: wcsrchr_armv8.wcsrchr_armv8 ⊆2 prog) (P0: wcslen_armv8.wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fe20, s))
    (MDL: models arm8typctx s)
    (PRE: wpre sp mem raddr p x29 x19 x20)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29) (X19: s R_X19 = x19) (X20: s R_X20 = x20),
  satisfies_all prog (invs1 sp mem raddr p c x29 x19 x20) (exits1 sp mem raddr p c x29 x19 x20) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcsrchr_prog).
    unfold wcsrchr_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL PRE SP MEM X30 X0 X1 X29 X19 X20 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. refine (conj PRE _). repeat split; assumption.
  clear PRE. intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsrchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry: save frame, call wcslen *)
    destruct PRE as (WP & X0 & X1 & MEM & SP & X30 & X29 & X19 & X20).
    pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
    pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
    pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
    pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
    pose proof (MDL1 R_X19 64 eq_refl) as X1964. rewrite X19 in X1964. simpl in X1964.
    pose proof (MDL1 R_X20 64 eq_refl) as X2064. rewrite X20 in X2064. simpl in X2064.
    do 6 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply wcsrchr_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply wcslen_correct_in_wcsrchr with (c:=c) (x29:=x29) (x19:=x19) (x20:=x20);
      first [ exact wcsrchr_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply wcsrchr_prog_welltyped.
    set (t' := t2++t0++_::t) in *. clearbody s2 t'.
    clear - PRE MDL' SP64 P64 C64 R64 X2964 X1964 X2064 WP.
    rename MDL' into MDL. rename s' into s.
    destruct_inv 64 PRE.
    destruct PRE as ((k & KLT & R0 & NF & Z & MEM & SP & X30) & X19 & X20).
    repeat arm8_step.
    pose proof WP as (P4 & NW). pose proof (NW k NF) as KW.
    exists k. splits; try assumption; try reflexivity.
    + unfold fbounds. splits; assumption.
    + unfold wlen. splits; assumption.
    + left. exists k. splits.
      * reflexivity.
      * rewrite <- add_mod_r, wcschr_proof.ashiftr2_shl2 by (lia || (rewrite N.mul_comm; apply N.Div0.mod_mul)).
        apply N.mod_small. exact KW.
      * intros j J1 J2. lia.
  - destruct PRE as (L & WP & FB & WL & XC & X19 & X20 & MEM & SP).
    pose proof FB as (SP64 & R64 & X2964 & X1964 & X2064).
    pose proof WP as (P4 & NW). pose proof WL as (LLT & NF & ZL & LW).
    destruct XC as [(i & IL & X0 & RS) | (X0 & AS)].
    + (* X0 = p + 4i *)
      unfold frame_mem in MEM. repeat arm8_step.
      all: try (apply N.leb_gt in BC; exfalso; lia).
      all: unfold c32 in *; rewrite N.mod_mod in BC0 by discriminate.
      * (* match: return p + 4i *)
        apply N.eqb_eq in BC0.
        splits; try (apply N.mod_small; assumption); try reflexivity.
        exists L. split. exact WL. left. exists i. splits; try assumption; reflexivity.
      * (* no match: step down *)
        apply N.eqb_neq in BC0.
        exists L. splits; try assumption; try reflexivity.
        destruct (N.eq_dec i 0) as [I0|I1].
        -- right. subst i. split.
           rewrite N.mul_0_r, N.add_0_r. apply msub_small; lia.
           intros j J. destruct (N.eq_dec j 0) as [J0|J0].
           ++ subst j. exact BC0.
           ++ apply RS; lia.
        -- left. exists (i-1). splits.
           ++ lia.
           ++ rewrite msub_small by lia. lia.
           ++ intros j J1 J2. destruct (N.eq_dec j i) as [JI|JI].
              ** subst j. exact BC0.
              ** apply RS; lia.
    + (* X0 = p - 4: return NULL *)
      unfold frame_mem in MEM. repeat arm8_step.
      all: try (apply N.leb_le in BC; exfalso; lia).
      splits; try (apply N.mod_small; assumption); try reflexivity.
      exists L. split. exact WL. right. split. reflexivity. exact AS.
Qed.

(* Frame: the AAPCS64 callee-saved registers X21..X28, Z8..Z15 are never
   written by wcsrchr or wcslen (X19, X20, X29, X30 are restored; see post). *)
Theorem wcsrchr_preserves_other_callee_saved:
  ∀ r, In r (R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wcsrchr_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
