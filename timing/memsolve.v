Require Import riscvTiming.
Import RISCVNotations.

Lemma noverlap_index:
  forall w a1 len1 a2 len2 index size
  (NO : ~ overlap w a1 len1 a2 len2)
  (IN : index + size <= len1),
  ~ overlap w (a1 + index) size a2 len2.
Proof.
  intros.
  remember (a1 + index) as a1'. apply noverlap_shrink with (a1:=a1) (len1:=len1).
  rewrite Heqa1'. rewrite add_msub_l.
  apply N.le_trans with (m:=index+size). rewrite <-N.add_le_mono_r. apply N.Div0.mod_le.
  assumption.
  assumption.
Qed.

Lemma noverlap_index_index:
  forall w a1 len1 a2 len2 index1 size1 index2 size2
  (NO  : ~ overlap w a1 len1 a2 len2)
  (IN1 : index1 + size1 <= len1)
  (IN2 : index2 + size2 <= len2),
  ~ overlap w (a1 + index1) size1 (a2 + index2) size2.
Proof.
  intros. apply noverlap_index with (len1:=len1).
  apply noverlap_symmetry. apply noverlap_index with (len1:=len2).
  apply noverlap_symmetry.
  all: assumption.
Qed.

Lemma Nsub_add_eq: forall x y, x < y -> y = y - x + x.
Proof.
  induction x using N.peano_ind. intros; simpl. now rewrite N.sub_0_r, N.add_0_r.
  intros. apply N.lt_succ_l in H.
  rewrite N.sub_succ_r.
  rewrite N.add_succ_r, <-N.add_succ_l.
  rewrite N.succ_pred. now apply IHx. now apply N.sub_gt.
Qed.

Lemma getmem_nbyte_distance:
  forall w e m a1 a2 n v,
  msub w a1 a2 > n ->
  msub w a2 a1 > n ->
    getmem w e n (setmem w e n m a2 v) a1 = getmem w e n m a1.
Proof.
  intros.
  apply getmem_noverlap.
  clear - H H0.
  apply sep_noverlap; try (left; lia || right; lia).
Qed.
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Lemma succ_msub_swap:
  forall w m p : N, msub w (N.succ m) p = N.succ (msub w m p) mod 2 ^ w.
Proof.
  intros. rewrite <-N.add_1_r, add_msub_swap, N.add_1_r.
  reflexivity.
Qed.

Lemma succ_mod_swap:
  forall c b, N.succ c mod b = N.succ (c mod b) mod b.
Proof.
    intros c b. assert (H:=N.eq_dec b 0).
    destruct H as [H | H]. subst. now repeat rewrite N.mod_0_r. remember H as NZ. clear HeqNZ.
    apply (N.div_mod c (b)) in H.
    remember (c / b) as q; remember (c mod b) as r.
    destruct (N.lt_trichotomy (N.succ r) (b)) as [Lt | [Eq | Gt]].
    1,2: rewrite H, <-N.add_succ_r, N.add_comm, N.mul_comm, N.Div0.mod_add; reflexivity.
    assert (Help: c mod b < b) by (apply N.mod_upper_bound; lia). rewrite <-Heqr in Help.
    lia.
Qed.

Lemma pred_mod:
  forall w q, 0 < w -> 0 < w * q -> N.pred (w * q) mod w = N.pred w.
Proof.
  intros. rewrite N.pred_sub. 
  enough (Hhelp: exists q', q = N.succ q'); try destruct Hhelp.
  rewrite H1, N.mul_succ_r, <-N.add_sub_assoc, <-N.Div0.add_mod_idemp_l.
  psimpl. rewrite N.mul_comm, N.Div0.mod_mul, N.add_0_l.
  rewrite N.mod_small. all: try lia.
  exists (N.pred q); try lia.
Qed.

Lemma sub_pred:
  forall x:N, 0 < x -> x - (N.pred x) = 1.
Proof.
  intros. destruct x; try lia.
Qed.

Lemma sub_pred_succ:
  forall x y:N, 0 < y -> x - (N.pred y) = (N.succ x) - y.
Proof.
  intros. lia.
Qed.

Lemma msub_pred_cancel:
  forall w a c, 0 < a -> 0 < c -> msub w a c = msub w (N.pred a) (N.pred c).
Proof.
  intros. assert (Eqa: 2 ^ w <> 0) by lia. remember Eqa as Eqc; clear HeqEqc.
  apply (N.div_mod a) in Eqa. apply (N.div_mod c) in Eqc.
  remember (a / 2 ^ w) as qa; remember (a mod 2 ^ w) as ra.
  remember (c / 2 ^ w) as qc; remember (c mod 2 ^ w) as rc.
  rewrite Eqa, Eqc. destruct (N.lt_trichotomy 0 ra) as [Gt | [Eq | Lt]]; [ | | lia]; cycle 1.
  (* 0 = ra *)
    subst ra. rewrite <-Eq, N.add_0_r in *. psimpl.
    destruct (N.lt_trichotomy 0 rc) as [Gtrc | [Eqrc | Ltrc]]; [ | | lia]; cycle 1.
    (* 0 = rc *)
    subst rc; rewrite <-Eqrc, N.add_0_r in *. psimpl; rewrite Eqa in H; rewrite Eqc in H0; clear - H H0.
    unfold msub. (**) rewrite (N.mul_comm _ qc) at 1. rewrite N.Div0.mod_mul, N.sub_0_r. (**)rewrite <-(N.mul_1_r (2^w)) at 2. 
    rewrite <-N.mul_add_distr_l, N.mul_comm, N.Div0.mod_mul.
    rewrite pred_mod, sub_pred_succ; try lia.
    rewrite N.add_sub_assoc, <-N.add_succ_comm, N.succ_pred; try lia.
    rewrite <-N.add_sub_assoc, N.sub_diag, N.add_0_r, N.mul_comm, N.Div0.mod_mul; try lia.
    (* 0 < rc *)
    rewrite (N.pred_sub (_ + rc)). rewrite <-N.add_sub_assoc; try lia.
    unfold msub. rewrite <-(N.Div0.add_mod_idemp_l (N.pred (2 ^ w * qa))). rewrite pred_mod; try lia.
    rewrite N.mul_comm. rewrite <-(N.Div0.add_mod_idemp_l (_ *qc)),<-(N.Div0.add_mod_idemp_l (_ *qc)). rewrite (N.mul_comm _ qc).
    rewrite N.Div0.mod_mul, N.add_0_l, N.add_0_l.
    rewrite (N.mod_small (rc - 1)); try lia. rewrite <-N.pred_sub, sub_pred_succ; try lia.
    rewrite N.add_pred_l, <-N.add_pred_r; try lia.
    rewrite N.sub_succ_l; try lia. rewrite N.pred_succ.
    rewrite (N.mod_small rc); try lia. rewrite <-N.Div0.add_mod_idemp_l, <-(N.Div0.add_mod_idemp_l (2^w)).
    rewrite N.Div0.mod_mul, N.Div0.mod_same, N.add_0_l; reflexivity.
  (* 0 < ra *)
    destruct (N.lt_trichotomy 0 rc) as [Gtrc | [Eqrc | Ltrc]]; [ | | lia]; cycle 1.
    (* 0 = rc *)
    subst rc; rewrite <-Eqrc, N.add_0_r. psimpl. unfold msub. rewrite pred_mod; try lia.
    rewrite <-N.add_pred_r; try lia. rewrite sub_pred; try lia. 
    rewrite (N.mul_comm _ qc) at 1. rewrite N.Div0.mod_mul, N.sub_0_r. rewrite N.add_comm, N.add_assoc.
    rewrite <-(N.mul_1_r (2^w)) at 1.
    rewrite <-N.mul_add_distr_l, N.mul_comm, <-(N.Div0.add_mod_idemp_l (_*2^w)), N.Div0.mod_mul, N.add_0_l.
    rewrite N.mod_small; try lia.
    rewrite <-N.add_assoc.
    rewrite <-N.Div0.add_mod_idemp_l, N.mul_comm, N.Div0.mod_mul, N.add_0_l, N.add_1_r, N.succ_pred, N.mod_small; try lia.
    (* 0 < rc *)
    rewrite <-N.add_pred_r, <-N.add_pred_r; try lia.
    unfold msub at 2. 
    (* TODO: Make this simplify automatically: 
             2 ^ w * qc + N.pred rc) mod 2 ^ w *) 
    rewrite <-(N.Div0.add_mod_idemp_l (2^w*qc)), (N.mul_comm (2^w) qc), N.Div0.mod_mul, N.add_0_l.
    rewrite (N.mod_small (N.pred rc)); try lia.
    rewrite N.add_sub_assoc, <-(N.add_assoc _ (N.pred ra)), (N.add_comm _ (2^w)),N.add_assoc ; try lia.
    rewrite <-N.add_assoc, <-N.add_sub_assoc, <-N.Div0.add_mod_idemp_l; try lia.
    rewrite N.mul_comm, N.Div0.mod_mul, N.add_0_l. unfold msub.
    rewrite <-(N.Div0.add_mod_idemp_l (qc * _)), N.Div0.mod_mul, N.add_0_l.
    rewrite <-N.add_assoc. rewrite <-(N.Div0.add_mod_idemp_l (qa * _)), N.Div0.mod_mul, N.add_0_l.
    rewrite (N.mod_small rc), N.add_sub_assoc, N.add_comm; try lia.
    rewrite sub_pred_succ; try assumption. rewrite <-N.add_succ_r, N.succ_pred; try lia.
Qed. 

Lemma msub_pred_succ:
  forall w a b, 0 < b -> (msub w a (N.pred b)) mod 2 ^ w = (N.succ (msub w a b)) mod 2 ^ w.
Proof.
    intros w a b H; clear - H. generalize dependent a. generalize dependent b. induction b using N.peano_ind.
    lia. 
    intros. rewrite N.pred_succ.
    destruct (N.lt_trichotomy 0 a) as [Gt | [Eq | Lt]]; try lia.
    About succ_msub_swap.
     rewrite <-(succ_msub_swap w).
      rewrite (msub_pred_cancel w (N.succ a)), N.pred_succ, N.pred_succ; try lia. now rewrite msub_mod_pow2, N.min_id.
      subst a.
      rewrite <-succ_msub_swap, (msub_pred_cancel w (N.succ 0)), N.pred_succ, N.pred_succ; try lia.
      now rewrite msub_mod_pow2, N.min_id.
Qed.

Theorem msub_le_distr:
  forall w x y z
    (Le: z <= y),
    ((msub w x y) + z) mod 2 ^ w = (msub w x (y - z)) mod 2 ^ w.
Proof.
  intros w x y z; generalize dependent x; generalize dependent y; induction z using N.peano_ind; intros.
  - now rewrite N.sub_0_r, N.add_0_r.
  - rewrite N.add_succ_r.
    rewrite N.sub_succ_r.
    rewrite (msub_pred_succ w); try lia. 
    rewrite (succ_mod_swap (msub w x (y - z))), succ_mod_swap. rewrite <-IHz. reflexivity. lia.
Qed.

Theorem noverlap_mod_idemp_l:
  forall w a1 len1 a2 len2,
    ~ overlap w (a1 mod 2 ^ w) len1 a2 len2 <->
    ~ overlap w  a1            len1 a2 len2.
Proof.
  intros. unfold overlap.
  split; intro H; intro H'. destruct H' as [i [j [LTi [LTj EQ]]]]. rewrite <-(N.Div0.add_mod_idemp_l a1) in EQ.
  apply H; exists i, j; repeat split; assumption.
  destruct H' as [i [j [LTi [LTj EQ]]]]. rewrite N.Div0.add_mod_idemp_l in EQ.
  apply H; exists i, j; repeat split; assumption.
Qed.

Theorem noverlap_reindex_msub:
  forall w a1 len1 a2 len2 x y, y <= x -> 
          ~ overlap w ( msub w a1 (x  - y)) len1 a2 len2 <->
          ~ overlap w ((msub w a1  x) + y ) len1 a2 len2.
Proof.
  intros.
  rewrite <-overlap_mod_l with (a1:=msub w a1 (x - y)). 
  rewrite <-msub_le_distr; try assumption.
  rewrite  noverlap_mod_idemp_l. reflexivity.
Qed.

Ltac clear_independent_hypotheses x y :=
    repeat match goal with
    | H : _ |- _ =>
        (* Check if the type of H contains the variable x *)
        tryif (match type of H with
                | context[x] => fail 1 (* if x is present, do not clear *)
                | context[y] => fail 1
                | _ => idtac (* if x is absent, proceed to clear *)
                end)
        then clear H
        else fail
    end.

Ltac _noverlap_prepare uxSchedulerSuspended pxCurrentTCB gp_sp_noverlap
        __global_size vTaskSwitchContext_stack_frame_size gp sp := 
    try (unfold uxSchedulerSuspended in *;
    (* clear_independent_hypotheses gp sp; *)
    unfold pxCurrentTCB in *;
    unfold gp_sp_noverlap in *; unfold __global_size, vTaskSwitchContext_stack_frame_size in *);
    (* rewrite nasty large additions as their more human readable modular subtractions *)
    repeat match goal with
    | [ |- context[?M [Ⓓ ?X + ?B + ?N := ?V]] ] =>
      rewrite <-(setmem_mod_l _ _ _ M (X+B+N) V);
      replace (M [ⒹX+B⊕N := V]) with
        (M [Ⓓ(msub 32 B (2^32 - X)) ⊕ N := V]) by
        (unfold msub; now psimpl);
      simpl (2^32 - X)
    | [ |- context[?M [Ⓓ?X + ?Y := ?V]]] =>
      rewrite <- setmem_mod_l with (a := X + Y);
      replace (X⊕Y) with (msub 32 Y (2^32 - X)) by (now rewrite N.add_comm);
      simpl (2^32 - X)
    | [ |- context[?M Ⓓ[ ?X + ?B + ?N]] ] =>
      rewrite <-(getmem_mod_l _ _ _ M (X+B+N));
      replace (M Ⓓ[X+B⊕N]) with
        (M Ⓓ[(msub 32 B (2^32 - X)) ⊕ N]) by
        (unfold msub; now psimpl);
      simpl (2^32 - X)
    | [ |- context[?M Ⓓ[?X + ?Y]]] =>
      rewrite <- getmem_mod_l with (a := X + Y);
      replace (X⊕Y) with (msub 32 Y (2^32 - X)) by (now rewrite N.add_comm);
      simpl (2^32 - X)
  end;
  repeat match goal with
    (* 48 is a special case *)
    | [|- context[?N ⊖ 4294967248]] =>
      replace (N ⊖ 4294967248) with (48 ⊕ N) by
        (unfold msub; now psimpl);
      (rewrite getmem_mod_l with (a := 48 + N) ||
        rewrite setmem_mod_l with (a := 48 + N))
  end.

Ltac memsolve mem gp sp:=
    (* split up all the memory read-write dependencies with getmem_noverlap *)
    repeat rewrite getmem_noverlap; try now (unfold msub; psimpl);
    try (
      (* goals involving noverlap of gp and gp *)
      apply noverlap_mod_idemp_l, sep_noverlap; left; psimpl; lia);
    try solve [apply noverlap_shrink with (gp ⊖ 2048) 2048; [
                psimpl; lia |
                (apply noverlap_symmetry; apply noverlap_shrink with (sp ⊖ 16) 16;
                    [psimpl; lia | now apply noverlap_symmetry])
    ]];
    try assumption;
    match goal with
    | [ |- ~ overlap _ (?P ⊖ ?X1) ?N (?P ⊖ ?X2) ?N] =>
        solve [apply sep_noverlap; (left; now psimpl) || (right; now psimpl)]
    | [ H : ~ overlap _ (?A1 ⊖ ?A1B) ?A1S  (?A2 ⊖ ?A2B) ?A2S
        |-  ~ overlap _ (?A1 ⊖ ?A1I) ?A1S' (?A2 ⊖ ?A2I) ?A2S'] =>
        solve [change A1I with (A1B - (A1B - A1I));
        change A2I with (A2B - (A2B - A2I));
        rewrite noverlap_reindex_msub; (lia || apply noverlap_symmetry); rewrite noverlap_reindex_msub; (lia || apply noverlap_symmetry); try lia;
        apply (noverlap_index_index 32 (A1 ⊖ A1B) A1B (A2 ⊖ A2B) A2B (A1B-A1I) A1S' (A2B-A2I) A2S');
        lia || assumption
        ]
    | [ |- ~ overlap _ (48 +  mem Ⓓ[ gp ⊖ ?GPI]) 4 (sp ⊖ ?SPI) 4] =>
        rewrite N.add_comm; change SPI with (16 - (16 - SPI));
        idtac; apply noverlap_symmetry; rewrite noverlap_reindex_msub; try lia; apply noverlap_symmetry;
        apply (noverlap_index_index _ (mem Ⓓ[ gp ⊖ 1896 ]) 52 (sp ⊖ 16) 16 48 4 (16-SPI) 4);
        lia || assumption
    | _ => idtac
    end.
