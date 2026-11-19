(* Signed 32-bit division routine from ld-musl-armhf.so.1 (musl 1.2.6-r6).
   Entry 0x3046e; inputs R0 and R1 are two's-complement words, R1 nonzero.
   The four return sites provide R0 = signed_quotient R0 R1 and preserve
   memory, SP, LR, and R4.  The proof stops before each BX LR. *)

From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  FUN_0003046e_armv7 armv7_common division_program signed_div_spec signed_div_stages
  signed_div_entry signed_div_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition signed_div_entry_addr : addr := 0x3046e.

Ltac arm7_step_rewrite H :=
  eapply NIStep; [reflexivity|reflexivity|];
  intros c2 s2 x2 XS2; step_stmt XS2;
  abstract_ignored_vars XS2; psimpl_hyp XS2;
  simpl_memaccs XS2; destruct_memaccs XS2; try generalize_trace;
  repeat lazymatch type of XS2 with
  | reset_temps _ s2 = _ /\ x2 = _ =>
      try clear c2; destruct XS2 as [XS2 ?]; subst x2;
      try (let rt := fresh in set (rt := reset_temps _ _) at 1;
        psimpl_hyp rt; subst rt; rewrite XS2; clear XS2; try clear s2)
  | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
      try rewrite H in XS2; ISA_step_and_simplify XS2
  | exec_stmt _ _ (Seq (if ?c then _ else _) _) _ _ _ =>
      try rewrite H in XS2; ISA_step_and_simplify XS2
  | _ => ISA_step_and_simplify XS2
  end;
  try rewrite exitof_none; try rewrite exitof_some;
  try lazymatch goal with |- context [Addr (?a+?sz)] => simpl (a+sz) end;
  try ISA_invhere.

Ltac arm7_step_rewrite2 H1 H2 :=
  eapply NIStep; [reflexivity|reflexivity|];
  intros c2 s2 x2 XS2; step_stmt XS2;
  abstract_ignored_vars XS2; psimpl_hyp XS2;
  simpl_memaccs XS2; destruct_memaccs XS2; try generalize_trace;
  repeat lazymatch type of XS2 with
  | reset_temps _ s2 = _ /\ x2 = _ =>
      try clear c2; destruct XS2 as [XS2 ?]; subst x2;
      try (let rt := fresh in set (rt := reset_temps _ _) at 1;
        psimpl_hyp rt; subst rt; rewrite XS2; clear XS2; try clear s2)
  | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
      try rewrite H1, H2 in XS2; ISA_step_and_simplify XS2
  | exec_stmt _ _ (Seq (if ?c then _ else _) _) _ _ _ =>
      try rewrite H1, H2 in XS2; ISA_step_and_simplify XS2
  | _ => ISA_step_and_simplify XS2
  end;
  try rewrite exitof_none; try rewrite exitof_some;
  try lazymatch goal with |- context [Addr (?a+?sz)] => simpl (a+sz) end;
  try ISA_invhere.

Theorem signed_div_correct :
  forall prog (EXT : division_program ⊆2 prog) ps t xs
    (ENTRY : startof t xs = (Addr signed_div_entry_addr, ps))
    (MDL : models arm7typctx ps)
    (NONZERO : ps R_R1 <> 0)
    (NF : ps R_NF = ps R_R1 >> 31),
  satisfies_all prog
    (make_invs 1 division_program (signed_div_family ps ps))
    (make_exits 1 division_program (signed_div_family ps ps)) (xs :: t).
Proof.
  intros prog EXT ps t xs ENTRY MDL NONZERO NF.
  eapply satisfies_all_pmono with (p1 := division_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold make_invs, signed_div_family.
    rewrite NOCODE. reflexivity.
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    pose proof (MDL R_R0 32 eq_refl) as PA32.
    pose proof (MDL R_R1 32 eq_refl) as PB32.
    clear - ps MDL NONZERO NF PA32 PB32 START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. arm7_step. reflexivity.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply division_program_welltyped.
      intro MDL1.
      pose proof (magnitude_bound (ps R_R0) PA32) as MA.
      pose proof (magnitude_bound (ps R_R1) PB32) as MB.
      pose proof (magnitude_nonzero (ps R_R1) NONZERO PB32) as MB0.
      clear - ps PA32 PB32 MA MB MB0 NF PRE MDL1.
      destruct_inv 32 PRE.
      all: try contradiction.

      * simpl in PRE.
        pose proof (sign_bound (ps R_R1) PB32) as PB1.
        assert (BS : ps R_R1 >> 31 = 0 \/ ps R_R1 >> 31 = 1) by lia.
        destruct BS as [BS|BS].
        all: rewrite <- PRE in *; do 2 arm7_step.
        all: eapply NIStep; [reflexivity|reflexivity|].
        all: intros c2 s2 x2 XS2; step_stmt XS2.
        all: rewrite BS in XS2.
        all: abstract_ignored_vars XS2; psimpl_hyp XS2.
        all: simpl_memaccs XS2; destruct_memaccs XS2; try generalize_trace.
        all: repeat ISA_step_and_simplify XS2.
        all: destruct XS2 as [XS2 X2]; subst x2.
        all: try (let rt := fresh in set (rt := reset_temps _ _) at 1;
          psimpl_hyp rt; subst rt; rewrite XS2; clear XS2; try clear s2).
        all: try rewrite exitof_none; try rewrite exitof_some.
        all: arm7_step.
        all: unfold signed_div_setup, signed_div_frame, magnitude, neg32.
        all: rewrite BS; elimstore; repeat split; psimpl; try reflexivity.
        all: rewrite neg32_eq1 by assumption.
        all: destruct (N.eq_dec vR_R1 4294967295) as [E|E].
        all: try (subst vR_R1; reflexivity).
        all: rewrite (proj2 (N.eqb_neq _ _) E),
          (proj2 (N.eqb_neq _ _) (not_eq_sym E)); reflexivity.

      * unfold signed_div_setup, signed_div_frame in PRE.
        destruct PRE as (R0 & R1 & R2 & R12 & ZF & MEM & SP & LR & R4F).
        destruct (N.eq_dec (magnitude (ps R_R1)) 1) as [B1|B1].
        -- assert (Z1 : (magnitude (ps R_R1) ⊖ 1 =? 0) = true).
           { replace 0 with (1-1) by lia. rewrite msub_eqb_spec by lia. rewrite N.mod_small by exact MB. apply N.eqb_eq. exact B1. }
           rewrite Z1 in ZF. cbn in ZF.
           assert (TEQNF : slt 32 (N.lxor (N.lxor (ps R_R0) (ps R_R1)) (ps R_R0)) 0 =
             (ps R_R1 >> 31 =? 1)).
           { rewrite quotient_xor_cancel. apply slt32_sign. exact PB32. }
           arm7_step_rewrite ZF. do 2 arm7_step.
           pose proof (sign_bound (ps R_R1) PB32) as SB.
           assert (BSV : ps R_R1 >> 31 = 0 \/ ps R_R1 >> 31 = 1) by lia.
           destruct BSV as [BSV|BSV].
           all: rewrite TEQNF, BSV in |- *; arm7_step.
           all: unfold signed_div_post, signed_div_frame.
           all: split.
           all: match goal with
             |- context [signed_quotient] =>
               rewrite signed_quotient_div1_original by assumption;
               unfold apply_sign, neg32; rewrite BSV; reflexivity
             | _ => repeat split; try assumption; try reflexivity
           end.
        -- assert (Z1 : (magnitude (ps R_R1) ⊖ 1 =? 0) = false).
           { replace 0 with (1-1) by lia. rewrite msub_eqb_spec by lia. rewrite N.mod_small by exact MB. apply N.eqb_neq. exact B1. }
           rewrite Z1 in ZF. cbn in ZF.
           assert (NFN : slt 32 (ps R_R0) 0 = (ps R_R0 >> 31 =? 1)).
           { apply slt32_sign. exact PA32. }
           arm7_step_rewrite ZF. do 2 arm7_step.
           pose proof (sign_bound (ps R_R0) PA32) as SA.
           assert (ASV : ps R_R0 >> 31 = 0 \/ ps R_R0 >> 31 = 1) by lia.
           destruct ASV as [ASV|ASV].
           all: rewrite NFN, ASV in |- *; arm7_step.
           all: arm7_step.
           all: unfold signed_div_compare, signed_div_frame, magnitude, neg32.
           all: rewrite ASV; elimstore; repeat split; psimpl; try assumption;
             try rewrite (N.mod_small (ps R_R0) (2^32) PA32); reflexivity.

      * unfold signed_div_compare, signed_div_frame in PRE.
        destruct PRE as (R0 & R1 & R2 & R3 & R12 & CF & ZF & MEM & SP & LR & R4F).
        destruct (N.lt_trichotomy (magnitude (ps R_R0)) (magnitude (ps R_R1)))
          as [LT|[EQ|GT]].
        -- assert (CFB : (magnitude (ps R_R1) <=? magnitude (ps R_R0)) = false)
             by (apply N.leb_gt; exact LT).
           assert (ZFB : (magnitude (ps R_R0) =? magnitude (ps R_R1)) = false)
             by (apply N.eqb_neq; lia).
           rewrite CFB in CF; rewrite ZFB in ZF; cbn in CF, ZF.
           arm7_step_rewrite2 CF ZF. arm7_step. arm7_step_rewrite CF.
           arm7_step. arm7_step_rewrite ZF. arm7_step_rewrite ZF.
           unfold signed_div_post, signed_div_frame.
           elimstore; repeat split; psimpl; try assumption.
           symmetry. apply signed_quotient_small. exact LT.
        -- assert (CFB : (magnitude (ps R_R1) <=? magnitude (ps R_R0)) = true)
             by (apply N.leb_le; lia).
           assert (ZFB : (magnitude (ps R_R0) =? magnitude (ps R_R1)) = true)
             by (apply N.eqb_eq; exact EQ).
           rewrite CFB in CF; rewrite ZFB in ZF; cbn in CF, ZF.
           arm7_step_rewrite2 CF ZF. arm7_step. arm7_step_rewrite CF.
           arm7_step. arm7_step_rewrite ZF. arm7_step_rewrite ZF.
           unfold signed_div_post, signed_div_frame.
           elimstore; repeat split; psimpl; try assumption.
           rewrite signed_quotient_same by assumption.
           unfold quotient_sign. apply signmask_or_one.
           apply lxor_bound; assumption.
        -- assert (CFB : (magnitude (ps R_R1) <=? magnitude (ps R_R0)) = true)
             by (apply N.leb_le; lia).
           assert (ZFB : (magnitude (ps R_R0) =? magnitude (ps R_R1)) = false)
             by (apply N.eqb_neq; lia).
           rewrite CFB in CF; rewrite ZFB in ZF; cbn in CF, ZF.
           assert (PRED : magnitude (ps R_R1) ⊖ 1 = magnitude (ps R_R1) - 1).
           { rewrite msub_sub by lia. apply N.mod_small. lia. }
           assert (LAND : N.land (s1 R_R1) (s1 R_R2) =
             N.land (magnitude (ps R_R1)) (magnitude (ps R_R1) ⊖ 1))
             by (rewrite R1, R2; reflexivity).
           arm7_step_rewrite2 CF ZF. arm7_step.
           destruct (N.land (magnitude (ps R_R1))
                       (magnitude (ps R_R1) ⊖ 1) =? 0) eqn:POW.
           ++ assert (POWF : (N.land (s1 R_R1) (s1 R_R2) =? 0) = true)
                by (rewrite LAND, POW; reflexivity).
              arm7_step_rewrite POWF.
              apply N.eqb_eq in POW. rewrite PRED in POW.
              pose proof (land_pred_zero_power2 (magnitude (ps R_R1)) ltac:(lia) POW) as BPOW.
              do 5 arm7_step.
              assert (SGF : slt 32 ((N.lxor (ps R_R0) (ps R_R1)) ⊖ 0) 0 =
                (N.lxor (ps R_R0) (ps R_R1) >> 31 =? 1)).
              { rewrite msub_0_r, N.mod_small by (apply lxor_bound; assumption).
                apply slt32_sign. apply lxor_bound; assumption. }
              pose proof (sign_bound (N.lxor (ps R_R0) (ps R_R1))
                (lxor_bound 32 _ _ PA32 PB32)) as X1.
              assert (SG : N.lxor (ps R_R0) (ps R_R1) >> 31 = 0 \/
                N.lxor (ps R_R0) (ps R_R1) >> 31 = 1) by lia.
              destruct SG as [SG|SG].
              all: rewrite SGF, SG in |- *; arm7_step.
              all: unfold signed_div_post, signed_div_frame.
              all: elimstore; repeat split; psimpl; try assumption.
              all: rewrite div_pow2_index in |- * by (try assumption; lia).
              all: rewrite signed_quotient_pow2 with (k := N.log2 (magnitude (ps R_R1)))
                by exact BPOW.
              all: unfold quotient_sign, apply_sign, neg32; rewrite SG; reflexivity.
           ++ assert (POWF : (N.land (s1 R_R1) (s1 R_R2) =? 0) = false)
                by (rewrite LAND, POW; reflexivity).
              arm7_step_rewrite POWF.
              pose proof (div_general_entry (magnitude (ps R_R0))
                (magnitude (ps R_R1)) MA ltac:(lia) GT) as [K31 DI].
              do 8 arm7_step.
              rewrite N.shiftl_mul_pow2 in *.
              assert (CA : 0x304b0 ⊕
                (msub 28 (31+N.size (magnitude (ps R_R1)))
                  (N.size (magnitude (ps R_R0))) * 2^4) =
                divstage_addr (div_general_k (magnitude (ps R_R0)) (magnitude (ps R_R1)))).
              { apply div_general_addr; lia. }
              rewrite CA. set (cs := update _ _ _).
              assert (C12 : cs R_R12 = N.lxor (ps R_R0) (ps R_R1))
                by (unfold cs; rewrite !update_frame by discriminate; exact R12).
              assert (CFRAME : signed_div_frame ps cs).
              { unfold cs, signed_div_frame; repeat split;
                  rewrite !update_frame by discriminate; assumption. }
              assert (C0 : cs R_R0 = 0)
                by (unfold cs; repeat first
                  [rewrite update_updated | rewrite update_frame by discriminate]; reflexivity).
              assert (C1 : cs R_R1 = magnitude (ps R_R1))
                by (unfold cs; repeat first
                  [rewrite update_updated | rewrite update_frame by discriminate]; reflexivity).
              assert (C3 : cs R_R3 = magnitude (ps R_R0))
                by (unfold cs; repeat first
                  [rewrite update_updated | rewrite update_frame by discriminate]; reflexivity).
              assert (SPRE : unsigned_div_stage cs (magnitude (ps R_R0))
                (magnitude (ps R_R1)) (div_general_k (magnitude (ps R_R0))
                  (magnitude (ps R_R1))) 0 (magnitude (ps R_R0)) cs).
              { unfold unsigned_div_stage, unsigned_div_frame. split; [exact DI|].
                repeat split; try assumption; reflexivity. }
              eapply models_after_steps. eassumption.
                apply division_program_welltyped. intro MDL2.
              eapply (perform_call 0).
              ** reflexivity.
              ** intros. exact (unsigned_div_family_correct cs ps
                   (div_general_k (magnitude (ps R_R0)) (magnitude (ps R_R1)))
                   0 (magnitude (ps R_R0)) _ _ ENTRY MDL2 K31 SPRE).
              ** reflexivity.
              ** intros a' s' t2 ENTRY2 XP UT PRE.
                 destruct_inv 32 PRE.
                 destruct PRE as (q & r & POST).
                 unfold unsigned_div_post, unsigned_div_frame in POST.
                 destruct POST as (NB & BP & HNR & HR & R0Q & R1B & R3R &
                   MEMC & SPC & LRC & R12C & R4C).
                 assert (SGF : slt 32 ((cs R_R12) ⊖ 0) 0 =
                   (N.lxor (ps R_R0) (ps R_R1) >> 31 =? 1)).
                 { rewrite msub_0_r, C12, N.mod_small
                     by (apply lxor_bound; assumption).
                   apply slt32_sign. apply lxor_bound; assumption. }
                 do 2 arm7_step.
                 pose proof (sign_bound (N.lxor (ps R_R0) (ps R_R1))
                   (lxor_bound 32 _ _ PA32 PB32)) as X1.
                 assert (SG : N.lxor (ps R_R0) (ps R_R1) >> 31 = 0 \/
                   N.lxor (ps R_R0) (ps R_R1) >> 31 = 1) by lia.
                 destruct SG as [SG|SG].
                 all: rewrite SGF, SG in |- *; arm7_step.
                 all: unfold signed_div_post, signed_div_frame.
                 all: split;
                   [ elimstore; psimpl
                   | repeat split; rewrite !update_frame by discriminate;
                       [ rewrite MEMC; exact (proj1 CFRAME)
                       | rewrite SPC; exact (proj1 (proj2 CFRAME))
                       | rewrite LRC; exact (proj1 (proj2 (proj2 CFRAME)))
                       | rewrite R4C; exact (proj2 (proj2 (proj2 CFRAME))) ] ].
                 all: pose proof (signed_quotient_eq (ps R_R0) (ps R_R1)
                   (magnitude (ps R_R0)) (magnitude (ps R_R1)) q r
                   eq_refl eq_refl HR HNR) as SQ.
                 all: rewrite SQ; unfold quotient_sign, apply_sign, neg32;
                   rewrite SG; reflexivity.
Qed.
