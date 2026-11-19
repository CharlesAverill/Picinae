From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  armv7_divstep FUN_0003046e_armv7 division_program.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition divstage_addr (k : N) : addr := 0x304b0 + 16 * (31-k).

Definition unsigned_div_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR /\ s R_R12 = s0 R_R12 /\ s R_R4 = s0 R_R4.

Definition div_inv (n b k q r : N) : Prop :=
  n < 2^32 /\ 0 < b /\ r < b * 2^(k+1) /\
  n = b * (q * 2^(k+1)) + r /\ q * 2^(k+1) < 2^32 /\ b * 2^k < 2^32.

Definition unsigned_div_stage (s0 : store) (n b k q r : N) (s : store) : Prop :=
  div_inv n b k q r /\ s R_R0 = q /\ s R_R1 = b /\ s R_R3 = r /\
  unsigned_div_frame s0 s.

Definition unsigned_div_post (s0 : store) (n b q r : N) (s : store) : Prop :=
  n < 2^32 /\ 0 < b /\ n = b*q + r /\ r < b /\
  s R_R0 = q /\ s R_R1 = b /\ s R_R3 = r /\ unsigned_div_frame s0 s.

Definition unsigned_div_invs (s0 : store) (n b : N) (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with
      | 0x304b0 => Some (exists q r, unsigned_div_stage s0 n b 31 q r s)
      | 0x304c0 => Some (exists q r, unsigned_div_stage s0 n b 30 q r s)
      | 0x304d0 => Some (exists q r, unsigned_div_stage s0 n b 29 q r s)
      | 0x304e0 => Some (exists q r, unsigned_div_stage s0 n b 28 q r s)
      | 0x304f0 => Some (exists q r, unsigned_div_stage s0 n b 27 q r s)
      | 0x30500 => Some (exists q r, unsigned_div_stage s0 n b 26 q r s)
      | 0x30510 => Some (exists q r, unsigned_div_stage s0 n b 25 q r s)
      | 0x30520 => Some (exists q r, unsigned_div_stage s0 n b 24 q r s)
      | 0x30530 => Some (exists q r, unsigned_div_stage s0 n b 23 q r s)
      | 0x30540 => Some (exists q r, unsigned_div_stage s0 n b 22 q r s)
      | 0x30550 => Some (exists q r, unsigned_div_stage s0 n b 21 q r s)
      | 0x30560 => Some (exists q r, unsigned_div_stage s0 n b 20 q r s)
      | 0x30570 => Some (exists q r, unsigned_div_stage s0 n b 19 q r s)
      | 0x30580 => Some (exists q r, unsigned_div_stage s0 n b 18 q r s)
      | 0x30590 => Some (exists q r, unsigned_div_stage s0 n b 17 q r s)
      | 0x305a0 => Some (exists q r, unsigned_div_stage s0 n b 16 q r s)
      | 0x305b0 => Some (exists q r, unsigned_div_stage s0 n b 15 q r s)
      | 0x305c0 => Some (exists q r, unsigned_div_stage s0 n b 14 q r s)
      | 0x305d0 => Some (exists q r, unsigned_div_stage s0 n b 13 q r s)
      | 0x305e0 => Some (exists q r, unsigned_div_stage s0 n b 12 q r s)
      | 0x305f0 => Some (exists q r, unsigned_div_stage s0 n b 11 q r s)
      | 0x30600 => Some (exists q r, unsigned_div_stage s0 n b 10 q r s)
      | 0x30610 => Some (exists q r, unsigned_div_stage s0 n b 9 q r s)
      | 0x30620 => Some (exists q r, unsigned_div_stage s0 n b 8 q r s)
      | 0x30630 => Some (exists q r, unsigned_div_stage s0 n b 7 q r s)
      | 0x30640 => Some (exists q r, unsigned_div_stage s0 n b 6 q r s)
      | 0x30650 => Some (exists q r, unsigned_div_stage s0 n b 5 q r s)
      | 0x30660 => Some (exists q r, unsigned_div_stage s0 n b 4 q r s)
      | 0x30670 => Some (exists q r, unsigned_div_stage s0 n b 3 q r s)
      | 0x30680 => Some (exists q r, unsigned_div_stage s0 n b 2 q r s)
      | 0x30690 => Some (exists q r, unsigned_div_stage s0 n b 1 q r s)
      | 0x306a0 => Some (exists q r, unsigned_div_stage s0 n b 0 q r s)
      | 0x306b0 => Some (exists q r, unsigned_div_post s0 n b q r s)
      | 0x3046e | 0x30478 | 0x30484
      | 0x306b8 | 0x306c2 | 0x306d2 | 0x306e8
      | 0x306fc | 0x30712 | 0x5a5b8 | 0x5a5ca | 0x5a60a | 0x5a61c => Some False
      | _ => None
      end
  | _ => None
  end.

Definition unsigned_div_exit (t : trace) : bool :=
  match t with
  | (Addr a, _) :: _ => a =? 0x306b0
  | _ => false
  end.

Lemma unsigned_div_at_stage (s0 : store) (n b k q r : N) (s : store) :
  k <= 31 ->
  unsigned_div_invs s0 n b ((Addr (divstage_addr k), s) :: nil) =
    Some (exists q r, unsigned_div_stage s0 n b k q r s).
Proof.
  intros K31.
  assert (HK : exists nk, nk = N.to_nat k) by (eexists; reflexivity).
  destruct HK as [nk HK].
  assert (KE : k = N.of_nat nk) by (rewrite <- (N2Nat.id k), HK; reflexivity).
  do 32 (try (destruct nk as [|nk])); try lia.
  all: subst k; cbv [divstage_addr N.of_nat unsigned_div_invs]; reflexivity.
Qed.

Ltac solve_divstage n b k PRE :=
  destruct PRE as (q0 & r0 & PRE);
  unfold unsigned_div_stage, unsigned_div_frame, div_inv in PRE;
  destruct PRE as [DI RF];
  destruct DI as [NB [B [HR [HN [HQ HB]]]]];
  destruct RF as [R0H [R1H [R3 F]]];
  destruct F as [MEM [SP [LR [R12 R4]]]];
  destruct (divstep b k q0 r0) as (q' & r') eqn:DD;
  pose proof (divstep_sound b k q0 r0 n B NB HR HN) as DS;
  rewrite DD in DS; simpl in DS;
  try (pose proof (divstep_previous_bound b k (ltac:(lia)) HB) as HBnext);
  destruct (b*2^k <=? r0) eqn:E;
    unfold divstep in DD; rewrite E in DD; cbv beta iota in DD;
    pose proof (f_equal (@fst N N) DD) as Q;
    pose proof (f_equal (@snd N N) DD) as R;
    pose proof Q as Q0; cbv beta iota in Q0;
    simpl in Q, R; rewrite <- Q, <- R in DS;
    pose proof E as E0;
    [ apply N.leb_le in E | apply N.leb_gt in E ];
  assert (HQQ : 2*q0 < 2^32) by (
    pose proof (proj2 (proj2 DS)) as DSQ;
    assert (HP : 1 <= 2^k) by (
      pose proof (N.pow_nonzero 2 k ltac:(discriminate)); lia);
    nia);
  assert (HQQ1 : 1+q0+q0 < 2^32) by lia;
  try (rewrite (N.pow_0_r 2) in *);
  try (rewrite (N.mul_1_r b) in *);
  do 2 arm7_step;
  try (rewrite (N.shiftl_mul_pow2 b k) in *);
  try (rewrite (N.mod_small (b*2^k) (2^32) HB) in *);
  try (rewrite E0 in *);
  do 2 arm7_step;
  eapply NIStep; try reflexivity;
  intros c2 s2 x2 XS2; ISA_step_and_simplify XS2;
  try (rewrite E0 in XS2); ISA_step_and_simplify XS2;
  destruct XS2 as [XS2 X2]; subst x2;
  try lazymatch goal with |- context [exitof (?a+?sz)] => simpl (a+sz) end;
  try (let rt := fresh in set (rt := reset_temps _ _) at 1;
    psimpl_hyp rt; subst rt; rewrite XS2; clear XS2; try clear s2);
  try rewrite exitof_none; try rewrite exitof_some;
  try arm7_step;
  try apply NIHere; hnf;
  unfold unsigned_div_stage, unsigned_div_post, unsigned_div_frame;
  exists q', r'; repeat split; psimpl;
    try assumption; try reflexivity; try lia;
  try match goal with |- context [r0 ⊖ (b << k)] =>
    rewrite <- R; rewrite (N.shiftl_mul_pow2 b k);
    psimpl; rewrite N.mod_small by lia; reflexivity end;
  match type of E with
  | _ < _ => apply divstep_qmod; assumption
  | _ => idtac end;
  try (rewrite (N.shiftl_mul_pow2 b k) in *);
  try (rewrite (N.mod_small (b*2^k) (2^32) HB) in *);
  try (rewrite (N.mod_small (q0+q0) (2^32) HQQ) in *);
  try (rewrite (N.mod_small (1+q0+q0) (2^32) HQQ1) in *);
  try (rewrite msub_nowrap by lia; rewrite !N.mod_small by lia; exact R);
  apply divstep_qmod1; exact Q0.

Theorem unsigned_div_stages_correct :
  forall prog (EXT : division_program ⊆2 prog) s0 n b k q r t xs
         (ENTRY : startof t xs = (Addr (divstage_addr k), s0))
         (MDL : models arm7typctx s0)
         (K31 : k <= 31)
         (PRE : unsigned_div_stage s0 n b k q r s0),
    satisfies_all prog (unsigned_div_invs s0 n b) unsigned_div_exit (xs :: t).
Proof.
  intros prog EXT s0 n b k q r t [x' s'] ENTRY MDL K31 PRE.
  rename PRE into INIT.
  eapply satisfies_all_pmono with (p1 := division_program); [exact EXT | |].
  - intros a s1 t1 EXIT NOCODE. unfold unsigned_div_invs.
    repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [x1 s1] t1 START. rewrite ENTRY in START.
    clear - s0 n b k q r MDL K31 INIT START.
    rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
    apply prove_invs.
    + simpl. rewrite ENTRY. eapply nextinv_here;
      [ cbv [effinv]; rewrite (unsigned_div_at_stage s0 n b k q r s0 K31);
        reflexivity | ].
      hnf. exists q, r. exact INIT.
    + intros.
      erewrite startof_prefix in ENTRY; try eassumption.
      eapply models_at_invariant; try eassumption.
        apply division_program_welltyped.
      intro MDL1. clear - s0 n b PRE MDL1.
      all: destruct_inv 32 PRE.
      all: match type of PRE with context [unsigned_div_stage _ _ _ ?k _ _ _] =>
        solve_divstage n b k PRE end.
Qed.
