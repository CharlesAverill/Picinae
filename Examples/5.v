Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import -(notations) arm7_cfi2.
Require Import Picinae_armv7.
Require Import Lia ZifyN ZifyNat.
Require Import FunctionalExtensionality.
Import ARM7Notations.
Require Import Nat.

Definition LorB (R_E:N) := if R_E then LittleE else BigE.
Notation "! x" := (Z.of_N x) (at level 0, x at level 0, format "! x").
Notation "m [ e | a  ]" := (getmem 32 (LorB e) 4 m a) (at level 50, left associativity).
Notation "m [ e | a := v  ]" := (setmem 32 (LorB e) 4 m a v) (at level 50, left associativity).
Notation N_len l := (N.of_nat (length l)).
Notation N_len_cat l := (N_len (concat l)).
Notation N_len_cat_first n l := (N_len_cat (firstn n l)).
Ltac destruct_match_in H :=
  repeat match type of H with context[match ?x with _ => _ end] =>
    let e := fresh "e" in destruct x eqn:e
  end.
Ltac destruct_match_eqn :=
  repeat match goal with |- context[match ?x with _ => _ end] =>
    let e := fresh "e" in destruct x eqn:e
  end.
Ltac eqapply H := eapply ZifyClasses.eq_iff;[|apply H];repeat f_equal.

Lemma N_add_mod_eq_l: forall a b c m, b mod m = c mod m -> (a + b) mod m = (a + c) mod m.
Proof.
  intros. now rewrite N.Div0.add_mod, H, <-N.Div0.add_mod.
Qed.
Lemma Nshiftl_add_distr : forall a b s, (a << s) + (b << s) = (a + b) << s.
Proof.
  intros. now rewrite !N.shiftl_mul_pow2, N.mul_add_distr_r.
Qed.
Lemma map2list_len: forall m n, length (_map2list m n) = n.
Proof. induction n. easy. simpl. now rewrite IHn. Qed.
Lemma make_jump_table_len:
  forall dis dis' ai sl sr n, length (make_jump_table dis dis' ai sl sr n) = Z.to_nat n.
Proof.
  intros. unfold make_jump_table. rewrite length_rev, map2list_fix. now rewrite map2list_len.
Qed.
Lemma xbits_inner:
  forall n a b c d,
  c <= a -> b <= d ->
    xbits n a b = xbits (xbits n c d) (a-c) (b-c).
Proof.
  intros. apply N.bits_inj. intro. rewrite !xbits_spec. replace (_ + _ + _) with (n0 + a) by lia. lia.
Qed.
Lemma cons1{A}: forall (a:A) b, a::b = (a::nil)++b. Proof. easy. Qed.
Lemma cons2{A}: forall (a:A) b c, a::b::c = (a::b::nil)++c. Proof. easy. Qed.
Lemma reset_temps_overwrite_l: forall s1 s2 s3, reset_temps (reset_temps s1 s2) s3 = reset_temps s1 s3.
Proof. now specialize (reset_vars_overwrite_l armc). Qed.
Lemma reset_temps_not_temp:
  forall v s s', armc v <> None -> reset_temps s s' v = s' v.
Proof.
  intros. unfold reset_temps. rewrite reset_vars_fchoose. unfold fchoose. destruct in_ctx eqn:e. easy. unfold in_ctx in e. now destruct_match_in e.
Qed.
Lemma reset_temps_id: forall s, reset_temps s s = s.
Proof.
  intros. cbv[reset_temps reset_vars]. extensionality x. now destruct archtyps.
Qed.
Lemma reset_temps_models: forall s s', models armc s' <-> models armc (reset_temps s s').
Proof.
  unfold models; split; intros; cbv[reset_temps reset_vars archtyps] in *.
    rewrite CV; now apply H.
    specialize (H v w CV); now rewrite CV in H.
Qed.

Lemma arm_assemble_all_first:
  forall a a' z,
    arm_assemble_all (a::a') = Some z ->
    exists h t, arm_assemble_all a' = Some t /\ z = h::t /\ arm_decode h = a.
Proof.
  induction z. intros. unfold arm_assemble_all in H. destruct_match_in H; discriminate. intros. exists a0, z. repeat split; unfold arm_assemble_all in H; destruct_match_in H; try discriminate. inversion H. now subst. apply arm_assemble_eq in e. inversion H. now subst.
Qed.
Lemma arm_assemble_all_len:
  forall a b, arm_assemble_all a = Some b -> length a = length b.
Proof.
  intros. apply arm_assemble_all_eq in H. now rewrite <- H, length_map.
Qed.
Lemma arm_assemble_all_cond_len:
  forall a cond b, arm_assemble_all_cond a cond = Some b -> (length b = (Nat.b2n (cond <? 14)%Z + length a))%nat.
Proof.
  intros. unfold arm_assemble_all_cond in H. destruct Z.ltb. apply arm_assemble_all_len in H. rewrite <- H. simpl. lia. apply arm_assemble_all_eq in H. rewrite <- H, length_map. lia.
Qed.
Lemma typeof_arm_varid:
  forall n, arm7typctx (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.
Lemma exec_str :
  forall rt rn s s' a c' x offset
    (XS: exec_stmt armc s (arm2il a (STR (Z.of_N rt) (Z.of_N rn) (-(Z.of_N offset)))) c' s' x)
    (RT: rt < 15)
    (RN: rn < 15)
    (O: 0 < offset),
    reset_temps s s' = s[R_PC := a mod 2^32][V_MEM32 := s V_MEM32 [ s R_E | s (arm_varid rn) ⊖ offset := s (arm_varid rt)]]  /\ x = None.
Proof.
  intros. cbv[STR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il Z1 Z14 arm_assign_MemU arm_cond_il arm_cond_exp ] in XS.
  replace (- _ <? _)%Z with true in XS by lia.
  simpl Z.to_N in XS. cbv[N.eqb orb Pos.eqb] in XS. simpl in XS.
  cbv[arm_R] in XS.
  rewrite !N2Z.id in XS.
  replace (Z.to_N _) with (offset) in XS by lia.
  replace (rn =? 15) with false in XS by lia. replace (rt =? 15) with false in XS by lia. unfold arm_varid in *. remember (a mod _). destruct_match_eqn; try lia;
  step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _]; destruct (s R_E); step_stmt XS; now destruct XS as [[? ?] [? _]].
Qed.
Definition same_flags (s s':store) :=
  s' R_T = s R_T /\
  s' R_JF = s R_JF /\
  s' R_E = s R_E.
Definition SafeInst inst :=
  forall a s c' s' x i,
    exec_stmt armc s (arm2il i inst) c' s' x ->
    x <> Some (Addr a) /\ same_flags s s'.
Definition NoJ q := forall_stmts_in_stmt (fun q' : stmt => forall e : exp, q' <> Jmp e) q.
Definition NoE q := forall_stmts_in_stmt (fun q' : stmt => forall i : N, q' <> Exn i) q.
Definition NoJE q := NoJ q /\ NoE q.
Lemma safe:
  forall i
    (J: forall a, noassign R_JF (arm2il a i))
    (T: forall a, noassign R_T (arm2il a i))
    (E: forall a, noassign R_E (arm2il a i))
    (NJ: forall a, NoJ (arm2il a i)),
    SafeInst i.
Proof.
  cbv[SafeInst]. intros. repeat split. eapply stmt_xnotaddr. apply H. apply NJ.
  all: eapply noassign_stmt_same in H; inversion H; now try rewrite H1.
Qed.
Remark armvnotarmv: forall v v2, v < 15 -> v2 < 15 -> v <> v2 -> arm_varid v <> arm_varid v2.
Proof. unfold arm_varid. intros. destruct_match; easy || lia. Qed.
Remark armvnotsp: forall v, v < 13 -> arm_varid v <> R_SP.
Proof. unfold arm_varid. intros. destruct_match; easy || lia. Qed.
Remark armvnotsp': forall v, v < 13 -> R_SP <> arm_varid v.
Proof. unfold arm_varid. intros. destruct_match; easy || lia. Qed.
Remark armvnotpc: forall v, v < 15 -> arm_varid v <> R_PC.
Proof. unfold arm_varid. intros. destruct_match; easy || lia. Qed.
Remark armvnotpc': forall v, v < 15 -> R_PC <> arm_varid v.
Proof. unfold arm_varid. intros. destruct_match; easy || lia. Qed.
Remark armvnote: forall v, arm_varid v <> R_E.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnote': forall v, R_E <> arm_varid v.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnotj: forall v, arm_varid v <> R_JF.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnotj': forall v, R_JF <> arm_varid v.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnott: forall v, arm_varid v <> R_T.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnott': forall v, R_T <> arm_varid v.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnotmem: forall v, arm_varid v <> V_MEM32.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Remark armvnotmem': forall v, V_MEM32 <> arm_varid v.
Proof. unfold arm_varid. intros. now destruct_match. Qed.
Hint Resolve armvnotarmv armvnotsp armvnotsp' armvnotpc armvnotpc' armvnotj armvnotj' armvnott armvnott' armvnote armvnote' armvnotmem armvnotmem': cfi.
Lemma str_safe:
  forall rt rn offset,
  SafeInst (STR rt rn offset).
Proof.
  intros. apply safe; repeat constructor; discriminate.
Qed.
Lemma ldr_safe:
  forall rt rn offset
  (RT: rt <> 15%Z),
  SafeInst (LDR rt rn offset).
Proof.
  intros. apply safe;
  cbv [LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il];
  repeat constructor; try discriminate; replace (_ =? _) with false by lia;
  repeat constructor; auto with cfi; easy.
Qed.
Lemma movw_safe:
  forall rd imm,
  SafeInst (MOVW rd imm).
Proof.
  intros. apply safe; repeat constructor; try discriminate; auto with cfi.
Qed.
Lemma movt_safe:
  forall rd imm,
  SafeInst (MOVT rd imm).
Proof.
  intros. apply safe; repeat constructor; try discriminate; auto with cfi.
Qed.
Lemma exec_ldr:
  forall reg s a c' s' x,
  reg < 15 ->
  models armc s ->
  exec_stmt armc s (arm2il a (LDR (Z.of_N reg) (Z.of_N reg) 0)) c' s' x ->
  reset_temps s s' = s[R_PC := a mod 2^32][arm_varid reg := s V_MEM32 [ s R_E | s (arm_varid reg)] ] /\ x = None.
Proof.
  intros.
  cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il arm_cond_exp arm_assign_R arm_MemU] in H1.
  simpl in H1. rewrite !N2Z.id in H1. destruct N.eqb eqn:e; try lia.
  specialize (H0 (arm_varid reg) 32).
  unfold arm_varid. destruct_match_eqn; try lia; step_stmt H1; destruct H1; step_stmt H1; simpl in H1; destruct H1 as [[? ?] _];
  rewrite H1, N.add_0_r, N.mod_small by (now apply H0); destruct (s R_E); now subst.
Qed.
Lemma exec_ldr':
  forall reg reg2 offset s a c' s' x,
  reg < 15 ->
  reg2 < 15 ->
  offset > 0 ->
  exec_stmt armc s (arm2il a (LDR (Z.of_N reg) (Z.of_N reg2) (- Z.of_N offset))) c' s' x ->
  reset_temps s s' = s[R_PC := a mod 2^32][arm_varid reg := s V_MEM32 [ s R_E | s (arm_varid reg2) ⊖ offset ] ] /\ x = None.
Proof.
  intros.
  cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il arm_cond_exp arm_assign_R arm_MemU] in H2.
  simpl in H2. rewrite !N2Z.id in H2. destruct N.eqb eqn:e; try lia.
  replace (Z.ltb _ _) with true in H2 by lia. simpl in H2. replace (Z.to_N _) with offset in H2 by lia.
  unfold arm_varid. destruct_match_eqn; try lia; step_stmt H2; destruct H2; step_stmt H2; simpl in H2; destruct H2 as [[? ?] _];
  rewrite H2; destruct (s R_E); now subst.
Qed.
Lemma bfx_bound: forall i s s' c' x widthm1 rd lsb rn,
  exec_stmt armc s (arm2il i (ARM_bfx false 14 (Z.of_N widthm1) rd lsb rn)) c' s' x ->
  exists n, s' = s[R_PC := i mod 2^32][arm_varid (Z.to_N rd) := n] /\ n < 2 ^ (widthm1+1) /\ x = None.
Proof.
  intros. cbv[arm2il arm_bfx_il arm_cond_il arm_assign_R arm_R] in H. remember (_ mod _). simpl (Z.to_N 14) in H. unfold arm_varid in H. destruct_match_in H;
  remember (_ + _); remember (Z.to_N lsb); step_stmt H; destruct H as [H _]; subst; clear -H;
  inversion H; inversion E; inversion E1; inversion E0; subst; simpl; repeat eexists;
  replace (widthm1 + 1) with (N.succ (Z.to_N lsb + Z.to_N (Z.of_N widthm1)) - Z.to_N lsb) by lia; apply xbits_bound.
Qed.
Lemma UBFX_bound: forall i s s' c' x reg sl sr,
  exec_stmt armc s (arm2il i (UBFX reg reg sl (Z.of_N sr))) c' s' x ->
  (reg <> 15)%Z ->
  (sr < 32) ->
  exists n, s' = s[R_PC := i mod 2^32][arm_varid (Z.to_N reg) := n] /\ n < 2 ^ (32 - sr) /\ x = None.
Proof.
  intros. cbv [UBFX] in H. unfold Z31 in H. rewrite <-(Z2N.id 31) , <-N2Z.inj_sub in H by lia. apply bfx_bound in H. now rewrite <-N.add_sub_swap in H by lia.
Qed.
Lemma reset_temps_update_r:
  forall s s' n v v', reset_temps s (s'[R_PC := v][arm_varid n := v']) = (reset_temps s s')[R_PC := v][arm_varid n := v'].
Proof.
  intros. unfold reset_temps, arm_varid. now rewrite reset_vars_fchoose, !fchoose_update_distr, !fchoose_update_l by now destruct_match_eqn.
Qed.
Lemma exec_lsl:
  forall reg s a c' s' x,
  reg < 15 ->
  exec_stmt arm7typctx s (arm2il a (LSL (Z.of_N reg) (Z.of_N reg) Z2)) c' s' x ->
  reset_temps s s' = s[R_PC := a mod 2^32][arm_varid reg := (s (arm_varid reg) << 2) mod 2 ^ 32] /\ x = None.
Proof.
  intros. cbv[LSL arm2il arm_data_r_il arm_data_op_il arm_data_r_shiftc DecodeImmShift arm_data_il arm_cond_il arm_cond_exp arm_assign_R arm_R] in H0. simpl in H0. destruct N.eqb eqn:e; try lia.
  rewrite N2Z.id in H0. unfold arm_varid. destruct_match_eqn; step_stmt H0; destruct H0; step_stmt H0; destruct H0 as [[? ?] ?]; lia || now rewrite H0.
Qed.
Lemma exec_add: forall i s s' c' x reg imm shift,
  (reg < 15)%Z ->
  (imm < 2^8) ->
  (shift < 2^4) ->
  exec_stmt armc s (arm2il i (ARM_data_i ARM_ADD 14 0 reg reg (Z.lor (Z.shiftl (Z.of_N shift) 8) (Z.of_N imm)))) c' s' x ->
  reset_temps s s' = s[R_PC := i mod 2^32] [arm_varid (Z.to_N reg) := (s (arm_varid (Z.to_N reg)) ⊕ (imm >> (2 * shift) .| ((imm << (32 - (2* shift))) mod 2^ 32)))]
  /\ x = None.
Proof.
  intros.
  cbv[arm2il arm_data_i_il arm_data_op_il arm_data_i_addwcarry ARMExpandImm_C AddWithCarry arm_data_il arm_cond_il Shift_C] in H2.
  simpl (Z.to_N 0 =? 1) in H2.
  destruct N.eqb eqn:e; try lia. simpl (Z.to_N 14) in H2. cbv[arm_cond_exp] in H2. cbv[N.ltb N.compare Pos.compare Pos.compare_cont andb arm_assign_R] in H2.
  remember (xbits _ _ _).
  remember (2 * (xbits _ _ _)).
  rewrite Z2N_inj_lor, Z2N_inj_shiftl, N2Z.id, xbits_lor, xbits_shiftl in Heqn0, Heqn by (try apply Z.shiftl_nonneg; lia).
  rewrite xbits_0_j, N.shiftl_0_l, N.lor_0_l, N2Z.id, xbits_0_i, N.mod_small in Heqn by assumption.
  rewrite xbits_0_i, N.mod_small, N2Z.id, xbits_above, N.lor_0_r, N.shiftl_0_r in Heqn0 by assumption.
  unfold arm_varid. destruct_match_eqn; try lia; cbv[arm_varid arm_R N.eqb] in H2;
  step_stmt H2; destruct H2 as [H2 _]; step_stmt H2; destruct H2 as [[H2 H3] _];
  (split; [clear H3|apply H3]);
  rewrite H2; subst;
  rewrite N.add_0_r, msub_sub, (N.mod_small (_ - _)) by lia;
  (erewrite <-(N.mod_small (_ >> _)), <-N_lor_mod_pow2, N.Div0.add_mod_idemp_r, N.Div0.mod_mod; [reflexivity|
  assert ((imm >> 2 * shift) <= imm) by apply N.shiftr_upper_bound; lia]).
Qed.
Lemma exec_align:
  forall a s s' c' x
    (M: models armc s)
    (XS: exec_stmt armc s (arm2il a (ALIGN SP)) c' s' x),
    reset_temps s s' = s[R_PC := a mod 2^32][R_SP := (s R_SP >> 2) * 4] /\ x = None.
Proof.
  intros.
  cbv [ALIGN arm2il arm_data_i_il arm_data_op_il arm_data_i_shiftc arm_data_il SP Z13 arm_cond_il arm_assign_R] in XS. simpl N.eqb in XS. cbn in XS. step_stmt XS. destruct XS as [XS _]. step_stmt XS. simpl in XS. 
    change (4294967292) with (N.lnot (2 * (2 * 0 + 1) + 1) 32) in XS.
    rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r, N.mul_assoc, N.mul_comm in XS. simpl. easy.
    specialize (M R_SP _ eq_refl).
    destruct (s R_SP) eqn:E; now try solve [apply N.log2_lt_pow2; lia].
Qed.
Lemma exec_ldrpc:
  forall s a c' s' x
    (XS: exec_stmt armc s (arm2il a (LDR PC SP Z_8)) c' s' x)
    (D: (4 | getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s R_SP ⊖ 8)))
    (S: (4 | s R_SP)),
    x = Some (Addr (getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s R_SP ⊖ 8))) /\ reset_temps s s' = s[R_PC := a mod 2^32].
Proof.
  intros. cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il Z1] in XS.
  simpl Z.to_N in XS. cbv[N.eqb orb Pos.eqb arm_cond_exp BXWritePC arm_R arm_varid] in XS . simpl in XS. remember (_ mod _).
  step_stmt XS. destruct XS as [XS _]. step_stmt XS. replace (_ =? _) with true in XS. simpl in XS. destruct XS as [XS _].
  step_stmt XS. replace (_ mod _) with 0 in XS. destruct XS as [XS _]. step_stmt XS. replace (_ =? 1) with false in XS. destruct XS as [XS _].
  step_stmt XS. destruct XS as [[? ?] _]. destruct (s R_E). now subst. now subst. rewrite <-N.bit0_eqb, N.shiftr_spec'. 
  destruct (s R_E);  destruct D; simpl in H; rewrite H; change 4 with (2^2); now rewrite N.mul_pow2_bits_low. 
  destruct (s R_E);  destruct D; simpl in H; rewrite H; simpl; lia.
  destruct S. rewrite H. unfold msub. simpl N.sub. change 4294967288 with (1073741822*4). rewrite <-N.mul_add_distr_r.
  rewrite N_land_mod_pow2_move.
  change (_ mod _) with (N.ones 2).
  rewrite N.land_ones. lia.
Qed.
Lemma land_pow2_lt:
  forall a n, a < 2 ^ n -> N.land a (2^n) = 0.
Proof.
  intros. apply N.bits_inj_0. intros. rewrite N.land_spec. destruct (N.eq_dec n0 n). subst. 
  now rewrite <-(N.mod_small _ _ H), N.mod_pow2_bits_high, andb_false_l.
  now rewrite N.pow2_bits_false, andb_false_r.
Qed.

Lemma exec_ldmdb3:
  forall rh rl s s' c' x a
    (RL: rl < rh)
    (RH: rh < 15)
    (XS: exec_stmt armc s (arm2il a (LDMDB3 (Z.of_N rh) (Z.of_N rl) (Z.of_N rh) PC)) c' s' x)
    (M: (4|getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid rh) ⊖ 4 ))),
    x = Some (Addr (getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid rh) ⊖ 4 ))) /\ same_flags s s' \/ x = Some (Raise 16) /\ same_flags s s'.
Proof.
  intros.
  cbv[LDMDB3 arm2il arm_lsm_il arm_lsm_op_il arm_lsm_op_start arm_lsm_op_type arm_ldm_il arm_lsm_il_ arm_cond_il] in XS. 
  rewrite !Z.shiftl_mul_pow2, !Z.mul_1_l in XS.
  rewrite <-(N2Z.id 15), <-Z2N.inj_testbit, Z2N.id, !Z.lor_spec, Z.pow2_bits_true, orb_true_r in XS.
  simpl (Z.to_N 0) in XS. simpl (Z.to_N Z14) in XS. cbv[ arm_cond_exp] in XS. 
  rewrite !Z2N_inj_lor, !Z2N.inj_pow, (N.mod_small _ (2^16)), !popcount_lor, !popcount_pow2 in XS. 
  rewrite !land_pow2_lt in XS. remember (fun i => _). unfold for_0_14 in XS.
  simpl in XS. 
  simpl in Heqy. subst y.
  shelve. 
  rewrite !N2Z.id; apply lor_bound; apply N.log2_up_lt_pow2; cbn; lia.
  rewrite !N2Z.id; apply N.log2_up_lt_pow2; try rewrite N.log2_up_pow2; destruct rh; lia.
  rewrite !N2Z.id; apply lor_bound; try apply lor_bound; try apply N.log2_up_lt_pow2; cbn; lia.
  all: unfold PC, Z15; cbn; try lia.
  apply Z.lor_nonneg; split; destruct rl, rh; lia.
  apply Z.lor_nonneg; split; try apply Z.lor_nonneg; try split; destruct rl, rh; lia.
  Unshelve.
  remember (arm_varid rl, arm_varid rh).
  remember (s R_E).
  unfold arm_varid at 2 in Heqp.
  (*this one takes so long*)
  destruct_match_in Heqp; try lia;
  unfold arm_varid in Heqp; destruct_match_in Heqp; try lia;
  simpl in XS;
  destruct n eqn:E; remember (_ mod _);
  step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _];
  (destruct N.eqb; [left| step_stmt XS; right; destruct XS as [[S X] _]; repeat split; auto; now erewrite <-reset_temps_not_temp, S, update_frame by discriminate]);
      step_stmt XS; destruct XS as [XS _]; rewrite <-Heqn, N.shiftr_0_r in XS;
  rewrite !N.Div0.add_mod_idemp_l, <-2N.add_assoc in XS; simpl in XS; simpl in M; inversion M;
  unfold msub in H; simpl in H; rewrite <-N.add_assoc in XS; simpl in XS; rewrite H in XS;  replace (_ mod 2) with 0 in XS by lia; step_stmt XS; destruct XS as [XS _];
  rewrite <-Heqn, N.Div0.add_mod_idemp_l, <-N.add_assoc in XS; simpl in XS; rewrite H in XS; replace (_ =? 1) with false in XS by (simpl;lia);
  step_stmt XS; destruct XS as [[S XS] _]; rewrite <-Heqn, N.Div0.add_mod_idemp_l, <-N.add_assoc in XS; repeat split; auto; now erewrite <-reset_temps_not_temp, S, !update_frame by discriminate.
Qed.
Lemma N2Z_inj_popcount: forall n, Z.of_N (popcount n) = Z_popcount (Z.of_N n).
Proof.
  intros. now destruct n.
Qed.
Lemma forget_cond:
  forall c s q1 e q2 q3 c' s' x,
    exec_stmt c s (q1 $; If e q2 q3) c' s' x ->
    exec_stmt c s (q1 $; If (Unknown 1) q2 q3) c' s' x.
Proof.
  intros. inversion H.
    now constructor.
    subst. eapply XSeq2.
      apply XS1.
      inversion XS0. destruct b; [apply XIf with (b:=0)|apply XIf with (b:=1)]; now try constructor.
Qed.
Lemma noje_seq: forall a b, NoJE a -> NoJE b -> NoJE (a $; b).
Proof. intros. now destruct H, H0. Qed.
Lemma for_0_14_noje:
  forall reg_list f,
    (forall n m, NoJE (f n m)) -> NoJE (for_0_14 reg_list f).
Proof.
  intros. destruct reg_list. easy. simpl. generalize 0 at 1, 0 at 2. induction p. intros. simpl. cbv. apply noje_seq. easy. easy. 
  intro. simpl. easy. intro. simpl. easy.
Qed.
Lemma for_context:
forall reg_list f c, (forall n m s s' c' x, exec_stmt c s (f n m) c' s' x -> c' = c) ->
  (forall s s' c' x, exec_stmt c s (for_0_14 reg_list f) c' s' x -> c' = c).
Proof.
  intros. destruct reg_list. simpl in H0. inversion H0. easy. simpl in H0. revert H0. generalize 0 at 1, 0 at 2, s. induction p.
    intros. simpl in H0. inversion H0. subst. now apply H in XS. apply H in XS1. subst. now apply IHp in XS0.
    intros. simpl in H0. now apply IHp in H0.
    intros. simpl in H0. now apply H in H0.
Qed.
Lemma for_noassign:
  forall reg_list f v, (forall n m, noassign v (f n m)) -> noassign v (for_0_14 reg_list f).
Proof.
  intros. destruct reg_list. simpl. constructor.
    simpl. generalize 0 at 1, 0 at 2. induction p.
      intros. simpl. constructor. apply H. apply IHp.
      intros. simpl. apply IHp.
      intros. simpl. apply H.
Qed.
Lemma exec_ldm: 
  forall op cond Rn register_list a s s' c' x W
    (R: N.testbit register_list 15 = true)
    (RN: Rn < 15)
    (O: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => False | _ => True end)
    (XS: exec_stmt armc s (arm2il a (ARM_lsm op cond W (Z.of_N Rn) (Z.of_N register_list))) c' s' x),
    (let bc := (Z4 * Z_popcount (Z.of_N (register_list mod 2^16)))%Z in
     let addr := s V_MEM32 [s R_E | s (arm_varid Rn) ⊕ ofZ 32 (arm_lsm_op_start op bc + bc - Z4) ] in
     (4|addr) -> x = Some (Addr addr) /\ same_flags s s' )
    \/ x = None /\ same_flags s s' \/ x = Some (Raise 16) /\ same_flags s s'.
Proof.
  intros. rewrite <-N2Z_inj_popcount.
  cbv[arm2il arm_lsm_il arm_lsm_op_il arm_lsm_op_type] in XS. remember (_ mod _) as a'.
  replace (match op with _ => _ end) with arm_ldm_il in XS by now destruct op.
  cbv[arm_ldm_il arm_lsm_il_] in XS.
  apply forget_cond in XS. rewrite !N2Z.id, R in XS. remember (popcount _).
  rewrite <-(cbits_xbits _ 15 16), <-fold_cbits, popcount_lor, xbits_0_i, popcount_shiftl in Heqn.
  replace (_ .& _) with 0 in Heqn by now rewrite <-N_land_mod_pow2_move, N.shiftl_mul_pow2, N.Div0.mod_mul, N.land_0_l.
  unfold xbits in Heqn. rewrite <-N.bit0_mod, N.shiftr_spec', N.add_0_l, R, N.sub_0_r in Heqn. simpl N.b2n in Heqn. 
  remember (ofZ _ _).
  remember (ofZ _ (arm_lsm_op_wback _ _)).
  remember (4 * n - 4).
  cbv [arm_assign_R] in XS.

  inversion XS.
    easy.
    subst q1 q2 c'0 s'0 x'. inversion XS1. inversion E. subst v e c2 s2 a' w0 w n3. clear XS XS1. rewrite <-store_upd_eq in XS0 by easy. rename XS0 into XS.
  inversion XS. destruct b.
    step_stmt XS0. right. left. destruct XS0 as [[S X] _]. repeat split; auto; now erewrite <-reset_temps_not_temp, S, update_frame by discriminate.
    subst e q1 q2 c'0 s'0 x0. clear E0 p XS E. rename XS0 into XS.
  inversion XS. destruct b.
    step_stmt XS0. right. right. destruct XS0 as [[S X] _]. repeat split; auto; now erewrite <-reset_temps_not_temp, S, update_frame by discriminate.
    subst e q1 q2 c'0 s'0 x0. clear E p XS. rename XS0 into XS.
  inversion XS.
    exfalso. clear -XS0. inversion XS0.
      destruct N.eqb; now inversion XS.
      apply stmt_xnone in XS2. easy. 1,2: now apply for_0_14_noje.
    subst q1 q2 c'0 s'0 x'.
  assert (c2 = armct). {
    clear - XS1. inversion XS1. subst. assert (c0 = armct). {
      clear - XS0. destruct N.eqb.
        inversion XS0. subst. inversion XS1. subst. inversion XS2. subst.
        inversion E. inversion E2. subst. simpl. rewrite <-store_upd_eq. easy.
        inversion E0. inversion E4. subst. simpl.
        rewrite update_frame by (unfold arm_varid; destruct_match; discriminate). apply typeof_arm_varid.
        inversion XS0. subst. inversion E. inversion E2. subst. easy.
  }
    subst c0. clear XS0 XS1. apply for_context in XS2. easy. intros. inversion H. subst. rewrite <-store_upd_eq. easy.
    unfold armct. rewrite update_frame by (unfold arm_varid; destruct_match; discriminate).
    inversion E. subst. inversion E2. subst. apply typeof_arm_varid.
  }
  subst c2.
  assert (T0: s2 temp0 = s (arm_varid Rn) ⊕ n0). {
    clear - RN XS1. inversion XS1. subst. apply (noassign_stmt_same temp0) in XS2. inversion XS2. 
    clear - RN XS0. destruct N.eqb.
      inversion XS0. subst. inversion XS1. subst. inversion E. subst. unfold arm_R in E1. replace (_ =? _) with false in E1 by lia. inversion E1. subst.
      rewrite typeof_arm_varid in TYP. inversion TYP. subst. simpl in XS2. inversion E2. subst. apply (noassign_stmt_same temp0) in XS2. inversion XS2.
      rewrite update_updated. rewrite update_frame by now apply armvnotpc. easy. constructor. unfold arm_varid; destruct_match; discriminate.
      inversion XS0. subst. inversion E. subst. inversion E. subst. unfold arm_R in E1. replace (_ =? _) with false in E1 by lia. inversion E1. subst. inversion E2. subst.
      rewrite typeof_arm_varid in TYP. inversion TYP. subst. simpl.
      rewrite update_updated. rewrite update_frame by now apply armvnotpc. easy.
      apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (M: s2 V_MEM32 = s V_MEM32). {
    apply (noassign_stmt_same V_MEM32) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (RE: s2 R_E = s R_E). {
    apply (noassign_stmt_same R_E) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (RJ: s2 R_JF = s R_JF). {
    apply (noassign_stmt_same R_JF) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (RT: s2 R_T = s R_T). {
    apply (noassign_stmt_same R_T) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  clear XS1. rewrite (store_upd_eq _ _ _ T0), (store_upd_eq _ _ _ M), (store_upd_eq _ _ _ RE) in XS0.
  cbv [BXWritePC] in XS0.
  left. intros. enough (A: addr = s V_MEM32 [s R_E | s (arm_varid Rn) ⊕ n0 ⊕ n2]).
  step_stmt XS0. replace (_ mod 2) with 0 in XS0. destruct XS0 as [XS0 _].
  step_stmt XS0. replace (_ =? 1) with false in XS0. destruct XS0 as [XS0 _].
  step_stmt XS0. destruct XS0 as [[S X] _]. rewrite A, X. repeat split; [now destruct (s R_E)|..];
    now erewrite <-reset_temps_not_temp, S, !update_frame, ?update_updated by discriminate.
  inversion H. cbv[ N.shiftr Pos.iter]. destruct (s R_E); simpl LorB in A; rewrite <-A, H0; lia.
  inversion H. destruct (s R_E); simpl LorB in A; rewrite <-A, H0, N.shiftr_0_r; lia.
  subst n0 n2 addr bc. clear -Heqn. unfold Z4. rewrite N2Z.inj_mul. simpl Z.of_N.
  remember (arm_lsm_op_start _ _). unfold ofZ in *.
  rewrite <-(N.Div0.add_mod_idemp_r _ (4*n-4)), <-(N2Z.id ((4*n-4) mod _)), N.Div0.add_mod_idemp_l, <-N.add_assoc, <-Z2N.inj_add by lia.
  simpl popcount in Heqn.
  rewrite N2Z.inj_mod, N2Z.inj_sub, N2Z.inj_mul by lia. simpl Z.of_N. rewrite <-Z.add_sub_assoc, Z.add_mod by lia.
  symmetry. rewrite <-N.Div0.add_mod_idemp_r. change (2^32) with (Z.to_N (2^32)). rewrite <-Z2N.inj_mod.
  subst. now destruct (s R_E). lia. lia.
Qed.
Lemma exec_str':
  forall rt rn s s' a c' x offset
    (XS: exec_stmt armc s (arm2il a (STR (Z.of_N rt) (Z.of_N rn) offset)) c' s' x)
    (RT: rt < 15)
    (RN: rn < 15),
    reset_temps s s' = s[R_PC := a mod 2^32][V_MEM32 := setmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid rn) ⊕ (ofZ 32 offset)) (s (arm_varid rt))] /\ x = None.
Proof.
  intros.
  cbv[STR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il Z1 Z14 arm_assign_MemU arm_cond_il arm_cond_exp ] in XS.
  destruct (Z_lt_le_dec offset 0);
  [replace (_ <? _)%Z with true in XS by lia|
  replace (_ <? _)%Z with false in XS by lia];
  simpl Z.to_N in XS; cbv[N.eqb orb Pos.eqb] in XS; simpl in XS;
  cbv[arm_R] in XS;
  rewrite !N2Z.id in XS;
  replace (rn =? 15) with false in XS by lia; replace (rt =? 15) with false in XS by lia. remember (Z.to_N _).
  unfold arm_varid in *. destruct_match_eqn; try lia;
  step_stmt XS;
  destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _]; destruct (s R_E); step_stmt XS; destruct XS as [[? ?] [? _]];
  subst n; unfold msub in H; rewrite <-N.Div0.add_mod_idemp_r , <-msub_0_l, msub_0_l_neg in H;
  unfold toZ in H; rewrite Z2N.id, Z.opp_eq_mul_m1, canonicalZ_mul_l in H by lia; now replace (_ * -1)%Z with offset in H by lia.
  remember (Z.to_N _).
  unfold arm_varid in *. destruct_match_eqn; try lia;
  step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct (s R_E); destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _];
  subst n; replace (Z.abs _) with offset in XS by lia; unfold ofZ; now rewrite Z2N.inj_mod, N.Div0.add_mod_idemp_r by lia.
Qed.

Lemma exec_bx:
  forall reg s a c' s' x,
  reg < 15 ->
  (4 | s (arm_varid reg)) ->
  exec_stmt armc s (arm2il a (ARM_BX 14 (Z.of_N reg))) c' s' x ->
  x = Some (Addr (s (arm_varid reg))) /\ same_flags s s'.
Proof.
  intros.
  cbv[arm2il arm_bx_il arm_cond_il arm_cond_exp BXWritePC arm_R] in H1. simpl in H1.
  rewrite N2Z.id in H1. remember (_ mod _).
  change 4 with (2^2) in H0. inversion H0.
  unfold arm_varid. destruct_match_eqn; try lia; simpl arm_varid in *;
  step_stmt H1; destruct H1; step_stmt H1;
  rewrite N.shiftr_0_r, N.Div0.mul_mod, N.mul_0_r, N.Div0.mod_0_l in H1; destruct H1;
  step_stmt H1; rewrite N.shiftr_div_pow2, <-N.testbit_spec', N.mul_pow2_bits_low in H1 by lia; destruct H1; step_stmt H1; destruct H1 as [[S X] _]; (repeat split; [now rewrite X, H2|..]); now erewrite <-reset_temps_not_temp, S, !update_frame by discriminate.
Qed.
Lemma exec_blx:
  forall reg s a c' s' x,
  reg < 15 ->
  (4 | s (arm_varid reg)) ->
  exec_stmt armc s (arm2il a (ARM_BLX_r 14 (Z.of_N reg))) c' s' x ->
  x = Some (Addr (s (arm_varid reg))) /\ same_flags s s'.
Proof.
  intros.
  cbv[arm2il arm_bx_il arm_cond_il arm_cond_exp BXWritePC arm_R] in H1. simpl in H1.
  rewrite N2Z.id in H1. remember (_ mod _).
  change 4 with (2^2) in H0. inversion H0.
  unfold arm_varid. destruct_match_eqn; try lia; simpl arm_varid in *;
  step_stmt H1; destruct H1; step_stmt H1;
  rewrite N.shiftr_0_r, N.Div0.mul_mod, N.mul_0_r, N.Div0.mod_0_l in H1; destruct H1;
  step_stmt H1; rewrite N.shiftr_div_pow2, <-N.testbit_spec', N.mul_pow2_bits_low in H1 by lia; destruct H1; step_stmt H1; destruct H1 as [[S X] _]; (repeat split; [now rewrite X, H2|..]); now erewrite <-reset_temps_not_temp, S, !update_frame by discriminate.
Qed.


Fixpoint blockindex (irms: list (list Z)) j :=
  match irms with
  | irm::tail =>
      if j <? N_len irm
      then 0
      else blockindex tail (j - N_len irm) + 1
  | _ => 0
  end.
Fixpoint startsblock (irms: list (list Z)) i' a :=
  match irms with
  | irm::tail =>
      if a =? i'*4
      then true
      else startsblock tail (i' + N_len irm) a
  | _ => false
  end.
Definition outofbounds (irms: list (list Z)) i' a :=
  (a <? i' * 4) || ((i' + N_len_cat irms) * 4 <=? a).
Lemma startsblock_index:
  forall irms i' a,
    startsblock irms i' a = true -> 
    exists n,
      lt n (length irms) /\
      (i' + N_len_cat_first n irms) * 4 = a.
Proof.
  induction irms.
    easy.
    cbn [startsblock]. intros. destruct N.eqb eqn:e.
      exists O. split. simpl. lia. simpl length. lia.
      apply IHirms in H. inversion H. exists (S x). split. simpl. lia. rewrite firstn_cons, concat_cons, length_app. lia.
Qed.
Lemma startsblock_firstn:
  forall irms i' n,
    lt n (length irms) ->
    startsblock irms i' ((i' + N_len_cat_first n irms) * 4) = true.
Proof.
  induction irms.
    easy.
    cbn [startsblock]. intros. destruct N.eqb eqn:e.
      reflexivity.
      destruct n.
        simpl N.of_nat in e. lia.
        simpl in H. now rewrite firstn_cons, concat_cons, length_app, Nat2N.inj_add, N.add_assoc, IHirms by lia.
Qed.
Lemma outofbounds_firstn:
  forall irms i' n,
    ge n (length irms) ->
    outofbounds irms i' ((i' + N_len_cat_first n irms) * 4) = true.
Proof.
  intros.
  cbv[outofbounds].
  now rewrite firstn_all2, N.leb_refl, orb_true_r by assumption. 
Qed.
Definition NonEmpty{A} (l : list (list A)) := Forall (fun e => lt O (length e)) l.
Lemma blockindex_firstn:
  forall n irms,
    NonEmpty irms ->
    le n (length irms) ->
    blockindex irms (N_len_cat_first n irms) = N.of_nat n.
Proof.
  induction n. intros. destruct irms. now simpl. simpl. inversion H. now replace (N.ltb _ _) with true by lia.
  intros. destruct irms. now simpl in H0. cbn [blockindex]. rewrite firstn_cons, concat_cons, length_app. replace (N.ltb _ _) with false by lia. replace (_ - _) with (N_len_cat_first n irms) by lia. rewrite IHn. lia. now inversion H. simpl in H0. lia.
Qed.
Lemma blockindex_app:
  forall l l' n, blockindex (l' ++ l) (N_len_cat l' + n) = blockindex l n + N_len l'.
Proof.
  induction l'. intro. now rewrite N.add_0_r.
  intros. cbn. rewrite length_app.
  replace (_<?_) with false by lia.
  replace (_ + n - _) with (N_len_cat l' + n) by lia. rewrite IHl'.
  lia.
Qed.
Lemma sb_not_oob:
  forall irms i' m,
    NonEmpty irms ->
  startsblock irms i' m = true -> outofbounds irms i' m = false.
Proof.
  induction irms; cbn.
    easy.
    intros. destruct N.eqb eqn:e; unfold outofbounds in *; rewrite !orb_false_iff, concat_cons, length_app in *.
      inversion H. lia.
      apply IHirms in H0. lia. now inversion H.
Qed.

Lemma exec_GOTO:
  forall s l cond src dest c' s' x i,
    src < 2^30 ->
    dest < 2^30 ->
    GOTO l cond (Z.of_N src) (Z.of_N dest) = Some i ->
    exec_stmt armc s (arm2il (src * 4) i) c' s' x ->
    (x = Some (Addr (dest * 4)) \/ (x = None /\ cond <> 14%Z)) /\ same_flags s s'.
Proof.
  intros s l cond src dest c' s' x i S D G. intros.
  cbv [GOTO] in G. destruct orb eqn:e in G; try discriminate.
  remember (_ - _ - _)%Z as offset. unfold Z2, Z_8388608, Z8388607 in *.
  assert (src * 4 ⊕ 8 ⊕ scast 26 32 (Z.to_N (offset mod 16777216) << 2) .& 4294967292 = dest * 4).
  {
    change 2 with (Z.to_N 2) at 2. rewrite <- Z2N_inj_shiftl, Z.shiftl_mul_pow2, <- Zmult_mod_distr_r by lia.
    change (Z.to_N _) with (ofZ 26 (offset * 4)).
    unfold scast. rewrite toZ_ofZ by (unfold signed_range; cbn; lia). unfold ofZ.
    rewrite <- (N2Z.id ((_ + 8) mod _)), <- Z2N.inj_add, N2Z.inj_mod, <- (N2Z.id (_ ^ _)), <- Z2N.inj_mod, <- Zplus_mod by lia.
    replace (_ + _ * 4)%Z with (Z.of_N (dest * 4)) by lia.
    rewrite Z2N.inj_mod, 2 N2Z.id, N_land_mod_pow2_move by lia.
    change (_ mod _) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
    rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r. lia.
    destruct (dest * 4) eqn:E; now try solve [apply N.log2_lt_pow2; lia].
  }
  destruct (Z.eq_dec cond 14). subst cond.
  destruct l; inversion G; subst; cbv [arm2il arm_bl_il arm_b_il] in H; rewrite N.mod_small in H by lia;
    remember (scast _ _ _) as dsta; remember (src * 4) as srca;
    step_stmt H; destruct H as [H _];
    step_stmt H; destruct H as [[? ?] _]; (split; [left; now rewrite H1, H0| repeat split; now erewrite <-reset_temps_not_temp, H, update_frame by discriminate]).
  destruct l; inversion G; subst; cbv [arm2il arm_bl_il arm_b_il] in H; rewrite N.mod_small in H by lia;
    remember (scast _ _ _) as dsta; remember (src * 4) as srca; apply forget_cond in H;
    step_stmt H; destruct H as [H _]; destruct (_ mod _) in H;
    step_stmt H; destruct H as [[? H] _]; (split; [(now right) || left; now rewrite H, H0|repeat split; now erewrite <-reset_temps_not_temp, H1, update_frame by discriminate]).
Qed.
Lemma exec_GOTOz:
  forall s l cond src dest c' s' x z,
    src < 2^30 ->
    dest < 2^30 ->
    GOTOz l cond (Z.of_N src) (Z.of_N dest) = Some z ->
    exec_stmt armc s (arm2il (src * 4) (arm_decode z)) c' s' x ->
    (x = Some (Addr (dest * 4)) \/ (x = None /\ cond <> 14%Z)) /\ same_flags s s'.
Proof.
  intros. unfold GOTOz in H1. destruct GOTO eqn:e in H1; try discriminate. apply arm_assemble_eq in H1. rewrite H1 in H2.
  now apply (exec_GOTO s l cond src dest c' s' x a).
Qed.
Lemma fix_make_i:
  forall z's i', make_i's z's i' = _make_i's z's i'.
Proof.
  induction z's. easy.
  intros. cbn. rewrite <-IHz's. unfold make_i's. cbn. rewrite <-rev_unit. apply rev_inj. rewrite !rev_involutive, Z.add_0_r.
  replace (_, i'::nil) with ((Z.of_nat (length a) + 0)%Z, i'::nil) by now rewrite Z.add_0_r.
  rewrite <-(app_nil_l (i'::nil)) at 1. remember nil. rewrite Heql at 2. rewrite Heql at 3. generalize l, 0%Z.
  clear IHz's.
  induction z's. easy. simpl. simpl. intros. rewrite <-IHz's. now rewrite !Z.add_assoc.
Qed.
Lemma make_i's_len:
  forall z's i', length (make_i's z's i') = length z's.
Proof.
  setoid_rewrite fix_make_i. induction z's. easy. intro. simpl. now rewrite IHz's.
Qed.
Lemma make_i's_first:
  forall z's i' d, lt O (length z's) -> nth O (make_i's z's i') d = i'.
Proof.
  intros. destruct z's. easy. now rewrite fix_make_i.
Qed.
Lemma rewrite_w_table_irm:
  forall irm tc dis i2i' cond i ti ai irm' table tc'
    (RWT: rewrite_w_table irm tc dis i2i' cond i ti ai = Some (irm', table, tc')),
  exists ti sl sr, irm cond i ti sl sr = Some irm'.
Proof.
  intros. unfold rewrite_w_table in RWT. destruct_match_in RWT; try discriminate; inversion RWT; subst.
    now exists z0, z1, z.
    now exists ti, z, z0.
Qed.
Lemma wo_table_irm:
  forall z' tc irm table tc'
    (WT: wo_table z' tc = Some (irm, table, tc')),
    z' = Some irm.
Proof. intros; destruct z'; now inversion WT. Qed.

Lemma rewrite_nonempty:
  forall {zs tc pol i2i' i ti ai bi txt irms tables}
    (R: _rewrite zs tc pol i2i' i ti ai bi txt = Some (irms, tables)),
  NonEmpty irms.
Proof.
  induction zs. intros. simpl in R. destruct_match_in R; try easy. inversion R. constructor. simpl. lia. easy.
  intros. simpl in R. destruct_match_in R; try easy. inversion R. subst. constructor. shelve. now apply IHzs in e3.
  Unshelve.
  rename e0 into RI.
  unfold rewrite_inst in RI. destruct negb. easy. unfold goto_abort, rewrite_b, rewrite_bl, rewrite_b_bl in RI.
  destruct_match_in RI; try discriminate;
    ( (apply rewrite_w_table_irm in RI; inversion RI as [? [? [? IRM]]]) ||
      (apply wo_table_irm in RI; rename RI into IRM);
      apply arm_assemble_all_cond_len in IRM; rewrite IRM)
    || inversion RI;
    simpl; lia.
Qed.


Lemma rewrite_len:
  forall {zs tc pol i2i' i ti ai bi txt irms tables}
    (R: _rewrite zs tc pol i2i' i ti ai bi txt = Some (irms, tables)),
  S (length zs) = length irms.
Proof.
  induction zs. intros. simpl in R. destruct_match_in R; try easy. now inversion R.
  intros. simpl in R. destruct_match_in R; try easy. inversion R. subst. simpl. apply IHzs in e3. lia.
Qed.



(* each pair of elements has the same length *)
Definition SameLens{A} (a:list (list A)) b := forall n d, length (nth n a d) = length (nth n b d).
(* length of an irm is independent of i2i' *)
Lemma rw_i2i'_samelens:
  forall {zs _tc tc pol _i2i' i2i' i _ti ti ai bi txt _irms _tables irms tables}
    (_R: _rewrite zs _tc pol _i2i' i _ti ai bi txt = Some (_irms, _tables))
    (R: _rewrite zs tc pol i2i' i ti ai bi txt = Some (irms, tables)),
  SameLens irms _irms.
Proof.
  induction zs; intros; cbn in *; destruct_match_in _R; destruct_match_in R; try discriminate; inversion _R; inversion R; subst.
    intro. now destruct n.
    intro. destruct n; simpl. shelve. eapply IHzs. apply e3. apply e9.
  Unshelve.
  rename e6 into RI, e0 into _RI.
  clear -_RI RI.
  unfold rewrite_inst in *. destruct negb. easy. unfold goto_abort, rewrite_b, rewrite_bl, rewrite_b_bl in *.
  destruct (arm_decode a); destruct_match_in _RI; destruct_match_in RI;
    ( (apply rewrite_w_table_irm in _RI, RI; inversion _RI as [? [? [? _IRM]]]; inversion RI as [? [? [? IRM]]]) ||
      (apply wo_table_irm in _RI, RI; rename _RI into _IRM, RI into IRM);
      apply arm_assemble_all_cond_len in _IRM, IRM; simpl in _IRM, IRM; lia )
    || ( destruct_match_in _RI; destruct_match_in RI; inversion _RI; inversion RI; subst; easy ).
Qed.

Lemma samelens_len:
  forall {z1: list (list Z)} {z2}
    (SL: SameLens z1 z2),
    length z1 = length z2.
Proof.
  induction z1; intros.
    destruct z2.
      easy.
      specialize (SL O nil) as L0. specialize (SL O (1::nil)%Z). simpl in *. lia.
    destruct z2.
      specialize (SL O nil) as LL. specialize (SL O (1::nil)%Z). simpl in *. lia.
      simpl. erewrite IHz1. easy. unfold SameLens. apply (fun n => SL (S n)).
Qed.
Lemma len_cat_eq:
  forall A (l: list (list A)) l'
    (L: forall n d, length (nth n l d) = length (nth n l' d)),
  length (concat l) = length (concat l').
Proof.
  induction l; induction l'; intros.
    reflexivity.
    rewrite concat_cons, length_app, IHl'.
      specialize (L O nil). simpl in L. now rewrite <-L.
      intros. simpl. destruct n; apply (fun n => L (S n)).
    erewrite concat_cons, length_app, IHl.
      specialize (L O nil). simpl in L. now rewrite L.
      intros. simpl. destruct n; apply (fun n => L (S n)).
    rewrite !concat_cons, !length_app. apply f_equal2_plus. 
      now specialize (L O nil).
      apply IHl. apply (fun n => L (S n)).
Qed.
Lemma make_i_nth:
  forall {z's i' n d}
    (N: lt n (length z's)),
    nth n (make_i's z's (Z.of_N i')) d = Z.of_N (i' + N_len_cat_first n z's).
Proof.
  setoid_rewrite fix_make_i. induction z's; intros; subst.
    easy.
    destruct n; simpl.
      lia.
      rewrite <-nat_N_Z, <-N2Z.inj_add, IHz's, length_app. lia.
      simpl in N; lia.
Qed.
Lemma make_i_samelens:
  forall {z1 z2 i'}
    (SL: SameLens z1 z2),
  make_i's z1 i' = make_i's z2 i'.
Proof.
  setoid_rewrite fix_make_i. induction z1.
    intros. pose proof (samelens_len SL). symmetry in H. apply (length_zero_iff_nil) in H. now subst.
    intros. destruct z2. pose proof (samelens_len SL). simpl in H. lia.
      simpl. setoid_rewrite (SL O nil). erewrite IHz1. easy. unfold SameLens. apply (fun n => SL (S n)).
Qed.
Lemma make_i2i_samelens:
  forall {z1 z2 i i' ai}
    (SL: SameLens z1 z2),
  make_i2i' i i' ai z1 = make_i2i' i i' ai z2.
Proof.
  intros. cbv[make_i2i']. now rewrite !(make_i_samelens SL), !(len_cat_eq _ _ _ SL), (samelens_len SL).
Qed.
Lemma nlencatfirst_lt:
  forall A n (l: list (list A))
    (LT: lt n (length l))
    (NE: NonEmpty l),
    N_len_cat_first n l < N_len_cat l.
Proof.
  induction n; simpl.
    intros. destruct l. easy. inversion NE. subst. simpl. rewrite length_app. lia.
    destruct l.
      easy.
      rewrite !concat_cons, !length_app, !Nat2N.inj_add. specialize (IHn l0). simpl. intros. inversion NE. lia.
Qed.
Lemma nlencatfirst_le:
  forall {A} n (l: list (list A)),
    N_len_cat_first n l <= N_len_cat l.
Proof.
  induction n; simpl.
    lia.
    destruct l.
      easy.
      rewrite !concat_cons, !length_app, !Nat2N.inj_add. specialize (IHn l0). lia.
Qed.
Lemma nlencatfirst_s:
  forall {A n} {l: list (list A)} e
    (I: ith l n = Some e),
    N_len_cat_first (S n) l = N_len_cat_first n l + N_len e.
Proof.
  induction n. intros. rewrite firstn_O. destruct l. easy. inversion I. simpl. now rewrite app_nil_r.
    intros. destruct l. easy. destruct l0. easy. rewrite ith_cons in I. rewrite firstn_cons, concat_cons, length_app, Nat2N.inj_add. rewrite (IHn _ e). simpl. rewrite length_app. lia. easy.
Qed.
Lemma In_contains:
  forall z l, contains z l = true -> In z l.
Proof.
  intros. unfold contains in H. destruct_match_in H; try discriminate. apply find_some in e. destruct e. apply Z.eqb_eq in H1. now subst.
Qed.
Lemma ZNNat: forall n1 n2, (Z.of_N n1 + Z.of_nat n2)%Z = Z.of_N (n1 + N.of_nat n2). Proof. lia. Qed.

Lemma i2i'_first :
  forall irms bi bi' ai
    (IRM: lt O (length irms)),
    make_i2i' (Z.of_N bi) (Z.of_N bi') ai irms (Z.of_N bi) = Z.of_N bi'.
Proof.
  intros. cbv[make_i2i' get of_list].
  replace (orb _ _) with false by lia.
  rewrite make_i_nth. now rewrite Z.sub_diag, firstn_O, N.add_0_r.
  lia.
Qed.
Lemma i2i'_nth :
  forall irms bi bi' ai n
    (LT: lt n (length irms)),
    make_i2i' (Z.of_N bi) (Z.of_N bi') ai irms (Z.of_N (bi + N.of_nat n)) = Z.of_N (bi' + N_len_cat_first n irms).
Proof.
  intros. cbv[make_i2i' get of_list]. rewrite fix_make_i.
  replace (orb _ _) with false by lia. rewrite <-fix_make_i, make_i_nth. repeat f_equal. lia. lia.
Qed.

Lemma rewrite_no_table_overflow:
  forall {code tc pol i2i' i ti ai bi txt irms tables}
    (R: _rewrite code tc pol i2i' i (Z.of_N ti) ai bi txt = Some (irms, tables)),
  ti + N_len_cat tables < 2 ^ 30.
Proof.
  induction code; intros; cbn in R; destruct_match_in R; try discriminate; inversion R.
    simpl. lia.
    replace (Z.add (Z.of_N _) _) with (Z.of_N (ti + N.of_nat (length l0))) in e3 by lia.
    apply IHcode in e3. simpl. rewrite length_app. lia.
Qed.
Lemma rewrite_no_irm_overflow:
  forall {code tc pol i ti ai bi txt irms tables i'}
    (R: _rewrite code tc pol (make_i2i' (Z.of_N i) (Z.of_N i') ai irms) (Z.of_N i) (Z.of_N ti) ai bi txt = Some (irms, tables)),
  i' + N_len_cat irms < 2 ^ 30.
Proof.
  intros. destruct irms; try now apply rewrite_len in R.
  remember (make_i2i' _ _ _ _) as i2i'.
  assert (i2i' (Z.of_N i) = (Z.of_N i')). subst. apply i2i'_first. simpl; lia.
  assert (forall n, lt n (length (l::irms)) -> i2i' (Z.of_N (i + N.of_nat n)) = (Z.of_N (i' + N_len_cat_first n (l::irms)))). subst. apply i2i'_nth.
  clear Heqi2i'. revert R H H0.
  generalize code at 1, i, l, ti, irms, tables, tc, i'.
  induction code0.
    intros. cbn in R; destruct_match_in R; try discriminate. inversion R. rewrite H in e. simpl. lia.
    intros. cbn in R; destruct_match_in R; try discriminate.
      replace (_ + _)%Z with (Z.of_N (i0 + 1)) in e3 by (unfold Z1;lia).
      replace (_ + _)%Z with (Z.of_N (ti0 + N_len l2)) in e3 by lia.
      destruct l3. apply rewrite_len in e3. easy.
      inversion R. subst.
      apply IHcode0 with (i':=(i'0+N_len l0)) in e3. rewrite concat_cons, length_app. lia. specialize (H0 1%nat ltac:(simpl;lia)). simpl in H0. now rewrite app_nil_r in H0. intros. specialize (H0 (S n) ltac:(simpl in *;lia)). rewrite firstn_cons, concat_cons, length_app, <-Nat.add_1_l, Nat2N.inj_add, N.add_assoc in H0. simpl in H0. rewrite H0. lia.
Qed.
Lemma Forall_skipn{A}:
  forall n m (LE: le n m) P (l:list A) (F: Forall P (skipn n l)),
    Forall P (skipn m l).
Proof.
  setoid_rewrite Forall_forall.
  intros. apply F.
  destruct (Nat.le_exists_sub _ _ LE) as [k [M _]]; subst.
  rewrite <-skipn_skipn in H. rewrite <-(firstn_skipn k).
  apply in_or_app. now right.
Qed.

Section CFI.

Variable pol : Z -> list Z.
Variable code : list Z.
Variable bi bi' tbi ai en : N.
Variable irms tables : list (list Z).
Variable CFI_RW : cfi_rw pol code !bi !bi' !tbi !ai = Some (irms, tables).

Definition i2i' := make_i2i' !bi !bi' !ai irms.
Lemma RW : _rewrite code (fun _=>None) pol i2i' !bi !tbi !ai !bi code = Some (irms, tables).
Proof.
  unfold cfi_rw in CFI_RW. destruct_match_in CFI_RW; try easy.
  now rewrite (make_i2i_samelens (rw_i2i'_samelens CFI_RW e)) in CFI_RW.
Qed.

Lemma i2i'_oob_sb:
  forall j
    (J: (0 <= j)%Z)
    (AI: outofbounds irms bi' (ai*4) = true),
  outofbounds irms bi' (Z.to_N (i2i' j) * 4) || startsblock irms bi' (Z.to_N (i2i' j) * 4) = true.
Proof.
  intros. subst. cbv[i2i' make_i2i'].
  rewrite orb_true_iff.
  destruct orb eqn:e.
    destruct orb eqn:e1 in |- *; left; cbv[outofbounds] in *; lia.
    cbv[get of_list]. rewrite make_i_nth, N2Z.id, startsblock_firstn by lia. now right.
Qed.
Lemma i2i'_nonneg :
  forall i,
    (0 <= i)%Z <->
    (0 <= i2i' i)%Z.
Proof.
  intros. cbv[i2i' make_i2i' get of_list]. destruct orb eqn:E. destruct orb eqn:R in |-*. lia. lia.
  split; [|lia].
  edestruct Nat.lt_ge_cases as [LT|GE].
    apply Forall_nth;[|apply LT]. clear. rewrite fix_make_i. generalize bi'. induction irms.
      easy.
      simpl. constructor. lia. rewrite ZNNat. apply IHl.
    now rewrite (nth_overflow _ _ GE).
Qed.

Lemma no_irm_overflow: bi' + N_len_cat irms < 2 ^ 30. 
Proof.
  cbv[cfi_rw] in *; destruct_match_in CFI_RW; try easy.
  eapply rewrite_no_irm_overflow.
  erewrite make_i2i_samelens. apply CFI_RW. apply (rw_i2i'_samelens e CFI_RW).
Qed.
Lemma no_table_overflow: tbi + N_len_cat tables < 2 ^ 30.
Proof.
  cbv[cfi_rw] in *. destruct_match_in CFI_RW; try easy.
  eapply rewrite_no_table_overflow. apply CFI_RW.
Qed.

Definition i'2i i :=
  if outofbounds irms bi' (i*4)
  then i
  else bi + blockindex irms (i-bi').

Definition permitted_step '((x', _, (x, _)) : exit * store * (exit * store)) :=
  match x, x' with
  | Addr a, Addr a' =>
      exists i i',
        (* addresses must be aligned *)
        a = i * 4 /\
        a' = i' * 4 /\
        (
          i' = ai \/ (* destination is the abort *)
          i'2i i = i'2i i' \/ (* step within the same block *)
          In !(i'2i i') (pol !(i'2i i)) (* policy permitted step *)
        )
  | _, _ => True (* raising an exception is always allowed *)
  end.


(* store s contains list l in memory at index i with endianness e *)
Definition mem_has s l i e :=
  forall j n, ith l j = Some n ->
  !(s V_MEM32 [e | (i + N.of_nat j) * 4]) = n.
(* we call a store 's' valid if: *)
Definition flag_invs s :=
  (* s is in arm mode *)
  s R_T = 0 /\
  s R_JF = 0 /\
  (* s's endianness is en *)
  s R_E = en.
Definition mem_invs s :=
  (* s is a valid armv7 store *)
  models armc s /\
  (* the new code is in the correct location in memory with little endianness (decoding is unaffected by endianness) *)
  mem_has s (concat irms) bi' 0 /\
  (* the tables are in the correct location in memory with the initial endianness *)
  mem_has s (concat tables) tbi en /\
  (* the new code is nonwritable *)
  (xbits (s A_WRITE) (bi' * 4) ((bi' + N_len_cat irms) * 4) = 0) /\
  (* the tables are nonwritable *)
  (xbits (s A_WRITE) (tbi * 4) ((tbi + N_len_cat tables) * 4) = 0).
Definition store_invs s := flag_invs s /\ mem_invs s.
Definition hdP P (t:trace) :=
  match t with
  | (_, s)::_ => P s
  | _ => False
  end.
(* a trace is valid if the store of its head is valid *)
Remark hdPconj: forall P Q t, hdP (fun t => P t /\ Q t) t <-> hdP P t /\ hdP Q t.
Proof. destruct t. easy. now destruct p. Qed.
Remark vs_vs': forall s, store_invs s -> mem_invs s. Proof. intros. now destruct H. Qed.
Remark vs_vf: forall s, store_invs s -> flag_invs s. Proof. intros. now destruct H. Qed.
Hint Unfold store_invs : cfi.
Hint Resolve hdPconj vs_vs' vs_vf : cfi.
Remark vs_rt{s s'}: store_invs s' -> store_invs (reset_temps s s').
Proof. cbv[store_invs flag_invs mem_invs mem_has]. rewrite !reset_temps_not_temp by easy.
repeat split; try easy. now apply reset_temps_models. Qed.
Hint Resolve vs_rt : cfi.
(* if a prefix of the trace was valid, we only need to prove that the T, J, and E flags were unchanged *)
Lemma mem_invs_step:
  forall t0 x s
    (XP: exec_prog arm_prog ((x,s)::t0))
    (VS: hdP mem_invs t0),
  hdP mem_invs ((x,s)::t0).
Proof.
  intros. destruct t0; try easy. destruct p as [x0 s0].
  rewrite cons2 in XP. apply exec_prog_split in XP as [_ [_ XP]].
  destruct VS as [MDL [CODE [DATA [NWC NWD]]]].
  inversion XP. inversion H1. subst. clear H1 H2.
  pose no_irm_overflow; pose no_table_overflow.
  inversion LU; subst. remember (match s0 R_T with _ => _ end:arm_inst); clear Heqa0.
  apply (noassign_stmt_same A_WRITE) in XS as AW; [|apply noassign_awrite_arm2il]. 
  repeat split.
    eapply (preservation_exec_prog _ welltyped_arm_prog _ _ _ _ _ XP ltac:(easy) MDL).
    intros j n ITH. rewrite reset_temps_not_temp by easy. erewrite <-nonwritable_mem_arm2il. now apply CODE. apply XS. intros. rewrite testbit_xbits. remember ((bi'+N.of_nat j)*4). destruct (N.lt_decidable k (2^32)).
      pose proof (proj1 (ith_Some (concat irms) j) ltac:(now rewrite ITH)); destruct (N.lt_decidable k n0).
        pose proof(msub_wrap 32 k n0); lia.
        rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWC, xbits_0_l; easy || lia.
      rewrite xbits_above. easy. specialize (MDL A_WRITE _ ltac:(easy)). rewrite N.nlt_ge in H0. destruct (proj1 (N.lt_eq_cases _ _) H0); [transitivity (2^2^32)|]; try apply N.pow_lt_mono_r; now subst.
    intros j n ITH. rewrite reset_temps_not_temp by easy. erewrite <-nonwritable_mem_arm2il. now apply DATA. apply XS. intros. rewrite testbit_xbits. remember ((tbi+N.of_nat j)*4). destruct (N.lt_decidable k (2^32)).
      pose proof (proj1 (ith_Some (concat tables) j) ltac:(now rewrite ITH)); destruct (N.lt_decidable k n0).
        pose proof(msub_wrap 32 k n0); lia.
        rewrite msub_sub, N.mod_small in H by lia. erewrite xbits_inner, NWD, xbits_0_l; easy || lia.
      rewrite xbits_above. easy. specialize (MDL A_WRITE _ ltac:(easy)). rewrite N.nlt_ge in H0. destruct (proj1 (N.lt_eq_cases _ _) H0); [transitivity (2^2^32)|]; try apply N.pow_lt_mono_r; now subst.
    inversion AW. cbn; now rewrite <-H0.
    inversion AW. cbn; now rewrite <-H0.
Qed.

(* we have an invariant point: *)
Definition cfi_inv_point (t:trace) :=
   match t with
     (* whenever there is an exception, *)
   | (Raise i,s)::_ => true
       (* at any address outside the rewritten code, *)
       (* and at the start of each rewritten block *)
   | (Addr a,s)::_ => outofbounds irms bi' a || startsblock irms bi' a
   | _ => false
   end.
(* the invariants for a rewritten program:
   1) all steps so far are permitted
   2) the store of the head of the trace is valid *)
Definition cfi_inv t := Forall permitted_step (stepsof t) /\ hdP store_invs t.
Definition cfi_invs t := if cfi_inv_point t then Some (cfi_inv t) else None.

Definition cfi_exits (t:trace) :=
  match t with
  | (Addr a,_)::_ => outofbounds irms bi' a
  | _ => false
  end.

Lemma N_add_simpl_l : forall n m : N, n + m - n = m. Proof. lia. Qed.
Definition nonemptyirms := rewrite_nonempty RW.
Tactic Notation "lia:" constr(H) := (pose H; lia).
Tactic Notation "lia:" constr(H) constr(H1) := (pose H; pose H1; lia).

Remark sf_vf : forall s s', same_flags s s' -> flag_invs s -> flag_invs (reset_temps s s').
Proof. unfold flag_invs, same_flags. setoid_rewrite reset_temps_not_temp; try easy. lia. Qed.
Remark sf_rt : forall s s0 s', same_flags s s' -> same_flags s (reset_temps s0 s').
Proof. easy. Qed.
Remark vf_s' : forall s s', flag_invs s' -> flag_invs (reset_temps s s').
Proof. easy. Qed.
Hint Resolve sf_vf vf_s' sf_rt: cfi.

(* we can clear trace prefix t0 if we know its steps were permitted *)
Lemma cfi_clear_trace':
  forall xs t t0 b
    (NI: nextinv' arm_prog cfi_invs cfi_exits b (xs::t))
    (PS: Forall permitted_step (stepsof (startof t xs::t0))),
  nextinv' arm_prog cfi_invs cfi_exits b (xs::t++t0).
Proof.
  cofix IH; intros.
  destruct xs. inversion NI.
  - apply NIHere'.
    cbv[true_inv effinv effinv' cfi_exits cfi_invs] in TRU|-*.
    destruct cfi_inv_point, b, e, outofbounds; auto;
    (split; [rewrite app_comm_cons, stepsof_app, Forall_app; destruct t, t0|]);
    now inversion TRU.
  - eapply NIStep'.
      cbv[effinv effinv' cfi_invs cfi_exits] in NOI|-*.
        now destruct cfi_inv_point, b, outofbounds.
      apply IL.
      intros. subst. apply STEP in XS. rewrite app_comm_cons. apply IH.
        easy.
        now rewrite startof_cons.
Qed.
Lemma cfi_clear_trace:
  forall xs t t0 b
    (NI: nextinv arm_prog cfi_invs cfi_exits b (xs::t))
    (PS: Forall permitted_step (stepsof (startof t xs::t0))),
  nextinv arm_prog cfi_invs cfi_exits b (xs::t++t0).
Proof.
  intros. intro.
  apply cfi_clear_trace'; auto. apply NI. rewrite app_comm_cons in H. now apply exec_prog_split in H.
Qed.
(* since we can clear trace prefixes, we only ever need to deal with nextinv with single length traces*)
Definition cfi_nib b x s := nextinv arm_prog cfi_invs cfi_exits b ((x,s)::nil).
Definition cfi_ni := cfi_nib true.
Lemma CFIHere:
  forall x s
    (I: match x with
        | Addr a => outofbounds irms bi' a || startsblock irms bi' a = true
        | _ => True
        end)
    (VS: store_invs s),
  cfi_ni x s.
Proof.
  intros. intro. apply NIHere'.
  cbv[true_inv effinv cfi_invs cfi_inv_point].
  destruct x; now try rewrite I.
Qed.

Lemma mem_has_ith:
  forall {ll l b m s e}
    (J: ith ll m = Some l)
    (M: mem_has s (concat ll) b e),
  mem_has s l (b + N_len_cat_first m ll) e.
Proof.
  intros. intros j p ITH.
  specialize (M (j + length(concat(firstn m ll)))%nat p).
  rewrite ith_concat2 with (n:=m), Nat.add_sub in M by lia.
  rewrite ith_skipn_hd in J. destruct skipn. easy.
  inversion J.
  rewrite ith_concat1, H0 in M. apply M in ITH.
  rewrite <-ITH. do 2 f_equal. lia.
  subst. apply ith_Some. now rewrite ITH.
Qed.

Definition SafeE si a :=
  (!ai * 4 = a \/ exists di (D: (i2i' !di) * 4 = a), In !di (pol si))%Z.
Definition SafeP si t sr :=
  (0 <= sr < 32)%Z /\
  (0 <= t)%Z /\
  (Z.to_N t + 2 ^ (32 - Z.to_N sr) < 2 ^ 30) /\
  forall s n
    (VS: mem_invs s)
    (IB: Z.to_N t <= n < Z.to_N t + 2 ^ (32 - Z.to_N sr)),
  SafeE !si !(s V_MEM32 [ en | n*4 ]).
Lemma mjtm:
  forall j d sl sr x
    (D: (0 <= d)%Z)
    (M: d = make_jump_table_map (pol !j) (map i2i' (pol !j)) sl sr (fun _=>(!ai * 4)%Z) x),
  SafeE !j d.
Proof.
  intros. cbv[SafeE].
  induction (pol !j); simpl in M.
    now left.
    destruct orb.
      enough (0 <= a)%Z. right. repeat eexists. now rewrite M, Z2N.id. rewrite Z2N.id by easy. now left.
      cbv[Z4] in M. assert (0 <= i2i' a)%Z by lia. now apply i2i'_nonneg in H.
      apply IHl in M. destruct M. now left. right. destruct H as [? [? ?]]. exists x0, x1. now right.
Qed.
Lemma wo_table_tc':
  forall z' tc irm table tc'
    (WT: wo_table z' tc = Some (irm, table, tc')),
    tc = tc'.
Proof.
  intros. cbv[wo_table] in WT. destruct z'; now inversion WT.
Qed.
Definition SafeT (tc:TableCache) := forall j t sl sr (TC: tc (pol !j) = Some (t, sl, sr)), SafeP j t sr.
Lemma list_eqb_eq:
  forall a b, list_eqb a b = true <-> a = b.
Proof.
  induction a.
    split; now destruct b.
    split; simpl; intro; destruct b; try easy.
      destruct Z.eqb eqn:e in H; try easy. rewrite IHa in H. apply Z.eqb_eq in e. now subst.
      destruct Z.eqb eqn:e. rewrite IHa. now inversion H. inversion H. apply Z.eqb_neq in e. contradiction.
Qed.
Lemma find_sr_bound:
  forall dis dis' sl sr a, find_sr dis dis' sl sr = Some a -> (0 <= a <= sr)%Z.
Proof.
  intros until a. apply find_sr_ind.
    easy.
    intros. inversion H. lia.
    intros. unfold Z1 in *. apply H in H0. lia.
Qed.
Lemma find_hash_bound:
  forall dis dis' sl a b, find_hash dis dis' sl = Some (a, b) -> (0 <= b < 32)%Z.
Proof.
  intros until a. apply find_hash_ind.
    easy.
    intros. inversion H. subst. unfold Z31 in e0. apply find_sr_bound in e0. lia.
    intros. now apply H.
Qed.
Lemma mem_has_nonneg:
  forall {s l i e} (M: mem_has s l i e),
  Forall (Z.le Z0) l.
Proof.
  induction l. easy. intros. simpl. constructor. 2: apply (IHl (N.succ i) e).
  specialize (M O a eq_refl). lia.
  intros j m ITH. specialize (M (S j) m ITH). rewrite <-M. do 2 f_equal. lia.
Qed.
Lemma inmap2list:
  forall e m n (I: In e (map2list m n)),
    exists z, m z = e.
Proof.
  intros. rewrite map2list_fix in I. induction Z.to_nat. easy.
  destruct I. eexists. apply H. now apply IHn0.
Qed.
Lemma rewrite_w_table_st:
  forall irm tc j cond i irm' table tc' p
    (ITH: ith tables j = Some table)
    (RWT: rewrite_w_table irm tc (pol !(i+N.of_nat j)) i2i' cond !p !(tbi + N_len_cat_first j tables) !ai = Some (irm', table, tc'))
    (ST: SafeT tc),
    SafeT tc'.
Proof.
  intros. cbv[rewrite_w_table] in RWT. destruct_match_in RWT; try discriminate. inversion RWT; now subst.
  intros k t sl sr K. remember (Z.shiftl _ _). inversion RWT. subst tc'. clear RWT.
  destruct list_eqb eqn:q. shelve. eapply ST. apply K.
  Unshelve.
  inversion K.
  apply list_eqb_eq in q. repeat split; apply find_hash_bound in e0; try lia.
  rewrite N2Z.id. epose proof (make_jump_table_len _ _ _ _ _ _). subst z1.
  rewrite H1, H4, Z.shiftl_mul_pow2, Z.mul_1_l in H. unfold Z32 in H. replace (2^_) with (N_len table). 
  rewrite <-N.add_assoc, <-nlencatfirst_s by easy. pose proof (nlencatfirst_le (S j) tables). pose no_table_overflow. lia.
  rewrite H, Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. 
  replace (Z.to_N _) with 2 by lia. replace (Z.to_N _) with 32 by lia. lia. cbv[Z32]. lia.
  intros.
  remember (tbi + _) as ti.
  remember (N.to_nat (n - ti)) as m.
  assert (m < length table)%nat. subst. rewrite make_jump_table_len.
  cbv[Z1 Z32] in *. rewrite Z.shiftl_mul_pow2, Z.mul_1_l, Z2Nat.inj_pow, Z2Nat.inj_sub by lia.
  replace (Z.to_nat _) with 2%nat by lia. replace (Z.to_nat _) with 32%nat by lia. lia.
  pose proof (ith_nth' table m Z0 H). 
  destruct VS as [_ [_ [M _]]].
  pose proof (mem_has_ith ITH M m _ H5).
  replace n with (tbi + N_len_cat_first j tables + N.of_nat m) by lia. rewrite H6.
  apply ith_In in H5. remember (nth _ _ _) as d.
  pose proof (mem_has_nonneg (mem_has_ith ITH M)). rewrite Forall_forall in H7. specialize (H7 _ H5).
  subst table. cbv[make_jump_table] in H5. apply in_rev, inmap2list in H5.
  destruct H5. eapply mjtm. easy. symmetry. rewrite q. apply H1.
Qed.
Lemma skip_rewrite:
  forall n (N: le n (length code)),
  exists tc (ST: SafeT tc),
    _rewrite (skipn n code) tc pol i2i' !(bi+N.of_nat n) !(tbi+N_len_cat_first n tables) !ai !bi code
      = Some (skipn n irms, skipn n tables).
Proof.
  pose proof CFI_RW as CFI.
  cbv[cfi_rw] in CFI. destruct _rewrite eqn:E; try easy. destruct p.
  rewrite (make_i2i_samelens (rw_i2i'_samelens CFI E)) in CFI. clear E.
  induction n. intros. exists (fun _ => None). exists. easy. eqapply CFI. lia. now rewrite firstn_O, N.add_0_r.
  intros. specialize (IHn ltac:(lia)). destruct IHn as [tc [ST R]].
  destruct skipn eqn:SK. apply skipn_all3 in SK. lia.
  cbn in R. destruct_match_in R; try easy. exists t. exists. shelve. subst.
  inversion R; subst.
  rewrite <-Nat.add_1_l, <-!skipn_skipn, <-H0, <-H1, SK, !skipn_cons, !skipn_O. eqapply e3.
  cbv[Z1]. lia.
  rewrite (nlencatfirst_s l3). lia. now rewrite ith_skipn_hd, <-H1.
  Unshelve.
  inversion R. assert (ith tables n = Some l3) as ITH. now rewrite ith_skipn_hd, <-H1.
  clear -e0 ST ITH CFI_RW. rename e0 into RI.
  cbv[rewrite_inst goto_abort rewrite_b rewrite_bl rewrite_b_bl] in RI. destruct_match_in RI; try discriminate;
  (apply rewrite_w_table_st in RI || apply wo_table_tc' in RI || idtac); auto; inversion RI; try now subst.
Qed.

Section CFICases.
Variable tc tc' : TableCache.
Variable n : nat.
Variable z_orig : Z.
Variable irm table : list Z.

Definition i := bi + N.of_nat n.
Definition ti := tbi + N_len_cat_first n tables.
Definition i' := bi' + N_len_cat_first n irms.
Definition ni' := bi' + N_len_cat_first (S n) irms.

Variable RI : rewrite_inst tc i2i' z_orig (pol !i) !i !ti !ai !bi code = Some (irm, table, tc').
Variable ST: SafeT tc.
Variable IRM : ith irms n = Some irm.
Variable TABLE : ith tables n = Some table.
Variable SN : (S n < length irms)%nat.

Variable AI : ai < 2^30.
Variable AIB: outofbounds irms bi' (ai*4) = true.



Remark i'ni': ni' = i' + N_len irm.
Proof. cbv[i']. now rewrite <-N.add_assoc, <-nlencatfirst_s. Qed.
Hint Resolve i'ni' : cfi.

Remark CODE: forall s (VS: mem_invs s), mem_has s irm i' 0.
Proof. intros. apply mem_has_ith; auto. now destruct VS. Qed.
Remark DATA: forall s (VS: mem_invs s), mem_has s table ti en.
Proof. intros. apply mem_has_ith; auto. now destruct VS. Qed.
Ltac aauto := auto with *.
Remark nonemptyirm: lt O (length irm).
Proof.
  pose proof nonemptyirms. unfold NonEmpty in H.
  rewrite Forall_forall in H. apply (H _ (ith_In _ _ _ IRM)).
Qed.
Remark irmnotnil: irm <> nil.
Proof. pose proof nonemptyirm. now destruct irm. Qed.
Definition firstsnlt := (nlencatfirst_lt _ _ _ SN nonemptyirms).
Hint Resolve SN startsblock_firstn firstsnlt nonemptyirm irmnotnil : cfi.
Remark skiplt: lt n (length irms).
Proof. apply ith_Some. now rewrite IRM. Qed.
Definition firstnlt := (nlencatfirst_lt _ _ _ skiplt nonemptyirms).
Remark sbi: startsblock irms bi' (i'*4) = true.
Proof. cbv[i'];aauto. Qed.
Remark sbni: startsblock irms bi' (ni'*4) = true.
Proof. cbv[ni'];aauto. Qed.
Remark i'lt: i' < 2 ^ 30.
Proof. cbv[i']. lia: no_irm_overflow firstnlt. Qed.
Remark ni'lt: ni' < 2 ^ 30.
Proof. cbv[ni']. lia: no_irm_overflow firstsnlt. Qed.
Hint Resolve AIB sbi sbni sb_not_oob nonemptyirms nlencatfirst_s firstnlt i'lt ni'lt : cfi.
Lemma CFIStep:
  forall b j s q
    (VS: store_invs s)
    (Q: ith (map arm_decode irm) (N.to_nat j) = Some q)
    (STEP: forall c1 s1 x1
      (XS: exec_stmt armc s (arm2il ((i'+j)*4) q) c1 s1 x1)
      (VS: mem_invs (reset_temps s s1)),
      permitted_step ((exitof ((i'+N.succ j)*4) x1), (reset_temps s s1), (Addr ((i'+j)*4), s)) /\
      cfi_ni (exitof ((i'+N.succ j)*4) x1) (reset_temps s s1)),
  cfi_nib b (Addr ((i'+j)*4)) s.
Proof.
  clear SN. intros.
  assert (arm_prog s ((i'+j)*4) = Some (4, arm2il ((i'+j)*4) q)) as IL.
    unfold arm_prog. destruct VS as [[RT [RJ _]] VS]. rewrite RT, RJ, N.Div0.mod_mul.
    rewrite ith_map in Q. destruct (ith irm _) eqn:e.
    apply (CODE s VS) in e. rewrite N2Nat.id in e. cbv[LorB] in e. rewrite e. now inversion Q. easy.
  destruct (startsblock irms bi' ((i' + j) * 4) && b) eqn:B.
    apply andb_true_iff in B as [? ?]; subst. apply CFIHere. now rewrite H, orb_true_r. easy.
  intro XP. eapply NIStep'.
  - cbv[effinv cfi_invs effinv' cfi_exits cfi_inv_point].
    assert (N.to_nat j < length irm)%nat by (erewrite <-length_map; apply ith_Some; now rewrite Q).
    replace (outofbounds _ _ _) with false by (pose (nlencatfirst_le (S n) irms); pose i'ni'; cbv[outofbounds i' ni'] in *; lia).
    destruct b. rewrite andb_true_r in B. now rewrite B. now destruct startsblock.
  - apply IL.
  - intros. apply STEP in XS as [PS NI].
    + rewrite <-N.add_1_r, N.add_assoc, N.mul_add_distr_r in PS,NI.
      rewrite cons1. apply cfi_clear_trace'.
      now apply NI. rewrite stepsof_cons. now constructor.
    + eapply mem_invs_step. apply exec_prog_step. apply exec_prog_none.
      econstructor. apply IL. apply XS. now destruct VS.
Qed.
Definition cnd n cond := n + N.of_nat (Nat.b2n (cond <? 14))%Z.

Notation fa_vs P := (forall (s:store) (VS: store_invs s), P s) (only parsing).
Notation Goal := (fa_vs (cfi_nib false (Addr ((i'+0)*4)))) (only parsing). 
Lemma blockindex_inirm:
  forall j,
    lt j (length irm) ->
    blockindex irms (N_len_cat_first n irms + N.of_nat j) = N.of_nat n.
Proof.
  intros. rewrite <-(firstn_skipn n irms).
  rewrite ith_skipn_hd in IRM. destruct skipn. easy. inversion IRM. subst.
  rewrite firstn_app, length_firstn. replace (sub n _) with O by lia. rewrite firstn_O, app_nil_r, firstn_firstn, Nat.min_id.
  rewrite blockindex_app, length_firstn. simpl. replace (_<?_) with true by lia. lia.
Qed.
Lemma permitted_inirm:
  forall j k s s'
    (J: j < N_len irm)
    (K: k < N_len irm),
  permitted_step (Addr ((i'+k) * 4), s', (Addr ((i' + j) * 4), s)).
Proof.
  intros. repeat eexists. right. left. cbv[i'2i].
  cbv[outofbounds].
  assert (i' + j < ni' /\ i' + k < ni') by (rewrite i'ni'; lia).
  cbv[i' ni'] in *. do 2 replace (orb _ _) with false by lia: firstsnlt.
  replace (_ + _ - _) with (N_len_cat_first n irms + j) by lia.
  replace (_ + _ - _) with (N_len_cat_first n irms + k) by lia.
  now rewrite <-(N2Nat.id j), <-(N2Nat.id k), !blockindex_inirm by lia.
Qed.
Definition i'0 := eq_sym (N.add_0_r i').
Lemma i2i'2i :
  forall j,
    
  let k := i'2i (Z.to_N (i2i' !j)) in
  k = j \/ k = ai /\ Z.to_N (i2i' !j) = ai /\ outofbounds irms bi' (j*4) = false.
Proof.
  cbv[i2i' make_i2i' get of_list]. intros. destruct orb eqn:e.
    destruct orb eqn:e1 in |-*; cbv[i'2i outofbounds] in *; replace (orb _ _) with true by lia.
      left; lia.
      right; lia.
    cbv[i'2i outofbounds] in *. rewrite make_i_nth by lia. 
    remember (Z.to_nat _).
    replace (_||_) with false by lia: (nlencatfirst_lt _ n0 irms ltac:(lia) nonemptyirms).
    rewrite N2Z.id, N_add_simpl_l, blockindex_firstn by (pose nonemptyirms; now try lia). left; lia.
Qed.
Lemma i'2i_inirm:
  forall j (J: j < N_len irm),
  i'2i (i' + j) = i.
Proof.
  intros. cbv[i'2i]. assert (i' + j < ni') by lia: i'ni'.
  cbv[outofbounds i' ni'] in *. replace (orb _ _) with false by lia: firstsnlt.
  replace (_ + _ - _) with (N_len_cat_first n irms + j) by lia.
  now rewrite <-(N2Nat.id j), !blockindex_inirm by lia.
Qed.

Lemma permitted_abort:
  forall j s s',
    permitted_step (Addr (ai * 4), s', (Addr (j * 4), s)).
Proof.
  intros. repeat esplit. now left.
Qed.
Lemma permitted_safe:
  forall j a s s'
    (J: j < N_len irm)
    (SE: SafeE !i !a),
  permitted_step (Addr a, s', (Addr ((i' + j) *4), s)).
Proof.
  intros. destruct SE. replace a with (ai*4) by lia. repeat esplit. now left.
  destruct H as [? [? ?]]. replace a with (Z.to_N (i2i' !x) * 4) by lia. repeat esplit.
  destruct (i2i'2i x). rewrite H0, i'2i_inirm; aauto.
  destruct H0 as [_ [? _]]. now left.
Qed.
Lemma permitted_pol:
  forall j k s s'
    (J: j < N_len irm)
    (IN: In !(i'2i k) (pol !i)),
  permitted_step (Addr (k * 4), s', (Addr ((i' + j) * 4), s)).
Proof.
  intros. cbv[permitted_step]. repeat esplit.
  right. right.
  eqapply IN. cbv[i'2i].
  assert (i' + j < ni') by (rewrite i'ni'; lia).
  cbv[outofbounds i' ni'] in *. replace (orb _ _) with false by lia: firstsnlt.
  replace (_ + _ - _) with (N_len_cat_first n irms + j) by lia.
  now rewrite <-(N2Nat.id j), !blockindex_inirm by lia.
Qed.
Remark vfu:
  forall s v u, flag_invs s -> match v with | R_JF | R_T | R_E => False | _ => True end -> flag_invs (s[v := u]).
Proof. cbv[flag_invs]. intros. now destruct v. Qed.
Remark vfav:
  forall s v u, flag_invs s -> flag_invs (s[arm_varid v := u]).
Proof. cbv[flag_invs]. intros. unfold arm_varid. now destruct_match. Qed.
Remark i'i: i2i' !i = !i'.
Proof. clear SN. cbv[i2i' i]. rewrite i2i'_nth; auto. apply skiplt. Qed.
Hint Resolve vfu i'i vfav : cfi.
Lemma gotoz_ai_safe:
  forall z
  (Z: GOTOz true Z14 (i2i' !i) !ai = Some z)
  (IRM: irm = z::nil),
  Goal.
Proof.
  clear SN RI.
  intros. eapply CFIStep; aauto. now subst.
  intros.
  eapply exec_GOTOz in XS as [XS SF];[..|eqapply Z]; aauto.
  destruct XS; [|easy]. subst x1. split. apply permitted_abort. apply CFIHere; cbn; aauto. cbv[i']. lia: firstnlt no_irm_overflow. lia: i'i.
Qed.
Lemma goto_abort_safe: goto_abort (i2i' !i) !ai tc = Some (irm, table, tc') -> Goal.
Proof.
  clear SN.
  intros GA s VS. cbv[goto_abort] in GA; destruct_match_in GA; inversion GA.
  now eapply (gotoz_ai_safe z e).
Qed.
Lemma ni_in_pol: In !(i'2i ni') (pol !i).
Proof.
  cbv[rewrite_inst] in RI. destruct negb eqn:e. easy.
  rewrite negb_false_iff in e. apply In_contains in e.
  eqapply e. cbv[i'2i ni' i].
  rewrite sb_not_oob, N_add_simpl_l, blockindex_firstn by aauto.
  unfold Z1. lia.
Qed.



Lemma Cond:
  forall l cond
    (COND: arm_assemble_all_cond l cond = Some irm)
    (L: (0 < length l < 64)%nat)
    (PRE: fa_vs (cfi_nib (Z.ltb cond 14) (Addr ((cnd i' cond)*4)))),
  Goal.
Proof.
  intros. cbv[arm_assemble_all_cond] in COND. cbv[cnd] in PRE. destruct Z.ltb.
    apply arm_assemble_all_len in COND as LEN. simpl in LEN.
    apply arm_assemble_all_first in COND as [z [t [COND [ZT DECODE]]]].
    eapply CFIStep; aauto. now subst.
    intros. rewrite DECODE in XS.
      cbv[arm2il arm_b_il BranchWritePC arm_R] in XS.
      apply forget_cond in XS. cbn in XS. remember (_ mod _). remember (scast _ _ _).
      step_stmt XS. destruct XS. destruct (n2 mod _). step_stmt H. 
        destruct H as [[? ?] _]. subst x1. split. apply permitted_inirm; lia. 
        eqapply PRE. aauto. rewrite H in *; aauto.
      step_stmt H.
      assert (n0 ⊕ 8 ⊕ n1 .& 4294967292 = ni'*4) as E.
      {
        subst n0 n1.
        rewrite N.shiftl_mul_pow2, <-Z_nat_N, Z2Nat.inj_sub, Nat2Z.id, Nat2N.inj_sub, Z_nat_N by easy.
        cbn. rewrite N.mul_sub_distr_r. unfold scast. pose proof (toZ_nonneg). edestruct H1. rewrite H2.
        rewrite (N.mod_small _ (2^26)), N2Z.inj_sub, N2Z.inj_mul, nat_N_Z by lia. cbn. unfold ofZ. rewrite Z2N.inj_mod by lia. replace (Z.to_N (_ - _)) with (N.of_nat (length l) * 4 - 4) by lia. rewrite <-N.Div0.add_mod, N.add_0_r. rewrite (N.mod_small (i'*4)) by lia: i'lt.
        change 4294967296 with (2^32).
        rewrite N_land_mod_pow2_move by lia.
        change (_ mod _) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
        rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r, i'ni'. lia. apply N.log2_lt_pow2. lia. 
        lia: ni'lt i'ni'. enough (N.of_nat (length l) * 4 - 4 < 2^ 25). rewrite N.mod_small by lia. apply H4. lia.
      }
      rewrite E in H.
      destruct H as [[? ?] _]. subst x1.
      split. apply permitted_pol; aauto. now destruct irm. apply ni_in_pol.
      apply CFIHere; cbn; aauto. rewrite H in *; aauto.
  now apply PRE.
Qed.
Lemma safeinststep:
  forall inst j s b
    (VS: store_invs s)
    (ITH: ith (map arm_decode irm) (N.to_nat j) = Some inst)
    (SI: SafeInst inst)
    (NI: fa_vs (cfi_ni (Addr ((i' + N.succ j) * 4)))),
    cfi_nib b (Addr ((i' + j) * 4)) s.
Proof.
  intros.
  assert (N.to_nat j < length irm)%nat by (erewrite <-length_map; apply ith_Some; now rewrite ITH).
  eapply CFIStep; auto. apply ITH.
  intros. destruct x1. destruct e.
  - now apply (SI a) in XS.
  - apply (SI 0) in XS as [_ SF]. split. easy. apply CFIHere; now aauto.
  - apply (SI 0) in XS as [_ SF]. destruct (N.eq_dec j (N.pred (N_len irm))).
    + replace (i' + _) with ni' by (rewrite i'ni';lia). split.
      * apply permitted_pol. lia. apply ni_in_pol.
      * apply CFIHere; cbn; aauto.
    + split.
      * apply permitted_inirm. lia. lia.
      * apply NI. aauto.
Qed.
Lemma OnlyFallthru:
  forall m b
    (M: (m < length irm)%nat)
    (AS: Forall (fun z => SafeInst (arm_decode z)) (skipn m irm)),
  fa_vs (cfi_nib b (Addr ((i'+N.of_nat m)*4))).
Proof.
  intros m b M.
  remember (length irm - m)%nat.
  replace m with (length irm - n0)%nat by lia.
  assert (0 < n0 <= length irm)%nat by lia.
  clear Heqn0 M m; revert n0 b H.
  induction n0 as [|m]. easy.
  intros b M SI s VS.
  eapply safeinststep; auto.
    apply ith_nth' with (d:=arm_decode 0). rewrite length_map. lia.
    rewrite <-(Nat.add_0_r _), map_nth, Nat2N.id, <-nth_skipn.
      rewrite Forall_forall in SI. apply SI, nth_In. rewrite length_skipn. lia.
  intros. destruct m.
    replace (i' + _) with ni' by (rewrite i'ni';lia). apply CFIHere; cbn; aauto.
    rewrite <-Nat2N.inj_succ, <-Nat.sub_pred_r, Nat.pred_succ by lia.
      apply IHm; aauto. eapply Forall_skipn; [| apply SI]; lia.
Qed.
Lemma SingleFallthru:
  forall z (SI: SafeInst (arm_decode z)) (IRM: irm = z::nil), Goal.
Proof.
  intros. eqapply (OnlyFallthru O); aauto. subst. now constructor.
Qed.
Lemma skip_b2n_cond:
  forall {l cond l1}
    (C: arm_assemble_all_cond l cond = Some l1),
  skipn (Nat.b2n (cond <? 14)%Z) (map arm_decode l1) = l.
Proof.
  intros. cbv[arm_assemble_all_cond] in C. destruct Z.ltb;
  apply arm_assemble_all_eq in C; now rewrite C.
Qed.

Open Scope Z.
Open Scope N.
Ltac unZ := cbv[PC LR SP Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27 Z28 Z29 Z30 Z31 Z32 Z0xffff Z_4 Z_8] in *.
Tactic Notation "!" uconstr(x) "in" ident(H) :=
  (rewrite <-(Z2N.id x) in H; [|unZ;auto;try lia]).
Tactic Notation "!" uconstr(x) uconstr(y) "in" ident(H) :=
  (rewrite <-(Z2N.id x), <-(Z2N.id y) in H; [|unZ;auto;try lia..]).
Hint Resolve ldr_safe str_safe movw_safe movt_safe : cfi.
Lemma rewrite_pc_no_jump_safe:
  forall {si cond reg}
    (R: rewrite_pc_no_jump si cond !i reg tc = Some (irm, table, tc'))
    (REG: (0 <= reg < 15)%Z)
    (SI: SafeInst si),
  Goal.
Proof.
  intros. cbv[rewrite_pc_no_jump wo_table] in R. destruct_match_in R; try discriminate.
  inversion R.
  eapply Cond; auto. eqapply e; auto. cbn;lia.
  intros. apply OnlyFallthru; auto. apply arm_assemble_all_cond_len in e. simpl in e. subst. lia.
  rewrite <-Forall_map, <-skipn_map, <-H0, (skip_b2n_cond e).
  now repeat (constructor; [aauto|]).
Qed.
Lemma mov_safe:
  forall rd rm
  (RT: (rd <> 15%Z)),
  SafeInst (MOV rd rm).
Proof.
  intros. apply safe;
  repeat constructor; try discriminate; replace (_ =? _) with false by lia;
  repeat constructor; auto with cfi; easy.
Qed.
Hint Resolve mov_safe: cfi.
Lemma ldm_safe:
  forall op cond W Rn register_list
    (R: N.testbit (Z.to_N register_list) 15 = false),
  SafeInst (ARM_lsm op cond W Rn register_list).
Proof.
  intros. apply safe; destruct op; repeat constructor; try discriminate;
  rewrite R; repeat (constructor || discriminate || lia || destruct_match_eqn || auto with cfi);
  apply for_noassign || apply for_0_14_noje; intros; repeat constructor; try discriminate; auto with cfi.
Qed.
Lemma stm_safe:
  forall op cond W Rn register_list
    (OP: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => True | _ => False end),
  SafeInst (ARM_lsm op cond W Rn register_list).
Proof.
  intros. apply safe; destruct op; repeat constructor; try discriminate;
  repeat (constructor || discriminate || lia || destruct_match_eqn || auto with cfi);
  apply for_noassign || apply for_0_14_noje; intros; repeat constructor; try discriminate; auto with cfi.
Qed.
Lemma rewrite_pc_sp_no_jump_safe:
  forall {si cond reg reg2}
    (R: rewrite_pc_sp_no_jump si cond !i reg reg2 tc = Some (irm, table, tc'))
    (REG: (0 <= reg < 15)%Z)
    (REG2: (0 <= reg2 < 15)%Z)
    (SI: SafeInst si),
  Goal.
Proof.
  intros. cbv[rewrite_pc_sp_no_jump wo_table] in R. destruct_match_in R; try discriminate.
  inversion R.
  eapply Cond; auto. eqapply e; auto. cbn;lia.
  intros. apply OnlyFallthru; auto. apply arm_assemble_all_cond_len in e. simpl in e. subst. lia.
  rewrite <-Forall_map, <-skipn_map, <-H0, (skip_b2n_cond e).
  repeat (constructor; [aauto;apply ldm_safe|]); auto;
  now rewrite Z2N_inj_lor, !Z2N_inj_shiftl, N.lor_spec, !N.shiftl_mul_pow2, !N.mul_1_l, !N.pow2_bits_false by (unZ; try apply Z.shiftl_nonneg; lia).
Qed.

Lemma rewrite_w_table_safe:
  forall {irmf cond}
    (R: rewrite_w_table irmf tc (pol !i) i2i' cond !i !ti !ai = Some (irm, table, tc'))
    (I: forall t sl sr
      (IRMF: irmf cond !i t sl sr = Some irm)
      (SF: SafeP i t sr),
      Goal),
    Goal.
Proof.
  intros. apply rewrite_w_table_st in R as ST2; auto. cbv[rewrite_w_table] in R. destruct_match_in R; try discriminate; subst.
  eapply I;auto. inversion R; subst. apply e2. eapply ST. apply e.
  remember (make_jump_table _ _ _ _ _ _). inversion R. subst l. 
  eapply I; auto. apply e2. subst tc'. eapply (ST2 _). epose proof (proj2 (list_eqb_eq _ _) eq_refl). now rewrite H.
Qed.

Remark mdlvs: forall s, mem_invs s -> models armc s.
Proof. intros. now destruct H. Qed.
Hint Resolve mdlvs : cfi.
Remark cndadd: forall a b c, cnd a b + c = a + cnd c b.
Proof. cbv[cnd]. lia. Qed.

Remark vs_vs'_vf:forall s, mem_invs s -> flag_invs s -> store_invs s.
Proof. easy. Qed.
Hint Resolve vs_vs'_vf : cfi.
Lemma cond_ith: forall {l cond} (C: arm_assemble_all_cond l cond = Some irm) j,
  ith (map arm_decode irm) (N.to_nat (cnd j cond)) = ith l (N.to_nat j).
Proof.
  cbv[cnd].
  intros. cbv[arm_assemble_all_cond] in C. destruct Z.ltb.
  apply arm_assemble_all_first in C as [z [t [C [ZT DECODE]]]].
  now rewrite ZT, map_cons, (arm_assemble_all_eq _ _ C), N.add_1_r, N2Nat.inj_succ, ith_cons.
  now rewrite (arm_assemble_all_eq _ _ C), N.add_0_r.
Qed.
Remark cnds: forall a b, N.succ (cnd a b) = cnd (N.succ a) b.
Proof. cbv[cnd]. lia. Qed.
Remark update_cancel2: forall (s:store) v n v' n' n0,
  v <> v' -> s[v' := n0][v := n][v' := n'] = s[v' := n'][v := n].
Proof.
  intros. now rewrite update_swap, update_cancel by easy.
Qed.
Remark update_cancel2': forall (s:store) v n v' n' n0,
  v <> v' -> s[v' := n0][v := n][v' := n'] = s[v := n][v' := n'].
Proof.
  intros. now rewrite update_swap, update_cancel, update_swap by easy.
Qed.
Ltac vs H := match type of H with
             | mem_invs ?x => let VS := fresh "VS" in assert (store_invs x) as VS; [| clear H; rename VS into H]
             end.
Lemma add4:
  forall b j s reg v after
    (VS: store_invs s)
    (AA: firstn 5 (skipn (N.to_nat j) (map arm_decode irm)) = arm_add !reg !v ++ after::nil)
    (R: reg < 15)
    (A: let s' := s[R_PC := ((i'+(j+3))*4) mod 2^32][arm_varid reg := s (arm_varid reg) ⊕ v] in
      store_invs s' -> cfi_ni (Addr ((i'+(j+4))*4)) s'),
  cfi_nib b (Addr ((i'+j)*4)) s.
Proof.
  intros.
  epose proof (length_firstn 5 _) as LEN. rewrite AA, length_skipn, length_map in LEN. simpl length in LEN.
  unfold arm_add in AA. unZ. rewrite !zxbits_eq in AA.

  eapply CFIStep; auto.
  now rewrite <-(Nat.add_0_r _), <-ith_skipn, <-(firstn_skipn 5 _), AA.
  intros. !4%Z (Z_xbits _ _ _) in XS; [|apply Z_xbits_nonneg].
  apply exec_add in XS as [S1 X]; try lia; [|rewrite Z2N_xbits by lia; apply xbits_bound]. subst x1.
  split. apply permitted_inirm; lia.
  vs VS0. rewrite S1 in *; aauto.

  eapply CFIStep; auto.
  now rewrite N2Nat.inj_succ, <-Nat.add_1_r, <-ith_skipn, <-(firstn_skipn 5 _), AA.
  intros. !8%Z (Z_xbits _ _ _) in XS; [|apply Z_xbits_nonneg].
  apply exec_add in XS as [S2 X]; try lia; [|rewrite Z2N_xbits by lia; apply xbits_bound]. subst x1.
  split. apply permitted_inirm; lia.
  rewrite reset_temps_overwrite_l in *. vs VS1. rewrite S2 in *; aauto.

  eapply CFIStep; auto.
  now rewrite !N2Nat.inj_succ, <-(Nat.add_0_r (N.to_nat _)), !plus_n_Sm, <-ith_skipn, <-(firstn_skipn 5 _), AA.
  intros. !12%Z (Z_xbits _ _ _) in XS; [|apply Z_xbits_nonneg].
  apply exec_add in XS as [S3 X]; try lia; [|rewrite Z2N_xbits by lia; apply xbits_bound]. subst x1.
  split. apply permitted_inirm; lia.
  rewrite reset_temps_overwrite_l in *. vs VS2. rewrite S3 in *; aauto.

  eapply CFIStep; auto.
  now rewrite !N2Nat.inj_succ, <-(Nat.add_0_r (N.to_nat _)), !plus_n_Sm, <-ith_skipn, <-(firstn_skipn 5 _), AA.
  intros. replace (Z_xbits _ _ _) with (Z.lor (Z.shiftl !0 8) !(xbits v 0 8)) in XS by now rewrite N2Z_xbits.
  apply exec_add in XS as [S4 X]; try lia; [|apply xbits_bound]. subst x1.
  split. apply permitted_inirm; lia.
  rewrite reset_temps_overwrite_l in *. simpl.

  assert (reset_temps s s3 = s[R_PC := (i' + (j + 3)) ⊗ 4][arm_varid reg := s (arm_varid reg) ⊕ v]).
  rewrite S4, S3, S2, S1, N2Z.id, !update_updated, !update_cancel2 by aauto. f_equal. f_equal. lia.

  clear.
  rewrite ! N.Div0.add_mod_idemp_l, <-N.add_assoc, N.Div0.add_mod_idemp_l, <-!N.add_assoc.
  apply N_add_mod_eq_l. rewrite !Z2N_xbits by (apply N2Z.is_nonneg || lia). rewrite !N2Z.id. cbv [Z.to_N N.mul Pos.mul]. simpl N.sub. 
  rewrite (N.shiftl_mul_pow2 _ 32), N.Div0.mod_mul, N.lor_0_r.
  erewrite <-(N.mod_small (_>>8)), <-(N.mod_small (_>>16)), <-(N.mod_small (_>>24)), <-(N.mod_small (_>>0)), <-!N_lor_mod_pow2.
  rewrite !N.add_assoc. repeat rewrite !N.Div0.add_mod_idemp_r, N.add_comm, !N.add_assoc.
  apply N.bits_inj. intro. 
  destruct (N.lt_ge_cases n (32)).
  rewrite !N.mod_pow2_bits_low by assumption.
  rewrite 3 shiftr_low_pow2, !N.lor_0_l. rewrite <-!lor_plus, !N.lor_spec.
  rewrite !xbits_equiv, <-!N.ldiff_ones_r, !N.ldiff_spec, !N.shiftr_0_r, !N_ones_spec_ltb.
  destruct (N.lt_ge_cases n 8).
    repeat replace (_ <? _) with true by lia.
    now rewrite !andb_false_r, N.mod_pow2_bits_low.
  destruct (N.lt_ge_cases n 16).
    repeat replace (_ <? _) with true by lia. replace (_ <? _) with false by lia.
    now rewrite !andb_false_r, N.mod_pow2_bits_low, N.mod_pow2_bits_high, andb_true_r, orb_false_r.
  destruct (N.lt_ge_cases n 24).
    replace (_ <? _) with true by lia. repeat replace (_ <? _) with false by lia.
    now rewrite !andb_false_r, !andb_true_r, N.mod_pow2_bits_low, !N.mod_pow2_bits_high, !orb_false_r by easy.
    repeat replace (_ <? _) with false by lia.
    now rewrite N.mod_pow2_bits_low, !N.mod_pow2_bits_high, !andb_true_r, !orb_false_r by easy.
  apply N.bits_inj_0. intro. rewrite N.land_spec.
  destruct (N.lt_ge_cases n0 24).
    now rewrite N.shiftl_spec_low, andb_false_l by lia.
    unfold xbits. now rewrite (N.shiftl_spec_high' _ 16), N.mod_pow2_bits_high, andb_false_r by lia.
  apply N.bits_inj_0. intro. rewrite N.land_spec, andb_false_iff. 
  destruct (N.lt_ge_cases n0 16).
    change 24 with (8+16). rewrite <- N.shiftl_shiftl, Nshiftl_add_distr, N.shiftl_spec_low by easy. now left.
    rewrite !xbits_equiv, N.shiftl_spec_high', N.shiftr_spec', N.mod_pow2_bits_high by lia. now right.
  apply N.bits_inj_0. intro. rewrite N.land_spec, andb_false_iff.
  destruct (N.lt_ge_cases n0 8).
    change 16 with (8+8). change 24 with (16+8). rewrite <-!N.shiftl_shiftl, !Nshiftl_add_distr, N.shiftl_spec_low by easy. now left.
    unfold xbits. rewrite N.shiftr_0_r, N.mod_pow2_bits_high by lia. now right.
     pose proof (xbits_bound v 8 16). simpl in H0. lia.
     pose proof (xbits_bound v 16 24). simpl in H0. lia.
     apply xbits_bound.
     now rewrite !N.mod_pow2_bits_high by assumption.
     pose proof (xbits_bound v 0 8). simpl in *. lia.
     pose proof (xbits_bound v 8 16). pose proof (N.shiftr_upper_bound (xbits v 8 16) 24). simpl in H. lia.
     pose proof (xbits_bound v 16 24). pose proof (N.shiftr_upper_bound (xbits v 16 24) 16). simpl in H. lia.
     pose proof (xbits_bound v 24 32). pose proof (N.shiftr_upper_bound (xbits v 24 32) 8). simpl in H. lia.

  eqapply A. lia. easy. split. aauto. rewrite <-H. aauto.
Qed.

Lemma tablelookup:
  forall b j s t_ sl sr reg after
  (VS: store_invs s)
  (TL: firstn 8 (skipn (N.to_nat j) (map arm_decode irm)) = arm_table_lookup !t_ sl !sr !reg ++ after::nil)
  (SR: sr < 32)
  (TB: t_ + 2 ^ (32 - sr) < 2 ^ 30)
  (REG: reg < 15)
  (A: forall k,
    t_ <= k < t_ + 2 ^ (32 - sr) ->
    let s' := s[R_PC := (i'+(j+6)) ⊗ 4][arm_varid reg := s V_MEM32 [en | k*4 ]] in
    store_invs s' -> cfi_ni (Addr ((i'+(j+7))*4)) s'),
  cfi_nib b (Addr ((i'+j)*4)) s.
Proof.
  intros.
  epose proof (length_firstn 8 _) as LEN. rewrite TL, length_skipn, length_map in LEN. simpl length in LEN.

  eapply CFIStep; auto.
  now rewrite <-(Nat.add_0_r _), <-ith_skipn, <-(firstn_skipn 8 _), TL.
  intros.
  apply UBFX_bound in XS as [t [S1 [T X1]]]; [|lia..]. subst x1.
  split. eapply permitted_inirm; lia.
  vs VS0. rewrite S1 in *; split; aauto.

  eapply CFIStep; auto.
  now rewrite N2Nat.inj_succ, <-Nat.add_1_r, <-ith_skipn, <-(firstn_skipn 8 _), TL.
  intros.
  apply exec_lsl in XS as [S2 X]; auto. subst x1.
  split. eapply permitted_inirm; lia.
  vs VS1. rewrite S2 in *; aauto.

  eapply add4. aauto. rewrite !N2Nat.inj_succ, <-(Nat.add_0_l (N.to_nat _)), <-!plus_Sn_m, <-skipn_skipn, firstn_skipn_comm.
  replace (_ + _)%nat with (min 7 8) by lia. rewrite <-firstn_firstn, TL, firstn_app, firstn_all2, firstn_O, app_nil_r by easy.
  unfold arm_table_lookup. unZ. rewrite skipn_app, skipn_all2, app_nil_l, skipn_O by easy. do 2 f_equal. rewrite N2Z.inj_mul, Z2N.id. easy. lia. lia.
  intros.

  eapply CFIStep; auto.
  now rewrite !N.add_succ_comm, N2Nat.inj_add, <-ith_skipn, <-(firstn_skipn 8 _), TL.
  intros.
  apply exec_ldr in XS as [S3 X]; [|aauto..]. subst x1.
  split. eapply permitted_inirm; lia.
  vs VS2. rewrite S3 in *; aauto. simpl.

  assert (reset_temps s' s2 = s[R_PC := (i' + (j + 6)) ⊗ 4][arm_varid reg := s V_MEM32 [en | (t mod 2 ^ (32 - 2) + t_) mod 2 ^ (32 - 2) * 4 ]]).
  subst s'. rewrite S3, S2, S1, N2Z.id, reset_temps_update_r, reset_temps_id, !update_cancel2 by aauto.
  rewrite !update_updated, !update_frame by aauto. f_equal. f_equal. lia. f_equal. f_equal. now destruct VS, H0, H2.
  rewrite <-(xbits_0_i (_<<_)), xbits_shiftl, xbits_0_i, N.mul_comm, N.shiftl_mul_pow2, <-N.mul_add_distr_r.
  now rewrite <-(N.shiftl_mul_pow2 _ 2), <-xbits_0_i, xbits_shiftl, xbits_0_i, N.shiftl_mul_pow2. 
  rewrite H0. eqapply A. lia. rewrite N.mod_small.
  lia: (N.Div0.mod_le t (2^(32-2))). etransitivity. 2: apply TB. lia: (N.Div0.mod_le t (2^(32-2))). 
  now rewrite <- H0.
Qed.
Lemma reset_temps_armv:
  forall s s' n, reset_temps s s' (arm_varid n) = s' (arm_varid n).
Proof.
  intros. unfold arm_varid. now destruct_match_eqn.
Qed.
Tactic Notation "forget" uconstr(x) := (let n := fresh "n" in set (n:=x) in *; clearbody n).
Lemma at_safe:
  forall si a s
   (VS: store_invs s)
   (SE: SafeE si !a),
  cfi_ni (Addr a) s.
Proof.
  intros. apply CFIHere. inversion SE. replace a with (ai*4) by lia. now rewrite AIB.
  destruct H as [? [? ?]]. replace a with (Z.to_N (i2i' !x) * 4) by lia. apply (i2i'_oob_sb); aauto. easy.
Qed.
Lemma safe_div4:
  forall si a (SE: SafeE si !a),
  (4 | a).
Proof.
  intros. inversion SE. exists ai. lia. destruct H as [? [? ?]]. exists (Z.to_N (i2i' !x)). lia.
Qed.
Lemma rewrite_pc_safe:
  forall {si cond reg}
    (R: rewrite_pc si reg tc (pol !i) i2i' cond !i !ti !ai = Some (irm, table, tc'))
    (REG: (0 <= reg < 13)%Z)
    (SI: SafeInst si),
  Goal.
Proof.
  intros.
  rewrite <-(Z2N.id reg) in R by lia. remember (Z.to_N reg) as r. assert (r < 13) by lia. clear Heqr reg REG. rename r into reg, H into REG.
  eapply rewrite_w_table_safe; auto. apply R.
  intros. cbv[pc_irm] in IRMF.
  eapply Cond; auto. apply IRMF. simpl. lia.
  intros.
  pose proof (ITH:=cond_ith IRMF).
  apply arm_assemble_all_cond_len in IRMF as LEN. simpl in LEN.

  rewrite <-(N.add_0_r (cnd _ _)), cndadd.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  easy. clear s0 VS0 s1 VS1 s2 VS2 s3 VS3 s4 VS4 VS.

  intros. rewrite cnds. simpl N.succ.
  eapply tablelookup; auto. erewrite <-(N.add_0_r (cnd _ _)), cndadd, N2Nat.inj_add, <-skipn_skipn. cbv[cnd]. rewrite N.add_0_l, Nat2N.id, (skip_b2n_cond IRMF).
  rewrite skipn_app, skipn_all2, app_nil_l, skipn_O, firstn_app, firstn_all2 by (simpl length;lia). simpl sub. rewrite firstn_cons, firstn_O, !Z2N.id. easy.
  all: try solve [destruct SF; lia].
  intros. replace (_ + 7) with (cnd 11 cond) by (unfold cnd;lia).
  assert (reg < 15) by lia.

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  apply exec_align in XS as [S1 X]; [|aauto]. subst x1.
  split. apply permitted_inirm; cbv[cnd]; lia.
  vs VS0. rewrite S1 in *; aauto. forget (reset_temps _ _). subst s'. rewrite !N2Z.id, update_cancel2 in S1 by aauto. forget (((_ + cnd _ _) * 4) mod _).
  rewrite !update_frame in S1 by aauto.

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds in *. simpl N.succ.
  !SP in XS. change Z_8 with (-!8) in XS. apply exec_str in XS as [S2 X]; [|unZ; lia || aauto..]. subst x1.
  split. apply permitted_inirm; cbv[cnd]; lia.
  vs VS1. rewrite S2 in *; aauto. forget (reset_temps _ _).
  rewrite S1, !update_frame, !update_updated, !update_frame, !update_updated in S2 by (unfold arm_varid; destruct_match;discriminate).
  rewrite (update_swap _ R_SP R_PC), update_cancel2' in S2 by aauto. replace (s0 R_E) with en in S2 by now destruct VS as [[? [? ?]] ?].
  forget (_ >> 2). remember (s0 _ [ _ | _ ] ). forget ((_ + cnd 12 _)  ⊗ 4).
  
  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  ! SP in XS. change Z_4 with (-!4) in XS. apply exec_ldr' in XS as [S3 X]; [|unZ; lia..]. subst x1.
  split. apply permitted_inirm; cbv[cnd]; lia.
  vs VS2. rewrite S3 in *; aauto. forget (reset_temps _ _). forget (n2 _ [ _ | _ ]). forget ((_ + cnd 13 _)  ⊗ 4).
  rewrite S2 in S3.

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  simpl arm_varid in *. rewrite 2(update_swap _ _ R_PC), 4(update_swap _ _ (arm_varid _)), !update_cancel in S3 by aauto.
  eenough (SafeE !i _).
  apply exec_ldrpc in XS as [X S4]; [..|rewrite S3, update_frame, update_updated by discriminate; now eexists].
   subst x1. split. apply permitted_safe. cbv[cnd];lia. apply H2.
   apply (at_safe !i);auto. rewrite S4 in *; aauto.
   apply (safe_div4 !i);auto.
  replace (n6 R_E) with en in * by now destruct VS2 as [[? [? ?]] ?]. rewrite S3. rewrite update_updated, update_frame, update_updated, getmem_setmem, Heqn4 by discriminate.
  rewrite N.mod_small by apply typesafe_getmem. apply SF; aauto.
Qed.
Lemma rewrite_pc_sp_safe:
  forall {si cond reg reg2}
    (R: rewrite_pc_sp si reg reg2 tc (pol !i) i2i' cond !i !ti !ai = Some (irm, table, tc'))
    (REG: (0 <= reg < reg2)%Z)
    (REG2: (0 <= reg2 < 15)%Z)
    (SI: SafeInst si),
  Goal.
Proof.
  intros. 
  rewrite <-(Z2N.id reg), <-(Z2N.id reg2) in R by lia. remember (Z.to_N reg) as r. remember (Z.to_N reg2) as r2.
  assert (r < r2) by lia. assert (r2 < 15) by lia. clear Heqr Heqr2 reg reg2 REG REG2. rename r into reg, r2 into reg2, H into REG, H0 into REG2.
  eapply rewrite_w_table_safe; auto. apply R.
  intros. cbv[pc_sp_irm] in IRMF.
  eapply Cond; auto. apply IRMF. simpl. lia.
  intros.
  pose proof (ITH:=cond_ith IRMF).
  apply arm_assemble_all_cond_len in IRMF as LEN. simpl in LEN.

  rewrite <-(N.add_0_r (cnd _ _)), cndadd.
  eapply safeinststep; auto. now rewrite ITH.
  now apply stm_safe.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  easy. clear s0 VS0 s1 VS1 s2 VS2 s3 VS3 s4 VS4 s5 VS5 VS.

  intros. rewrite cnds. simpl N.succ.
  eapply tablelookup; auto. erewrite <-(N.add_0_r (cnd _ _)), cndadd, N2Nat.inj_add, <-skipn_skipn. cbv[cnd]. rewrite N.add_0_l, Nat2N.id, (skip_b2n_cond IRMF).
  rewrite skipn_app, skipn_all2, app_nil_l, skipn_O, firstn_app, firstn_all2 by (simpl length;lia). simpl sub. rewrite firstn_cons, firstn_O, !Z2N.id. easy.
  all: try solve [destruct SF; lia].
  intros. replace (_ + 7) with (cnd 12 cond) by (unfold cnd;lia).

  assert (reg < 15) by lia.
  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  change Z_4 with (-!4) in XS. apply exec_str in XS as [S1 X]; [|lia||aauto..]. subst x1.
  split. apply permitted_inirm; cbv[cnd]; lia.
  vs VS0. rewrite S1 in *; aauto. forget (reset_temps _ _). subst s'. rewrite !N2Z.id, update_cancel2 in S1 by aauto. forget (((_ + cnd _ _) * 4) mod _).
  rewrite update_updated in S1.
  rewrite !update_frame in S1 by aauto.
  replace (s0 R_E) with en in S1 by now destruct VS as [[? [? ?]] ?].
  remember (s0 _ [ _ | _ ]).

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  assert(SafeE !i !(n0 V_MEM32 [n0 R_E | n0 (arm_varid reg2) ⊖ 4 ])).
  replace (n0 R_E) with en by now destruct VS0 as [[? [? ?]] ?].
  rewrite S1, update_updated, !update_frame, getmem_setmem by (aauto;lia). subst n2.
  rewrite N.mod_small by apply typesafe_getmem. apply SF; aauto.
  apply exec_ldmdb3 in XS; [|lia || now apply (safe_div4 !i)..].
  destruct XS as [[X S]|[X S]]. subst x1.
  split. apply permitted_safe; auto; cbv[cnd]; lia.
  apply (at_safe !i); aauto. subst x1.
  split. easy. apply CFIHere; cbn; aauto.
Qed.
Lemma rewrite_bx_blx_safe:
  forall {l reg cond}
    (R: rewrite_bx_blx l reg tc (pol !i) i2i' cond !i !ti !ai = Some (irm, table, tc'))
    (REG: (0 <= reg < 15)%Z),
  Goal.
Proof.
  intros. eapply rewrite_w_table_safe; auto. apply R.
  intros. cbv[bx_blx_irm] in IRMF.
  eapply Cond; auto. apply IRMF. simpl. lia.
  intros.
  pose proof (ITH:=cond_ith IRMF).
  apply arm_assemble_all_cond_len in IRMF as LEN. simpl in LEN.

  rewrite <-(N.add_0_r (cnd _ _)), cndadd.
  eapply tablelookup; auto. erewrite <-(N.add_0_r (cnd _ _)), cndadd, N2Nat.inj_add, <-skipn_skipn. cbv[cnd]. rewrite N.add_0_l, Nat2N.id, (skip_b2n_cond IRMF).
  rewrite skipn_O, firstn_app, firstn_all2 by (simpl length;lia). simpl sub. rewrite firstn_cons, firstn_O, !Z2N.id. easy.
  all: try solve [destruct SF; lia].
  intros. replace (_ + 7) with (cnd 7 cond) by (unfold cnd;lia).

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  
  enough (SafeE !i !(s' (arm_varid (Z.to_N reg)))).
  enough (x1 = Some (Addr (s' (arm_varid (Z.to_N reg)))) /\ same_flags s' s2).
  destruct H2. subst x1.
  split. apply permitted_safe; auto; cbv[cnd]; lia.
  apply (at_safe !i); aauto.
  destruct l; !reg in XS. apply exec_blx in XS; aauto. lia. now apply (safe_div4 !i).
  apply exec_bx in XS; aauto. lia. now apply (safe_div4 !i).
  subst s'. rewrite update_updated. apply SF; aauto.
Qed.
Lemma i2i'_max :
  forall i,
    (i2i' i <= Z.max (Z.max !ai i) !(bi' + N_len_cat irms))%Z.
Proof.
  intros. cbv[i2i' make_i2i' get of_list]. destruct orb. destruct orb; lia.
  edestruct Nat.lt_ge_cases as [LT|GE]; [|rewrite (nth_overflow _ _ GE)].
  rewrite make_i's_len in LT. rewrite make_i_nth by easy. pose proof (nlencatfirst_le (Z.to_nat (i0 - Z.of_N bi)) irms). lia. lia.
Qed.
Lemma rewrite_b_bl_safe:
  forall {l cond imm24}
    (R: rewrite_b_bl l cond imm24 !i (pol !i) i2i' !ai tc = Some (irm, table, tc')),
    Goal.
Proof.
  intros. cbv[rewrite_b_bl] in R.
  case_eq irm. intro.
  destruct_match_in R; inversion R; now subst.
  intros. eapply CFIStep; auto. now rewrite H. intros. enough ((x1 = None \/ x1 = Some (Addr (ai*4)) \/ exists e, x1 = Some (Addr e) /\ SafeE !i !e) /\ same_flags s s1 /\ N_len irm = 1).
  destruct H0 as [[?|[?|?]] [? ?]].
  subst x1. replace (_ + _) with ni' by (rewrite i'ni'; now rewrite H2). split. apply permitted_pol. lia. apply ni_in_pol.
  apply CFIHere. simpl. now rewrite sbni, orb_true_r. aauto.
  subst x1. split. apply permitted_abort. apply CFIHere; cbn; aauto.
  destruct H0. destruct H0. subst x1. split. apply permitted_safe; auto; lia. apply (at_safe !i); aauto.
  destruct_match_in R; try discriminate.
  destruct contains eqn:c. apply In_contains in c.
  simpl Z.shiftl in *.
  rewrite <-(Z2N.id (i2i' _)), <-(Z2N.id (i2i' (_ mod _))) in e by (rewrite <-i2i'_nonneg; lia).
  eapply exec_GOTOz in XS as [XS SF];[..|eqapply e]; aauto; [|lia: i'lt|shelve|rewrite i'i;lia|inversion R; subst; now inversion H1].
  inversion R. split; auto.
  destruct XS. right. right. subst x1. repeat eexists. right. do 2 eexists.
  symmetry. rewrite N2Z.inj_mul, Z2N.id by (rewrite <-i2i'_nonneg; lia). repeat f_equal. 
  rewrite Z2N.id. easy. lia. now rewrite Z2N.id by lia. left. easy.
  eapply exec_GOTOz in XS as [XS SF];[..|eqapply e]; aauto; [|lia: i'lt|rewrite i'i;lia|inversion R; subst; now inversion H1].
  inversion R. split; auto.
  destruct XS. right. now left. now left.
  eapply exec_GOTOz in XS as [XS SF];[..|eqapply e0]; aauto; [|lia: i'lt|rewrite i'i;lia|inversion R; subst; now inversion H1].
  inversion R. split; auto.
  destruct XS. right. now left. now left.
  Unshelve.
  remember (_ mod _)%Z. lia: (i2i'_max z1) no_irm_overflow.
Qed.

Lemma rewrite_ldm_pc_safe:
  forall {op Rn register_list reg W cond}
    (R: rewrite_ldm_pc op Rn register_list reg (ARM_lsm op cond W Rn register_list) tc (pol !i) i2i' cond !i !ti !ai = Some (irm, table, tc'))
    (REG: (0 <= reg < 15)%Z)
    (RN: (0 <= Rn < 15)%Z)
    (RL: (0 <= register_list)%Z)
    (RRN: reg <> Rn)
    (OP: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => False | _ => True end)
    (R15: Z.testbit register_list 15 = true),
  Goal.
Proof.
  intros.
  rewrite <-(Z2N.id reg), <-(Z2N.id Rn), <-(Z2N.id register_list) in R by lia. 
  rewrite <-(Z2N.id register_list), Z2N.inj_testbit in R15 by lia.
  remember (Z.to_N reg) as r. remember (Z.to_N Rn) as r2. remember (Z.to_N register_list) as r3.
  assert (r < 15) by lia. assert (r2 < 15) by lia. assert (r <> r2) by lia. clear Heqr Heqr2 reg Rn REG RN RRN register_list Heqr3 RL.
  rename r into reg, r2 into Rn, r3 into register_list, H into REG, H0 into RN, H1 into RRN.

  eapply rewrite_w_table_safe; auto. apply R.
  intros. cbv[ldm_pc_irm] in IRMF.
  eapply Cond; auto. apply IRMF. simpl. lia.
  intros.
  pose proof (ITH:=cond_ith IRMF).
  apply arm_assemble_all_cond_len in IRMF as LEN. simpl in LEN.

  rewrite <-(N.add_0_r (cnd _ _)), cndadd.
  eapply safeinststep; auto. now rewrite ITH.
  aauto.

  intros. rewrite cnds.
  eapply safeinststep; auto. now rewrite ITH.
  aauto. clear s0 VS0 s1 VS1 s2 VS2 VS.

  intros. rewrite cnds. simpl N.succ.
  eapply tablelookup; auto. erewrite <-(N.add_0_r (cnd _ _)), cndadd, N2Nat.inj_add, <-skipn_skipn. cbv[cnd]. rewrite N.add_0_l, Nat2N.id, (skip_b2n_cond IRMF).
  rewrite skipn_app, skipn_all2, app_nil_l, skipn_O, firstn_app, firstn_all2 by (simpl length;lia). simpl sub. rewrite firstn_cons, firstn_O, !Z2N.id. easy.
  all: try solve [destruct SF; lia].
  intros. replace (_ + 7) with (cnd 9 cond) by (unfold cnd;lia).

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  apply exec_str' in XS as [S1 X]; [|lia..]. subst x1.
  forget (reset_temps _ _). remember (ofZ _ _).
  replace (s' R_E) with en in S1 by now destruct H0 as [[? [? ?]] ?]. subst s'. rewrite N2Z.id, update_cancel2 in S1 by aauto.
  rewrite !update_updated, !update_frame in S1 by aauto.
  remember (s0 _ [ _ | _ ]). forget (((_ + cnd _ _) * 4) mod _).
  split. apply permitted_inirm; cbv[cnd]; lia.
  vs VS0. split; auto; rewrite S1 in *; aauto.

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  !SP in XS. change Z_4 with (-!4) in XS. apply exec_ldr' in XS as [S2 X]; [|unZ;lia..]. subst x1.
  forget (reset_temps _ _). forget (n0 _ [ _ | _ ]). rewrite S1, (update_swap _ R_PC _), update_cancel2, (update_swap _ R_PC _), update_cancel2 in S2 by aauto.
  vs VS1. split; auto; rewrite S2 in *; aauto.
  split. apply permitted_inirm; cbv[cnd]; lia.

  eapply CFIStep; auto. now rewrite ITH.
  intros. rewrite cnds. simpl N.succ.
  apply exec_ldm in XS; auto. cbv zeta in XS.
  eenough (SafeE !i _).
  destruct XS as [?|[[? ?]|[? ?]]]. epose proof (safe_div4 !i _ H1). apply a in H2 as [? ?]. subst x1.
  split. apply permitted_safe; auto; cbv[cnd]; lia. apply (at_safe !i); aauto.
  replace (_ + _) with ni' by (rewrite i'ni';cbv[cnd];lia). subst x1.
  split. apply permitted_pol. cbv[cnd];lia. apply ni_in_pol. apply CFIHere; cbn; aauto.
  subst x1. split. easy. apply CFIHere; cbn; aauto.
    remember (n4 (arm_varid Rn) ⊕ _). replace (n4 R_E) with en by now destruct VS1 as [[? [? ?]] ?]. rewrite S2, update_updated.
    replace (_ ⊕ _) with n6. rewrite getmem_setmem by lia. subst n2. rewrite N.mod_small by apply typesafe_getmem. apply SF; aauto.
    subst n6. do 2 f_equal. subst n4. now rewrite !update_frame by aauto. subst n1. now rewrite N2Z.inj_mod.
Qed.
Lemma movwmovt_safe:
  forall {cond reg v1 v2}
    (R: wo_table (arm_assemble_all_cond (MOVW reg v1:: MOVT reg v2::nil) cond) tc = Some (irm, table, tc')),
  Goal.
Proof.
  intros. apply wo_table_irm in R. apply arm_assemble_all_cond_len in R as LEN. simpl in LEN.
  eapply Cond; auto. apply R. simpl. lia.
  intros. apply OnlyFallthru; auto. lia.
  rewrite <-Forall_map, <-skipn_map, (skip_b2n_cond R).
  now repeat (constructor; [aauto|]).
Qed.

Lemma _unused_reg_bound:
  forall base r0 r1 r2, (base <= _unused_reg base r0 r1 r2 < base+4)%Z.
Proof.
  intros. unfold _unused_reg, Z1, Z2, Z3. destruct_match_eqn; lia.
Qed.
Lemma unused_reg_lt: forall r0 r1 r2, (0 <= unused_reg r0 r1 r2 < 13)%Z.
Proof. intros. cbv[unused_reg]. lia: (_unused_reg_bound 0 r0 r1 r2). Qed.
Lemma unused_reg_notpc: forall r0 r1 r2, (unused_reg r0 r1 r2 <> 15)%Z.
Proof. intros. lia: (unused_reg_lt r0 r1 r2). Qed.
Lemma unused_reg_high_lt: forall r0 r1 r2, (0 <= unused_reg_high r0 r1 r2 < 13)%Z.
Proof. intros. cbv[unused_reg_high Z4]. lia: (_unused_reg_bound 4 r0 r1 r2). Qed.
Lemma unused_reg_high_notpc: forall r0 r1 r2, (unused_reg_high r0 r1 r2 <> 15)%Z.
Proof. intros. lia: (unused_reg_high_lt r0 r1 r2). Qed.
Lemma unused_reg_lt': forall r0 r1 r2, (0 <= unused_reg r0 r1 r2 < 15)%Z.
Proof. intros. lia: (unused_reg_lt r0 r1 r2). Qed.
Lemma unused_reg_high_lt': forall r0 r1 r2, (0 <= unused_reg_high r0 r1 r2 < 15)%Z.
Proof. intros. lia: (unused_reg_high_lt r0 r1 r2). Qed.
Lemma unused_reg_lt_high: forall r0 r1 r2 r3 r4 r5, (0 <= unused_reg r0 r1 r2 < unused_reg_high r3 r4 r5)%Z.
Proof. intros. cbv[unused_reg unused_reg_high Z4]. lia: (_unused_reg_bound 0 r0 r1 r2) (_unused_reg_bound 4 r3 r4 r5). Qed.
Hint Resolve unused_reg_lt unused_reg_high_lt unused_reg_lt' unused_reg_high_lt' unused_reg_lt_high unused_reg_notpc unused_reg_high_notpc : cfi.
Set Implicit Arguments.
Lemma bitb_not0:
  forall z b, (bitb z b =? 0 = false -> Z_xbits z b (b+1) = 1)%Z.
Proof.
  intros. unfold bitb in *. rewrite zxbits_eq in *. unfold Z_xbits, Z1 in *. replace (2 ^ _)%Z with (2)%Z in * by (replace (Z.max _ _) with 1%Z by lia; lia). lia.
Qed.
Lemma datar_safe:
  forall op cond S Rn Rd imm5 type Rm
    (RD: Rd <> 15%Z),
  SafeInst (ARM_data_r op cond S Rn Rd imm5 type Rm).
Proof.
  intros. apply safe; cbv[arm2il arm_data_r_il arm_data_op_il arm_data_r_shiftc arm_data_r_addwcarry];
  destruct_match_eqn;
  repeat constructor; try discriminate; replace (_ =? _) with false by lia;
  destruct_match_eqn;
  repeat constructor; try discriminate; aauto.
Qed.
Lemma datarsr_safe:
  forall op cond S Rn Rd Rs type Rm
    (RD: Rd <> 15%Z),
  SafeInst (ARM_data_rsr op cond S Rn Rd Rs type Rm).
Proof.
  intros. apply safe; cbv[arm2il arm_data_rsr_il arm_data_op_il arm_data_rsr_shiftc arm_data_rsr_addwcarry];
  destruct_match_eqn;
  repeat constructor; try discriminate; replace (_ =? _) with false by lia;
  destruct_match_eqn;
  repeat constructor; try discriminate; aauto.
Qed.
Lemma datai_safe:
  forall op cond S Rn Rd imm12
    (RD: Rd <> 15%Z),
  SafeInst (ARM_data_i op cond S Rn Rd imm12).
Proof.
  intros. apply safe; cbv[arm2il arm_data_i_il arm_data_op_il arm_data_i_shiftc arm_data_i_addwcarry];
  destruct_match_eqn;
  repeat constructor; try discriminate; replace (_ =? _) with false by lia;
  destruct_match_eqn;
  repeat constructor; try discriminate; aauto.
Qed.
Lemma lsi_safe:
  forall op cond P U W Rn Rt imm12
    (R: match op with | ARM_LDR => Rt <> 15%Z | _ => True end),
  SafeInst (ARM_ls_i op cond P U W Rn Rt imm12).
Proof.
  intros. apply safe; cbv[arm2il arm_ls_i_il arm_ls_op_il arm_ls_il]; destruct_match_eqn; try lia; repeat constructor; try discriminate; auto; aauto.
Qed.
Lemma lsr_safe:
  forall op cond P U W Rn Rt imm5 type Rm
    (R: match op with | ARM_LDR => Rt <> 15%Z | _ => True end),
  SafeInst (ARM_ls_r op cond P U W Rn Rt imm5 type Rm).
Proof.
  intros. apply safe; cbv[arm2il arm_ls_r_il arm_ls_op_il arm_ls_il]; destruct_match_eqn; try lia; repeat constructor; try discriminate; auto; aauto.
Qed.
Theorem cfi_inst_safety: Goal.
Proof.
  intros s VS. assert(R:=RI). cbv[rewrite_inst] in R. 
  destruct negb. easy.
  destruct_match_in R; try discriminate; subst;
  match type of R with
  | context[goto_abort] => apply goto_abort_safe; auto with cfi
  | context[rewrite_pc_no_jump] => apply (rewrite_pc_no_jump_safe R); auto with cfi
  | context[rewrite_pc_sp_no_jump] => apply (rewrite_pc_sp_no_jump_safe R); auto with cfi
  | context[rewrite_pc] => apply (rewrite_pc_safe R); auto with cfi
  | context[rewrite_pc_sp] => apply (rewrite_pc_sp_safe R); auto with cfi
  | context[rewrite_ldm_pc] => apply (rewrite_ldm_pc_safe R); auto with cfi
  | context[rewrite_b] => apply (rewrite_b_bl_safe R); auto with cfi
  | context[rewrite_bl] => apply (rewrite_b_bl_safe R); auto with cfi
  | context[rewrite_bx] => apply (rewrite_bx_blx_safe R); auto with cfi
  | context[rewrite_blx] => apply (rewrite_bx_blx_safe R); auto with cfi
  | context[z_orig::nil] => apply (SingleFallthru z_orig); inversion R; auto
  | _ => apply (movwmovt_safe R); auto
  end; unZ; try lia.
  all: match goal with |- context[SafeInst] => shelve | _ => apply orb_false_iff in e1 as [? ?] end.
  1,3: now destruct op.
  all: apply bitb_not0 in H; simpl in H;
  rewrite Z.testbit_true, <-Z.shiftr_div_pow2 by lia; apply Z2N.inj; try lia;
  rewrite Z2N.inj_mod, Z2N_inj_shiftr, (shiftr_mod_xbits _ _ 1), xbits_Z2N by (try apply Z.shiftr_nonneg; lia); cbn; lia.
  Unshelve.
  all: try rewrite e.
  all: try solve [first [ apply datar_safe | apply datarsr_safe |apply datai_safe | apply lsr_safe |apply lsi_safe] ;lia || auto with cfi].
  all: try solve [apply safe; repeat (constructor || discriminate || destruct_match_eqn || lia || auto with cfi)].
  apply orb_true_iff in e1 as [?|?]. apply ldm_safe. unfold bitb in H. rewrite zxbits_eq in H. apply Z.eqb_eq in H. simpl in H.
  rewrite testbit_xbits, xbits_Z2N by lia. cbn. now rewrite H.
  apply stm_safe. now destruct op.
Qed.
End CFICases.
Theorem cfi_safety:
  forall a0 s0 t x s
    (* the designated abort address is a valid address not in the new code section *)
    (AI: ai < 2 ^ 30)
    (AIB: outofbounds irms bi' (ai*4) = true)
    (* s0 meets all the preconditions *)
    (VS: store_invs s0)
    (* a0 is the start of a block *)
    (SB: startsblock irms bi' a0 = true)
    (* t starts at the entry with store s0 *)
    (ENTRY: startof t (x, s) = (Addr a0, s0)),
  satisfies_all arm_prog cfi_invs cfi_exits ((x,s)::t).
Proof.
  intros. apply prove_invs.
  - cbn. setoid_rewrite ENTRY. apply NIHere. cbv [effinv cfi_invs cfi_inv_point]. now rewrite SB, orb_true_r.
  - intros. cbv[get_precondition] in PRE. destruct cfi_exits eqn:IB in PRE. easy.

    cbv[true_inv cfi_invs cfi_inv_point] in PRE. clear SB; destruct orb eqn:SB; try easy.
    cbn in IB. rewrite IB, orb_false_l in SB. destruct PRE as [PS VT].

    rewrite cons1; apply cfi_clear_trace; auto.
    simpl in VT. clear -VT SB AI AIB CFI_RW IB.

    apply startsblock_index in SB as [n [LEN A1]].
    assert (S (length code) = length irms)%nat.
      unfold cfi_rw in CFI_RW. destruct_match_in CFI_RW; try discriminate. now apply rewrite_len in CFI_RW.
    destruct (skip_rewrite n) as [tc [ST CFI]]. lia.
    destruct skipn as [|z_or] eqn:s; cbn in CFI; destruct_match_in CFI; try discriminate; inversion CFI; subst; rewrite <-(N.add_0_r (_+_)).
      eapply gotoz_ai_safe; auto. now rewrite ith_skipn_hd, <-H1. apply e0.
    eapply (cfi_inst_safety _  e0); auto. Unshelve. all: auto.
      now rewrite ith_skipn_hd, <-H1.
      now rewrite ith_skipn_hd, <-H2.
      edestruct le_lt_dec as [LE|LT]; [|apply LT].
        rewrite skipn_all_iff, <-Nat.add_1_l, <-skipn_skipn, <-H1, skipn_cons, skipn_O in LE. subst. now apply rewrite_len in e3.
Qed.
End CFI.
Print Assumptions cfi_safety.

