Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import -(notations) arm7_cfi2.
Require Import Picinae_armv7.
Require Import Lia ZifyN ZifyNat.
Import ARM7Notations.
Require Import Nat.

Open Scope Z.

Definition compute_table_size sr := Z.to_nat (2 ^ (32 - sr)).
Definition compute_table_start_index tbi ti := Z.to_nat (ti - tbi).
Definition SafeEntry i2i' (pol: Z -> list Z) ai si a :=
  ai * 4 = a \/ exists di (D: (i2i' di) * 4 = a), In di (pol si).
Definition InBlock i ilen da' :=
  (i * 4 < Z.of_N da' < (i + Z.of_nat ilen) * 4 /\ N.divide 4 da')%Z.
Definition SafeDest i2i' pol ai si ilen a :=
  SafeEntry i2i' pol ai si (Z.of_N a) \/ InBlock (i2i' si) ilen a.
Definition SafeTable i2i' pol ai si table :=
  Forall (SafeEntry i2i' pol ai si) table.
Definition extract_table sr tbi ti (flattened_tables: list Z) :=
  let si := compute_table_start_index tbi ti in
  let ts := compute_table_size sr in
  let table := firstn ts (skipn si flattened_tables) in
  if (si + ts <=? length flattened_tables)%nat && (tbi <=? ti)%Z then Some table else None.

Open Scope N.
Definition ContainsBlock b s i :=
  forall i', i <= i' < i + N.of_nat (length b) ->
    match nth_error b (N.to_nat (i' - i)) with
    | Some z => arm_prog s (i'*4) = Some (4, arm2il (i'*4) (arm_decode z))
    | None => False
    end.
Definition InBlockX i ilen (x: exit * store) :=
  match fst x with
  | Addr a => InBlock (Z.of_N i) ilen a
  | _ => False
  end.

Lemma inblockx_ss:
  forall i len x,
    InBlockX (i + 1) (len) x -> InBlockX i (len+1) x.
Proof.
  intros. destruct x, e.
    unfold InBlockX, InBlock in *. simpl in *. split. lia. easy.
    easy.
Qed.

Lemma make_jump_table_map_safety:
  forall ai dis i2i' sl sr x,
  In (make_jump_table_map dis (map i2i' dis) sl sr (fun _ => Z.mul ai 4) x) (Z.mul ai 4::map (fun i => Z.mul (i2i' i) 4) dis).
Proof.
  intros. induction dis.
    now left.
    cbn [make_jump_table_map map]. destruct orb.
      right. left. now rewrite Z.mul_comm.
      inversion IHdis.
        now left.
        right. now right.
Qed.
Lemma safeentry_in:
  forall ai pol i2i' i x,
    In x (Z.mul ai 4::map (fun i => Z.mul (i2i' i) 4) (pol i)) ->
    SafeEntry i2i' pol ai i x.
Proof.
  intros. inversion H.
    now left.
    right. apply in_map_iff in H0. inversion H0. now exists x0.
Qed.
Lemma Forall_map2list:
  forall P m n (H: forall a, P (m a)),
    Forall P (_map2list m n).
Proof.
  intros. induction n. constructor. simpl. now constructor.
Qed.
Lemma SafeTable_rewrite_w_table:
  forall irm tc pol i2i' cond i ti ai z' table tc'
    (RWT: rewrite_w_table irm tc (pol i) i2i' cond i ti ai = Some (z', table, tc')),
    SafeTable i2i' pol ai i table.
Proof.
  intros. unfold rewrite_w_table in RWT. destruct_match_in RWT; try discriminate.
    inversion RWT; subst. apply Forall_nil.
    remember (Z.shiftl _ _). inversion RWT. apply Forall_rev. rewrite map2list_fix. apply Forall_map2list.
      intro. rewrite Z.mul_comm. apply safeentry_in, make_jump_table_map_safety.
Qed.
Lemma SafeTable_rewrite_inst:
  forall tc i2i' z pol i ti ai bi txt z' table tc'
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (z', table, tc')),
    SafeTable i2i' pol ai i table.
Proof.
  assert (forall i' ai tc a b c, goto_abort i' ai tc = Some (a, b, c) -> b = nil).
    unfold goto_abort. intros. destruct_match_in H; now inversion H.
  assert (forall x tc a b c, wo_table x tc = Some (a, b, c) -> b = nil).
    unfold wo_table. intros. destruct x in H0; now inversion H0.
  assert (forall l cond imm24 i dis i2i' ai tc a b c, rewrite_b_bl l cond imm24 i dis i2i' ai tc = Some (a, b, c) -> b = nil).
    unfold rewrite_b_bl. intros. destruct_match_in H1; now inversion H1.

  intros. unfold rewrite_inst in RI. destruct_match_in RI;
    try solve [first [apply H in RI|apply H0 in RI|apply H1 in RI|inversion RI]; subst; constructor];
    now apply SafeTable_rewrite_w_table in RI.
Qed.

(* copied straight from the Z proof, since there is no N version for some reason *)
Lemma Ndivdec a b : {(a | b)} + {~ (a | b)}.
Proof.
 destruct (N.eq_dec a 0) as [Ha|Ha].
 - destruct (N.eq_dec b 0) as [Hb|Hb].
   + left; subst; apply N.divide_0_r.
   + right. subst. contradict Hb. now apply N.divide_0_l.
 - destruct (N.eq_dec (b mod a) 0).
   + left. now apply N.Lcm0.mod_divide.
   + right. now rewrite <- N.Lcm0.mod_divide.
Defined.
Lemma inblock_dec : forall i ilen a, {InBlock i ilen a} + {~InBlock i ilen a}.
Proof.
  intros. unfold InBlock.
  destruct (Ndivdec 4 a), (Z_lt_dec (i * 4) (Z.of_N a)), (Z_lt_dec (Z.of_N a) ((i + Z.of_nat ilen) * 4)).
  all: (now left) || (now right).
Qed.
Lemma inblockx_dec : forall i ilen a, {InBlockX i ilen a} + {~InBlockX i ilen a}.
Proof.
  intros. destruct a, e. apply inblock_dec. now right.
Qed.

Definition AfterBlock (P: exit * store -> Prop) s bi len ei :=
  forall t0 t1 a' s'
    (XP: exec_prog arm_prog ((Addr a', s')::t1++(Addr (ei*4), s)::t0))
    (IB: Forall (InBlockX bi len) t1),
    P (Addr a', s').

Definition DuringBlock P s bi len ei := AfterBlock (fun xs => P xs \/ ~InBlockX bi len xs) s bi len ei.
Definition DuringBlock' (P: _ -> Prop) s bi len ei :=
  forall t0 t1 a' s'
    (XP: exec_prog arm_prog ((Addr a', s')::t1++(Addr (ei*4), s)::t0))
    (IB: Forall (InBlockX bi len) ((Addr a', s')::t1)),
    P (Addr a', s').
Lemma db_db': forall P s bi len ei, DuringBlock P s bi len ei <-> DuringBlock' P s bi len ei.
Proof.
  intros. unfold DuringBlock, DuringBlock', AfterBlock. split.
    intros. apply H in XP. destruct XP. easy. now inversion IB. now inversion IB.
    intros. destruct (inblockx_dec bi len (Addr a', s')).
      apply H in XP. now left. constructor. easy. easy.
      now right.
Qed.

Definition MaintainsBlock b bi ei s :=
  ContainsBlock b s bi /\ DuringBlock (fun xs => ContainsBlock b (snd xs) bi) s bi (length b) ei.

Lemma ostartof_some_cons{A}:
  forall a b (c:A), ostartof a = Some b -> ostartof (c::a) = Some b.
Proof.
  simpl. destruct a. easy. intros. now rewrite startof_cons.
Qed.
Lemma ostartof_last{A}:
  forall a (b:A), ostartof a = Some b -> exists c, a = c ++ b::nil.
Proof.
  destruct a. easy. intros. destruct (@exists_last _ (a::a0)). easy. destruct s. exists x. rewrite e, ostartof_niltail in H. inversion H. now rewrite <-H1.
Qed.
Lemma single_element{A}:
  forall (a: A) b c,
    a::nil = b ++ c::nil ->
    a = c.
Proof.
  intros. destruct b; simpl in H; inversion H; auto. now apply app_cons_not_nil in H2.
Qed.

Lemma exsplit{A}{P: A -> Prop}:
  (forall a, {P a}+{~P a}) ->
  forall l, Exists P l -> exists l1 x l2, l = l1 ++ x :: l2 /\ P x /\ ~(Exists P l1).
Proof.
  induction l. easy.
  intros. destruct (X a).
    exists nil, a, l. now subst.
    rewrite Exists_cons in H. destruct H.
      contradiction.
      apply IHl in H as [? [? [? [? [? ?]]]]]. rewrite H. exists (a::x), x0, x1. repeat split; auto.
      rewrite Exists_cons. unfold not. now rewrite Decidable.not_or_iff.
Qed.
Lemma cons_cons{A}: forall (a:A) b c, a::b::c = (a::b::nil)++c. Proof. easy. Qed.
Lemma app_cons{A}: forall (a:A) b c, c++a::b = (c++a::nil)++b.
Proof.
  intros. now rewrite <-app_assoc, <-app_comm_cons, app_nil_l.
Qed.
Lemma undofst{A}{B}:
  forall (x: A * B) a,
    fst x = a ->
    exists b, x = (a,b).
Proof.
  intros. destruct x. exists b. now subst.
Qed.

Lemma xp_splice:
  forall p t t' x, exec_prog p (x::t) -> exec_prog p t' -> ostartof t' = Some x -> exec_prog p (t'++t).
Proof.
  intros. apply exec_prog_app. now apply exec_prog_tail in H. unfold can_step_between. destruct t. easy. rewrite H1. now inversion H. easy.
Qed.

Lemma afterblock_step:
  forall b z s bi ei P
    (MB: MaintainsBlock b bi ei s)
    (E: bi <= ei)
    (Z: nth_error b (N.to_nat (ei - bi)) = Some z),
    (forall c' s' x, exec_stmt armc s (arm2il (ei*4) (arm_decode z)) c' s' x ->
        (x = None /\
        (MaintainsBlock b bi (ei+1) (reset_temps s s') ->
          AfterBlock P (reset_temps s s') bi (length b) (ei+1)) /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
        (x = None /\
        length b = N.to_nat (ei - bi + 1) /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
        (exists a, x = Some (Addr a) /\
        P (Addr a, (reset_temps s s')) /\
        (~ (InBlock (Z.of_N bi) (length b) a))) \/
        (exists a, x = Some (Raise a))) ->
    AfterBlock P s bi (length b) ei.
Proof.
  intros. unfold AfterBlock. intros.
  destruct MB as [CB MB].
  specialize (CB ei) as CB'. rewrite Z in CB'.
  remember (N.to_nat _). pose proof (proj1 (nth_error_Some b n) ltac:(now rewrite Z)).
  specialize (CB' ltac:(lia)).
  destruct (@exists_last _ ((Addr a', s')::t1) ltac:(discriminate)) as [? [? ?]]. rewrite app_comm_cons, e, <-app_assoc in XP. simpl in XP.
  assert (XP':=XP). apply exec_prog_split in XP as [XP _].
  inversion XP. inversion H3. rewrite CB' in LU. inversion LU. subst. apply H in XS.
  clear H4 LU H. destruct XS as [[? [? ?]]|[[? [? ?]]|[[? [? [? ?]]]|[? ?]]]]; subst;
    (destruct x; [ inversion e; now try rewrite N.mul_add_distr_r in H2|]).
  {
    inversion e; subst; simpl in XP'.
    eapply H1.
      pose proof (exec_prog_step _ _ _ (exec_prog_none _ _) H3).
      rewrite Forall_app in IB. destruct IB.
      split. apply db_db' in MB. eapply MB. rewrite app_nil_l. apply H. easy.
      intros ??????. eapply MB. rewrite app_cons,app_comm_cons in XP0. apply exec_prog_split in XP0 as [_ [_ ?]].
      eapply (xp_splice _ _ _ _ H H6). now rewrite app_comm_cons, ostartof_niltail, N.mul_add_distr_r.
      apply Forall_app. split. easy. now rewrite N.mul_add_distr_r.
    rewrite N.mul_add_distr_r. apply XP'.
    now apply Forall_app in IB.
  }
  all: inversion e; subst; apply Forall_app in IB as [_ IB]; inversion IB; unfold InBlockX, InBlock in *; simpl in *; now try lia.
Qed.

Definition SafeDestX i2i' pol ai si ilen (xs: exit * store) :=
  match fst xs with
  | Addr a => SafeDest i2i' pol ai si ilen a
  | _ => False
  end.



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
Local Ltac mystep H := match type of H with ?a => idtac a end; match type of H with
                       | context[N.mul ?a 4] => remember (N.mul a 4); mystep H
                       | context[scast ?a ?b ?c] =>
                           remember (scast a b c); mystep H
                       | context[if ?a then ?b else ?c] => destruct a eqn:e; try lia
                       | exec_stmt _ _ (arm2il _ _) _ _ _ =>
                           cbv[arm2il arm_cond_il arm_b_il BranchWritePC arm_R arm_bfx_il] in H; mystep H
                       | exec_stmt _ _ (_ $; If (arm_cond_exp (Z.to_N Z14)) _ _) _ _ _ =>
                           simpl (Z.to_N Z14) in H; cbv[arm_cond_exp] in H; simpl (if _:bool then _ else _) in H
                       | exec_stmt _ _ (_ $; If (arm_cond_exp _) _ _) _ _ _ => apply forget_cond in H; mystep H
                       | exec_stmt _ _ _ _ _ _ => step_stmt H
                       | _ /\ True => destruct H as [H _]; mystep H
                       end.

Ltac destruct_match_in H :=
  repeat match type of H with context[match ?x with _ => _ end] =>
    let e := fresh "e" in
    destruct x eqn:e
  end.
Ltac destruct_match_eqn :=
repeat match goal with |- context[match ?x with _ => _ end] =>
    let e := fresh "e" in
    destruct x eqn:e
  end.
Lemma arm_assemble_all_first:
  forall a a' z,
    arm_assemble_all (a::a') = Some z ->
    exists h t, arm_assemble_all a' = Some t /\ z = h::t /\ arm_decode h = a.
Proof.
  induction z. intros. unfold arm_assemble_all in H. destruct_match_in H; discriminate. intros. exists a0, z. repeat split; unfold arm_assemble_all in H; destruct_match_in H; try discriminate. inversion H. now subst. apply arm_assemble_eq in e. inversion H. now subst.
Qed.
Lemma arm_assemble_all_split:
  forall a b z, arm_assemble_all (a++b) = Some z ->
  exists a' b', z = a'++b' /\ arm_assemble_all a = Some a' /\ arm_assemble_all b = Some b'.
Proof.
  induction a. exists nil, z. easy.
  intros. simpl in H. destruct_match_in H; try discriminate.
  apply IHa in e0 as [? [? [? [? ?]]]]. exists (z0::x), x0. repeat split.
  inversion H. now subst.
  simpl. now rewrite e, H1. easy.
Qed.
Lemma arm_assemble_all_len:
  forall a b, arm_assemble_all a = Some b -> length a = length b.
Proof.
  intros. apply arm_assemble_all_eq in H. now rewrite <- H, length_map.
Qed.
Lemma arm_assemble_all_cond_len:
  forall a cond b, arm_assemble_all_cond a cond = Some b -> (length a <= length b <= S (length a))%nat.
Proof.
  intros. unfold arm_assemble_all_cond in H. destruct Z.ltb. apply arm_assemble_all_len in H. rewrite <- H. simpl. lia. apply arm_assemble_all_eq in H. rewrite <- H, length_map. lia.
Qed.
Lemma update_cancel2: forall (s:store) v n v' n' n0,
  v <> v' -> s[v' := n0][v := n][v' := n'] = s[v' := n'][v := n].
Proof.
  intros. now rewrite update_swap, update_cancel by easy.
Qed.
Lemma update_cancel2': forall (s:store) v n v' n' n0,
  v <> v' -> s[v' := n0][v := n][v' := n'] = s[v := n][v' := n'].
Proof.
  intros. now rewrite update_swap, update_cancel, update_swap by easy.
Qed.

Lemma aaa: forall a b c m, b mod m = c mod m -> (a + b) mod m = (a + c) mod m.
Proof.
  intros. now rewrite N.Div0.add_mod, H, <-N.Div0.add_mod.
Qed.
Lemma exec_add: forall i s s' c' x reg imm shift,
  (reg < 15)%Z ->
  (imm < 2^8) ->
  (shift < 2^4) ->
  exec_stmt armc s (arm2il i (ARM_data_i ARM_ADD 14 0 reg reg (Z.lor (Z.shiftl (Z.of_N shift) 8) (Z.of_N imm)))) c' s' x ->
  reset_temps s s' = s[R_PC := i] [arm_varid (Z.to_N reg) := (s (arm_varid (Z.to_N reg)) ⊕ (imm >> (2 * shift) .| ((imm << (32 - (2* shift))) mod 2^ 32)))]
  /\ x = None.
Proof.
  intros.
  cbv[arm2il arm_data_i_il arm_data_op_il arm_data_i_addwcarry ARMExpandImm_C AddWithCarry arm_data_il arm_cond_il Shift_C] in H2.
  simpl (Z.to_N 0 =? 1) in H2.
  destruct N.eqb eqn:e; try lia. simpl (Z.to_N 14) in H2. cbv[arm_cond_exp] in H2. cbv[N.ltb N.compare Pos.compare Pos.compare_cont andb arm_assign_R] in H2.
  remember (xbits _ _ _).
  remember (2 * (xbits _ _ _)).
  rewrite Z2N_inj_lor, Z2N_inj_shiftl, N2Z.id, xbits_lor, xbits_shiftl in Heqn, Heqn0 by (try apply Z.shiftl_nonneg; lia).
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

Lemma rt:
  forall s s' n, reset_temps s s' (arm_varid n) = s' (arm_varid n).
Proof.
  intros. unfold arm_varid. now destruct_match_eqn.
Qed.
Lemma reset_temps_models{s s'}:
  models armc s' -> models armc (reset_temps s s').
Proof.
  unfold models. intros. unfold reset_temps, reset_vars, archtyps. rewrite CV. now apply H.
Qed.
Lemma Nshiftl_add_distr : forall a b s, (a << s) + (b << s) = (a + b) << s.
Proof.
  intros. now rewrite !N.shiftl_mul_pow2, N.mul_add_distr_r.
Qed.

Local Ltac replace_nth a := match goal with |- nth_error _ ?n = _ => replace n with a by lia end.

Lemma reset_temps_overwrite_l: forall s1 s2 s3, reset_temps (reset_temps s1 s2) s3 = reset_temps s1 s3.
Proof. now specialize (reset_vars_overwrite_l armc). Qed.
Lemma reset_temps_overwrite_r: forall s1 s2 s3, reset_temps s1 (reset_temps s2 s3) = reset_temps s1 s3.
Proof. now specialize (reset_vars_overwrite_r armc). Qed.
Lemma reset_temps_update_l:
  forall s s' n v v', reset_temps (s[R_PC := v][arm_varid n := v']) s' = reset_temps s s'.
Proof.
  intros. unfold reset_temps, arm_varid. now rewrite reset_vars_fchoose, !fchoose_update_l by now destruct_match_eqn.
Qed.
Lemma reset_temps_not_temp:
  forall v s s', armc v <> None -> reset_temps s s' v = s' v.
Proof.
  intros. unfold reset_temps. rewrite reset_vars_fchoose. unfold fchoose. destruct in_ctx eqn:e. easy. unfold in_ctx in e. now destruct_match_in e.
Qed.
Require Import FunctionalExtensionality.
Lemma reset_temps_id:
  forall s, reset_temps s s = s.
Proof.
  intros. unfold reset_temps, reset_vars. apply functional_extensionality. intro. now destruct (archtyps x).
Qed.
Lemma reset_temps_revert: forall s s', reset_temps s' (reset_temps s s') = s'.
Proof. now specialize (reset_vars_revert armc). Qed.
Local Lemma typeof_arm_varid:
  forall n, arm7typctx (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.
Lemma after_arm_add: forall P reg v s bi b pre post ei
  (MB: MaintainsBlock b bi ei s)
  (M: models armc s)
  (E: ei = bi + N.of_nat (length pre))
  (B: arm_assemble_all (pre++arm_add reg (Z.of_N v)++post) = Some b)
  (L: (0 < length post)%nat)
  (R: (reg < 15)%Z)
  (I: bi + N.of_nat (length pre) + 3 < 2 ^ 30)
  (IB: (forall x, InBlockX bi (length b) x -> P x))
  (PC: let s' := s[R_PC := (ei + 3) * 4][arm_varid (Z.to_N reg) := s (arm_varid (Z.to_N reg)) ⊕ v] in
    MaintainsBlock b bi (ei+4) s' ->
    models armc s' ->
    AfterBlock P s' bi (length b) (ei+4)),
  AfterBlock P s bi (length b) ei.
Proof.
  intros. unfold arm_add, Z4, Z8, Z12, Z14, Z16, Z24, Z32 in B. cbn[app]in B. rewrite !zxbits_eq in B.

  apply arm_assemble_all_split in B as [b_pre [b_tail [? [BPRE B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BPRE.
  apply arm_assemble_all_first in B as [? [? [? [? ?]]]]; subst.
  eapply afterblock_step. easy. lia.
  replace_nth (length pre). rewrite nth_error_app2 by lia. replace_nth O. reflexivity.

  intros.
  rewrite H1, <-(Z2N.id 4), <-(Z2N.id (Z_xbits _ _ _)) in H0 by (apply Z_xbits_nonneg||lia).
  apply exec_add in H0 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia].
  left; repeat split; [easy|intros ? RA|shelve].

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x1.
  eapply afterblock_step. easy. lia.
replace_nth (S(length pre)). rewrite nth_error_app2. replace_nth 1%nat. now subst. lia.

  intros.
  rewrite H5, <-(Z2N.id 8), <-(Z2N.id (Z_xbits _ _ _)) in H2 by (apply Z_xbits_nonneg||lia).
  apply exec_add in H2 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia].
  left; repeat split; [easy|intros|shelve].

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x3.
  eapply afterblock_step. easy. lia.
  replace_nth (length pre + 2)%nat. rewrite nth_error_app2. replace_nth 2%nat. now subst. lia.

  intros.
  rewrite H9, <-(Z2N.id 12), <-(Z2N.id (Z_xbits _ _ _)) in H8 by (apply Z_xbits_nonneg||lia).
  apply exec_add in H8 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia].
  left; repeat split; [easy|intros|shelve].

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x5.
  eapply afterblock_step. easy. lia.
  replace_nth (length pre + 3)%nat. rewrite nth_error_app2. replace_nth 3%nat. now subst. lia.

  intros.
  rewrite H13 in H12.
  replace (Z_xbits (Z.of_N v) 0 8) with (Z.lor (Z.shiftl (Z.of_N 0) 8) (Z_xbits (Z.of_N v) 0 8)) in H12 by now rewrite Z.lor_0_l.
  rewrite <-(Z2N.id (Z_xbits _ _ _)) in H12 by (apply Z_xbits_nonneg||lia).
  apply exec_add in H12 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia].
  left; repeat split; [easy|..|shelve].

  rewrite <-3N.add_assoc. rewrite !reset_temps_overwrite_l in *.
  assert (arm_varid (Z.to_N reg) <> R_PC) by (unfold arm_varid; destruct_match_eqn; lia || discriminate).
  rewrite H12, H8, H2, H0. repeat rewrite (update_updated _ (arm_varid _)). repeat rewrite update_swap, update_cancel by easy. rewrite <-!(N.add_assoc _ 1). eenough (_ mod _ = _ ). rewrite H16. intro. apply PC. easy. apply models_update. rewrite typeof_arm_varid. apply N.mod_lt. discriminate. apply models_update. simpl. lia. easy.


  Unshelve. shelve.
  all: apply IB; unfold InBlockX, InBlock; simpl; apply arm_assemble_all_len in H; simpl in H; rewrite length_app; subst; simpl; split; [try lia| apply N.divide_factor_r].
  Unshelve.
  clear.
  rewrite ! N.Div0.add_mod_idemp_l, <-N.add_assoc, N.Div0.add_mod_idemp_l, <-!N.add_assoc.
  apply aaa. rewrite !Z2N_xbits by (apply N2Z.is_nonneg || lia). rewrite !N2Z.id. cbv [Z.to_N N.mul Pos.mul]. simpl N.sub.
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
Qed.

Lemma bfx_bound: forall i s s' c' x widthm1 rd lsb rn,
  exec_stmt armc s (arm2il i (ARM_bfx false 14 (Z.of_N widthm1) rd lsb rn)) c' s' x ->
  exists n, s' = s[R_PC := i][arm_varid (Z.to_N rd) := n] /\ n < 2 ^ (widthm1+1) /\ x = None.
Proof.
  intros. mystep H; unfold arm_varid in H; destruct_match_in H; simpl in H; cbv [arm_cond_exp arm_assign_R arm_varid] in H; simpl in H; destruct_match_in H; rewrite N2Z.id in H; remember (Z.to_N lsb); remember (n + _); step_stmt H; destruct H; inversion H; exists n1; repeat split;
  inversion E; inversion E1; rewrite <-H6, <-H11; simpl; subst; replace (widthm1 + 1) with (N.succ (Z.to_N lsb + widthm1) - Z.to_N lsb) by lia; apply xbits_bound.
Qed.

Lemma UBFX_bound: forall i s s' c' x reg sl sr,
  exec_stmt armc s (arm2il i (UBFX reg reg sl (Z.of_N sr))) c' s' x ->
  (reg <> 15)%Z ->
  (sr < 32) ->
  exists n, s' = s[R_PC := i][arm_varid (Z.to_N reg) := n] /\ n < 2 ^ (32 - sr) /\ x = None.
Proof.
  intros. cbv [UBFX] in H. unfold Z31 in H. rewrite <-(Z2N.id 31) , <-N2Z.inj_sub in H by lia. apply bfx_bound in H. now rewrite <-N.add_sub_swap in H by lia.
Qed.

Lemma afterblock_cond:
  forall P b s i l cond
  (B: arm_assemble_all_cond l cond = Some b)
  (I: i < 2^30 - 64)
  (L: (1 <= length l < 64)%nat)
  (MB: MaintainsBlock b i i s)
  (AB: match arm_assemble_all l with
       | Some b' => forall pre pc,
           (length pre = length b - length l)%nat ->
           (models armc s -> models armc (s[R_PC := pc])) ->
           (exists pre', arm_assemble_all pre' = Some pre) ->
           MaintainsBlock (pre++b') i (i+N.of_nat (length pre)) (s[R_PC := pc]) ->
           AfterBlock P (s[R_PC := pc]) i (length (pre++b')) (i+N.of_nat (length pre))
       | _ => True
       end)
  (PA: forall s, P (Addr ((i + N.of_nat (length b))*4), s))
  (PS: forall s, P (Addr ((i + 1)*4), s)),
    AfterBlock P s i (length b) i.
Proof.
  intros.

  unfold arm_assemble_all_cond in B.
   destruct Z.ltb.

    assert (B':=B).
    apply arm_assemble_all_first in B as [? [? [? [? ?]]]]. subst.
    eapply afterblock_step. assumption. lia. now replace_nth O.
    intros ??? XS.
    rewrite H1 in XS. assert (CP:=XS). mystep XS. mystep XS. destruct N.modulo; mystep XS; destruct XS as [[? ?] _].
    left. repeat split. assumption. rewrite H0 in *.
    change 1 with (N.of_nat (length (x::nil))). rewrite H in AB. intro. apply AB. simpl length. apply arm_assemble_all_len in H. lia.  intro. apply models_update. simpl. lia. easy. eexists (_::nil). simpl. inversion B'. destruct arm_assemble eqn:ee; try discriminate. rewrite ee. rewrite H in H5. now inversion H5.  easy. easy.
      assert (n ⊕ 8 ⊕ n0 .& 4294967292 = (i + N.of_nat (S(length l)))*4) as E.
      {
        subst.
        rewrite N.mul_add_distr_r, N.shiftl_mul_pow2. rewrite <-Z_nat_N, Z2Nat.inj_sub, Nat2Z.id, Nat2N.inj_sub, Z_nat_N by easy.
        cbn. rewrite N.mul_sub_distr_r. unfold scast. pose proof (toZ_nonneg). edestruct H2. rewrite H3.
        rewrite (N.mod_small _ (2^26)), N2Z.inj_sub, N2Z.inj_mul, nat_N_Z by lia. cbn. unfold ofZ. rewrite Z2N.inj_mod by lia. replace (Z.to_N (_ - _)) with (N.of_nat (length l) * 4 - 4) by lia. rewrite <-N.Div0.add_mod.
        change 4294967296 with (2^32). rewrite N_land_mod_pow2_move by lia.
        change (_ mod _) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
        rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r. lia. apply N.log2_lt_pow2. lia. lia. enough (N.of_nat (length l) * 4 - 4 < 2^ 25). rewrite N.mod_small by lia. apply H5. lia.
      }
      simpl length in PA. apply arm_assemble_all_len in H.
      right. right. left. repeat esplit. apply H2. rewrite E, H. apply PA.
      unfold InBlock. rewrite E. simpl length. lia.

  rewrite B in AB.
  replace i with (i + N.of_nat (length (nil:list Z))) at 2. rewrite (store_upd_eq s R_PC _ eq_refl). apply AB. simpl. apply arm_assemble_all_len in B. lia. intro. now rewrite <-store_upd_eq. exists nil. easy. rewrite <-store_upd_eq, N.add_0_r by easy. apply MB. simpl. lia.
Qed.


Lemma afterblock_fallthru:
  forall P b' b s bi,
  Forall (fun z => forall s c' s' x i a, exec_stmt armc s (arm2il i (arm_decode z)) c' s' x -> x <> Some (Addr a)) b' ->
  (forall a s, InBlock (Z.of_N bi) (length (b++b')) a -> P (Addr a, s)) ->
  (0 < length b')%nat ->
  (MaintainsBlock (b++b') bi (bi+N.of_nat (length b)) s) ->
  (forall s, P (Addr ((bi + N.of_nat (length (b++b')))*4), s)) ->
  AfterBlock P s bi (length (b++b')) (bi+N.of_nat (length b)).
Proof.
  destruct b'. easy. revert z. induction b'. intros. eapply afterblock_step. easy. lia. rewrite nth_error_app2. now replace_nth O. lia.
  intros. inversion H. destruct x. destruct e. now eapply H7 in H4. right. right. right. now exists i. right. left. repeat split. rewrite length_app. simpl. lia. rewrite length_app in H3. simpl in H3. rewrite <-N.add_assoc. replace (_ + 1) with (N.of_nat (length b + 1)) by lia. apply H3.
  intros. eapply afterblock_step. easy. lia. rewrite nth_error_app2. replace_nth O. easy. lia.
  rewrite Forall_forall in H. pose proof (H z ltac:(now constructor)) as A. intros. destruct x. destruct e. now eapply A in H4.
  right. right. right. now exists i. left. repeat split. rewrite app_cons. intro. rewrite <-N.add_assoc. replace (_ + 1) with (N.of_nat (length (b++z::nil))) by (rewrite length_app;simpl;lia). eapply IHb'. apply Forall_forall in H. inversion H. apply H9. intros. apply H0. now rewrite app_cons. simpl. lia. rewrite length_app. rewrite Nat2N.inj_add, N.add_assoc. apply H5. intro. now rewrite <-app_cons. apply H0. rewrite length_app. simpl. unfold InBlock. split. lia. apply N.divide_factor_r.
Qed.


Lemma GOTO_correct:
  forall s l src dest c' s' x i,
    src < 2^30 ->
    dest < 2^30 ->
    GOTO l 14 (Z.of_N src) (Z.of_N dest) = Some i ->
    exec_stmt armc s (arm2il (src * 4) i) c' s' x ->
    x = Some (Addr (dest * 4)).
Proof.
  intros s l src dest c' s' x i S D G. intros.
  cbv [GOTO] in G. destruct orb eqn:e in G; try discriminate.
  remember (_ - _ - _)%Z as offset. unfold Z2 in *.
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
  destruct l; inversion G; subst; cbv [arm2il arm_bl_il arm_b_il] in H;
    remember (scast _ _ _) as dsta; remember (src * 4) as srca;
    step_stmt H; destruct H as [H _];
    step_stmt H; destruct H as [[_ ?] _]; now rewrite H, H0.
Qed.
Lemma exec_GOTO':
  forall s l cond src dest c' s' x i,
    src < 2^30 ->
    dest < 2^30 ->
    GOTO l cond (Z.of_N src) (Z.of_N dest) = Some i ->
    exec_stmt armc s (arm2il (src * 4) i) c' s' x ->
    x = Some (Addr (dest * 4)) \/ x = None.
Proof.
  intros s l cond src dest c' s' x i S D G. intros.
  cbv [GOTO] in G. destruct orb eqn:e in G; try discriminate.
  remember (_ - _ - _)%Z as offset. unfold Z2 in *.
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
  destruct l; inversion G; subst; cbv [arm2il arm_bl_il arm_b_il] in H;
    remember (scast _ _ _) as dsta; remember (src * 4) as srca; apply forget_cond in H;
    step_stmt H; destruct H as [H _]; destruct (_ mod _) in H;
    step_stmt H; destruct H as [[_ H] _]; (now right) || left; now rewrite H, H0.
Qed.

Lemma GOTOz_correct:
  forall s l src dest c' s' x z,
    src < 2^30 ->
    dest < 2^30 ->
    GOTOz l 14 (Z.of_N src) (Z.of_N dest) = Some z ->
    exec_stmt armc s (arm2il (src * 4) (arm_decode z)) c' s' x ->
    x = Some (Addr (dest * 4)).
Proof.
  intros. unfold GOTOz in H1. destruct GOTO eqn:e in H1; try discriminate. apply arm_assemble_eq in H1. rewrite H1 in H2.
  now apply (GOTO_correct s l src dest c' s' x a).
Qed.
Lemma exec_GOTOz':
  forall s l cond src dest c' s' x z,
    src < 2^30 ->
    dest < 2^30 ->
    GOTOz l cond (Z.of_N src) (Z.of_N dest) = Some z ->
    exec_stmt armc s (arm2il (src * 4) (arm_decode z)) c' s' x ->
    x = Some (Addr (dest * 4)) \/ x = None.
Proof.
  intros. unfold GOTOz in H1. destruct GOTO eqn:e in H1; try discriminate. apply arm_assemble_eq in H1. rewrite H1 in H2.
  now apply (exec_GOTO' s l cond src dest c' s' x a).
Qed.

Definition NoJ q := forall_stmts_in_stmt (fun q' : stmt => forall e : exp, q' <> Jmp e) q.
Definition NoE q := forall_stmts_in_stmt (fun q' : stmt => forall i : N, q' <> Exn i) q.
Definition NoJE q := NoJ q /\ NoE q.
Lemma noj_cond: forall cond il, NoJ il -> NoJ (arm_cond_il cond il).
Proof. easy. Qed.
Lemma noj_seq: forall a b, NoJ a -> NoJ b -> NoJ (a $; b).
Proof. easy. Qed.
Lemma noje_cond: forall cond il, NoJE il -> NoJE (arm_cond_il cond il).
Proof. intros. destruct H. easy. Qed.
Lemma noje_seq: forall a b, NoJE a -> NoJE b -> NoJE (a $; b).
Proof. intros. now destruct H, H0. Qed.
Lemma noj_ite: forall a b c, NoJ a -> NoJ b -> NoJ (If c b a).
Proof. easy. Qed.

Lemma arm_cond_fallthru:
  forall cond il c s c' s' x
    (XS: exec_stmt c s (arm_cond_il cond il) c' s' x),
    (forall x', exec_stmt c s il c' s' x' -> x' = None) ->
    x = None.
Proof.
  intros. cbv [arm_cond_il] in XS. destruct_match_in XS; first
    [ now apply H in XS
    | inversion XS; destruct b; first [now apply H in XS0 | now inversion XS0]].
Qed.
Local Ltac noje H :=
  match type of H with
  | exec_stmt _ _ (arm2il ?a ?i) _ _ ?x =>
      let A := fresh "A" in
      let B := fresh "B" in
      assert (NoJE (arm2il a i)) as [A B]; [cbv [arm2il]; apply noje_seq; [split;discriminate|try apply noje_cond] | now apply stmt_xnone in H]
  end.
Local Ltac noj H :=
  match type of H with
  | exec_stmt _ _ (arm2il ?a ?i) _ _ ?x =>
      let A := fresh "A" in
      assert (NoJ (arm2il a i)) as A; [cbv [arm2il]; apply noj_seq; [discriminate|try apply noj_cond] | eapply stmt_xnotaddr; now try apply H]
  end.
Local Ltac nje :=
  repeat match goal with
  | |- NoJE (arm_cond_il _ _) => apply noje_cond
  | |- NoJE (Seq _ _) => apply noje_seq
  | |- NoJE ?a => unfold_rec a
  end; try (split;discriminate).
Ltac nj :=
  repeat match goal with
  | |- NoJ (arm_cond_il _ _) => apply noj_cond
  | |- NoJ (Seq _ _) => apply noj_seq
  | |- NoJ ?a => unfold_rec a
  end.
Lemma for_0_14_noj:
  forall reg_list f,
    (forall n m, NoJ (f n m)) -> NoJ (for_0_14 reg_list f).
Proof.
  intros. destruct reg_list. easy. simpl. generalize 0 at 1, 0 at 2. induction p. intros. simpl. apply noj_seq. easy. easy.
  intro. simpl. easy. intro. simpl. easy.
Qed.
Lemma for_0_14_noje:
  forall reg_list f,
    (forall n m, NoJE (f n m)) -> NoJE (for_0_14 reg_list f).
Proof.
  intros. destruct reg_list. easy. simpl. generalize 0 at 1, 0 at 2. induction p. intros. simpl. apply noje_seq. easy. easy.
  intro. simpl. easy. intro. simpl. easy.
Qed.
Lemma arm_lsm_noj:
  forall op cond W Rn register_list a c s c' s' x A
    (XS: exec_stmt c s (arm2il a (ARM_lsm op cond W Rn register_list)) c' s' x),
    (N.testbit (Z.to_N register_list) 15 = false -> x <> Some (Addr A))%N.
Proof.
  intros. noj XS; cbv[arm_lsm_il arm_lsm_op_il arm_lsm_op_type arm_stm_il arm_ldm_il arm_lsm_il_]. easy. destruct_match_eqn;
  nj; try solve [now rewrite (bound_hibits_zero _ _ _ H ltac:(reflexivity)) in e0]; (apply noj_ite; [easy|try apply noj_seq; try apply for_0_14_noj]).
  all: try discriminate; intros; destruct_match_eqn; try easy.
Qed.
Lemma arm_lsm_noj':
  forall op cond W Rn register_list a c s c' s' x A
    (XS: exec_stmt c s (arm2il a (ARM_lsm op cond W Rn register_list)) c' s' x)
    (O: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => True | _ => False end),
    x <> Some (Addr A).
Proof.
  intros. noj XS; cbv[arm_lsm_il arm_lsm_op_il arm_lsm_op_type arm_stm_il arm_ldm_il arm_lsm_il_]. easy. destruct_match_eqn; try easy;
  repeat (destruct_match_eqn; try apply noj_ite; try apply noj_seq; try discriminate; try apply for_0_14_noj; try discriminate; try easy).
Qed.
Lemma arm_data_r_fallthru:
  forall op cond S Rn Rd imm5 type Rm a c s c' s' x
    (XS: exec_stmt c s (arm2il a (ARM_data_r op cond S Rn Rd imm5 type Rm)) c' s' x),
    Rd <> 15%Z -> x = None.
Proof.
  intros. noje XS.
  cbv[arm_data_r_il arm_data_op_il arm_data_r_shiftc arm_data_r_addwcarry arm_data_il].
  destruct DecodeImmShift, Shift_C. destruct_match_eqn; try lia; nje.
Qed.
Lemma arm_data_i_fallthru:
  forall op cond S Rn Rd imm12 a c s c' s' x
    (XS: exec_stmt c s (arm2il a (ARM_data_i op cond S Rn Rd imm12)) c' s' x),
    Rd <> 15%Z -> x = None.
Proof.
  intros. noje XS.
  cbv[arm_data_i_il arm_data_op_il arm_data_i_shiftc arm_data_i_addwcarry arm_data_il].
  destruct ARMExpandImm_C. destruct_match_eqn; try lia; nje.
Qed.
Lemma arm_ls_i_fallthru:
  forall op cond P U W Rn Rt imm12 a c s c' s' x
    (XS: exec_stmt c s (arm2il a (ARM_ls_i op cond P U W Rn Rt imm12)) c' s' x),
    Rt <> 15%Z \/ op <> ARM_LDR -> x = None.
Proof.
  intros. noje XS.
  cbv [arm_ls_i_il arm_ls_op_il arm_ls_il]. destruct H; destruct_match_eqn; try lia; nje; contradiction || (repeat split; try discriminate).
Qed.
Lemma arm_ls_r_fallthru:
  forall op cond P U W Rn Rt imm5 type Rm a c s c' s' x
    (XS: exec_stmt c s (arm2il a (ARM_ls_r op cond P U W Rn Rt imm5 type Rm)) c' s' x),
    Rt <> 15%Z \/ op <> ARM_LDR -> x = None.
Proof.
  intros. noje XS.
  cbv [arm_ls_r_il arm_ls_op_il arm_ls_il]. destruct H; destruct_match_eqn; try lia; nje; contradiction || (repeat split; try discriminate).
Qed.
Lemma arm_movwt_fallthru:
  forall is_w cond imm4 Rd imm12 a c s c' s' x
    (XS: exec_stmt c s (arm2il a (ARM_MOV_WT is_w cond imm4 Rd imm12)) c' s' x),
    x = None.
Proof.
  intros; noje XS; destruct is_w; split; discriminate.
Qed.

Lemma In_contains:
  forall z l, contains z l = true -> In z l.
Proof.
  intros. unfold contains in H. destruct_match_in H; try discriminate. apply find_some in e. destruct e. apply Z.eqb_eq in H1. now subst.
Qed.
Lemma arm_lsm_reglist_bound:
  forall reg reg2,
    (0 <= reg < 15)%Z ->
    (0 <= reg2 < 15)%Z ->
  N.testbit (Z.to_N (Z.lor (Z.shiftl 1 reg) (Z.shiftl 1 reg2))) 15 = false.
Proof.
  intros. rewrite !Z.shiftl_mul_pow2, !Z.mul_1_l, Z2N_inj_lor, N.lor_spec, !Z2N.inj_pow, !N.pow2_bits_eqb by lia. lia.
Qed.
Lemma unused_reg_not_pc:
  forall base r0 r1 r2, (base < 12 -> _unused_reg base r0 r1 r2 <> 15)%Z.
Proof.
  intros. unfold _unused_reg, Z1, Z2, Z3. destruct_match_eqn; lia.
Qed.
Lemma unused_reg_bound:
  forall base r0 r1 r2, (0 <= base < 12 -> 0 <= _unused_reg base r0 r1 r2 < 15)%Z.
Proof.
  intros. unfold _unused_reg, Z1, Z2, Z3. destruct_match_eqn; lia.
Qed.

Local Ltac ft XS :=
  unfold LDR, STR, MOV, MOVW, MOVT in XS; match type of XS with
  | context[ARM_data_i] => eapply arm_data_i_fallthru in XS; [subst;discriminate | try apply unused_reg_not_pc;unfold Z4;lia]
  | context[ARM_data_r] => eapply arm_data_r_fallthru in XS; [subst;discriminate | try apply unused_reg_not_pc;unfold Z4;lia]
  | context[ARM_ls_i] => eapply arm_ls_i_fallthru in XS; [subst;discriminate | (left;apply unused_reg_not_pc;unfold Z4;lia) || lia || now right]
  | context[ARM_ls_r] => eapply arm_ls_r_fallthru in XS; [subst;discriminate | (left;apply unused_reg_not_pc;unfold Z4;lia) || lia || now right]
  | context[ARM_lsm] => eapply arm_lsm_noj in XS; [apply XS|simpl Z.shiftl in *;lia]
  | context[STMDB2] => eapply arm_lsm_noj in XS; [apply XS|apply arm_lsm_reglist_bound; try apply unused_reg_bound;unfold Z4;lia]
  | context[LDMDB2] => eapply arm_lsm_noj in XS; [apply XS|apply arm_lsm_reglist_bound; try apply unused_reg_bound;unfold Z4;lia]
  | _ => noj XS; unfold arm_assign_MemU, arm_R; destruct_match_eqn; repeat split; try discriminate; easy
  end.
Local Ltac faft :=
  repeat constructor; solve [intros ?????? XS; ft XS] || assumption || idtac.

Lemma exec_lsl:
  forall reg s a c' s' x,
  reg < 15 ->
  exec_stmt arm7typctx s (arm2il a (LSL (Z.of_N reg) (Z.of_N reg) Z2)) c' s' x ->
  reset_temps s s' = s[R_PC := a][arm_varid reg := (s (arm_varid reg) << 2) mod 2 ^ 32] /\ x = None.
Proof.
  intros. cbv[LSL arm2il arm_data_r_il arm_data_op_il arm_data_r_shiftc DecodeImmShift arm_data_il arm_cond_il arm_cond_exp arm_assign_R arm_R] in H0. simpl in H0. destruct N.eqb eqn:e; try lia.
  rewrite N2Z.id in H0. unfold arm_varid. destruct_match_eqn; step_stmt H0; destruct H0; step_stmt H0; destruct H0 as [[? ?] ?]; lia || now rewrite H0.
Qed.
Definition LorB (R_E:N) := if R_E then LittleE else BigE.
Lemma exec_ldr:
  forall reg s a c' s' x,
  reg < 15 ->
  models armc s ->
  exec_stmt armc s (arm2il a (LDR (Z.of_N reg) (Z.of_N reg) 0)) c' s' x ->
  reset_temps s s' = s[R_PC := a][arm_varid reg := getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid reg))] /\ x = None.
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
  reset_temps s s' = s[R_PC := a][arm_varid reg := getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid reg2) ⊖ offset)] /\ x = None.
Proof.
  intros.
  cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il arm_cond_exp arm_assign_R arm_MemU] in H2.
  simpl in H2. rewrite !N2Z.id in H2. destruct N.eqb eqn:e; try lia.
  replace (Z.ltb _ _) with true in H2 by lia. simpl in H2. replace (Z.to_N _) with offset in H2 by lia.
  unfold arm_varid. destruct_match_eqn; try lia; step_stmt H2; destruct H2; step_stmt H2; simpl in H2; destruct H2 as [[? ?] _];
  rewrite H2; destruct (s R_E); now subst.
Qed.
Lemma exec_ldr'':
  forall reg reg2 offset s a c' s' x,
  reg < 15 ->
  reg2 < 15 ->
  exec_stmt armc s (arm2il a (LDR (Z.of_N reg) (Z.of_N reg2) offset)) c' s' x ->
  exists n, reset_temps s s' = s[R_PC := a][arm_varid reg := n] /\ x = None.
Proof.
  intros.
  cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il arm_cond_exp arm_assign_R arm_MemU] in H1.
  simpl in H1. rewrite !N2Z.id in H1. destruct N.eqb eqn:e; try lia.
  destruct (_ =? 1);
  unfold arm_varid; destruct_match_eqn; try lia;
  remember (arm_varid reg2); unfold arm_varid in Heqa0; destruct_match_in Heqa0; try lia; remember (Z.to_N _);
  step_stmt H1; destruct H1; step_stmt H1; simpl in H1; destruct H1 as [[? ?] _];
  rewrite H1; now eexists.
Qed.

Lemma exec_bx:
  forall reg s a c' s' x,
  reg < 15 ->
  (4 | s (arm_varid reg)) ->
  exec_stmt armc s (arm2il a (ARM_BX 14 (Z.of_N reg))) c' s' x ->
  x = Some (Addr (s (arm_varid reg))).
Proof.
  intros.
  cbv[arm2il arm_bx_il arm_cond_il arm_cond_exp BXWritePC arm_R] in H1. simpl in H1.
  rewrite N2Z.id in H1.
  change 4 with (2^2) in H0. inversion H0.
  unfold arm_varid. destruct_match_eqn; try lia; simpl arm_varid in *;
  step_stmt H1; destruct H1; step_stmt H1;
  rewrite N.shiftr_0_r, N.Div0.mul_mod, N.mul_0_r, N.Div0.mod_0_l in H1; destruct H1;
  step_stmt H1; rewrite N.shiftr_div_pow2, <-N.testbit_spec', N.mul_pow2_bits_low in H1 by lia; destruct H1; step_stmt H1; destruct H1 as [[_ ?] _]; now rewrite H1, H2.
Qed.
Lemma exec_blx:
  forall reg s a c' s' x,
  reg < 15 ->
  (4 | s (arm_varid reg)) ->
  exec_stmt armc s (arm2il a (ARM_BLX_r 14 (Z.of_N reg))) c' s' x ->
  x = Some (Addr (s (arm_varid reg))).
Proof.
  intros.
  cbv[arm2il arm_bx_il arm_cond_il arm_cond_exp BXWritePC arm_R] in H1. simpl in H1.
  rewrite N2Z.id in H1.
  change 4 with (2^2) in H0. inversion H0.
  unfold arm_varid. destruct_match_eqn; try lia; simpl arm_varid in *;
  step_stmt H1; destruct H1; step_stmt H1;
  rewrite N.shiftr_0_r, N.Div0.mul_mod, N.mul_0_r, N.Div0.mod_0_l in H1; destruct H1;
  step_stmt H1; rewrite N.shiftr_div_pow2, <-N.testbit_spec', N.mul_pow2_bits_low in H1 by lia; destruct H1; step_stmt H1; destruct H1 as [[_ ?] _]; now rewrite H1, H2.
Qed.
Lemma exec_str :
  forall rt rn s s' a c' x offset
    (XS: exec_stmt armc s (arm2il a (STR (Z.of_N rt) (Z.of_N rn) (-(Z.of_N offset)))) c' s' x)
    (RT: rt < 15)
    (RN: rn < 15)
    (O: 0 < offset)
    (M: models armc s),
    reset_temps s s' = s[R_PC := a][V_MEM32 := setmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid rn) ⊖ offset) (s (arm_varid rt))] /\ x = None.
Proof.
  intros. cbv[STR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il Z1 Z14 arm_assign_MemU arm_cond_il arm_cond_exp ] in XS.
  replace (- _ <? _)%Z with true in XS by lia.
  simpl Z.to_N in XS. cbv[N.eqb orb Pos.eqb] in XS. simpl in XS.
  cbv[arm_R] in XS.
  rewrite !N2Z.id in XS.
  replace (Z.to_N _) with (offset) in XS by lia.
  replace (rn =? 15) with false in XS by lia. replace (rt0 =? 15) with false in XS by lia.
  specialize (M (arm_varid rt0) _ (typeof_arm_varid _)). unfold arm_varid in *. destruct_match_eqn; try lia;
  step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _]; destruct (s R_E); step_stmt XS; now destruct XS as [[? ?] [? _]].
Qed.
Lemma exec_str':
  forall rt rn s s' a c' x offset
    (XS: exec_stmt armc s (arm2il a (STR (Z.of_N rt) (Z.of_N rn) offset)) c' s' x)
    (RT: rt < 15)
    (RN: rn < 15),
    reset_temps s s' = s[R_PC := a][V_MEM32 := setmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid rn) ⊕ (ofZ 32 offset)) (s (arm_varid rt))] /\ x = None.
Proof.
  intros.
  cbv[STR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il Z1 Z14 arm_assign_MemU arm_cond_il arm_cond_exp ] in XS.
  destruct (Z_lt_le_dec offset 0);
  [replace (_ <? _)%Z with true in XS by lia|
  replace (_ <? _)%Z with false in XS by lia];
  simpl Z.to_N in XS; cbv[N.eqb orb Pos.eqb] in XS; simpl in XS;
  cbv[arm_R] in XS;
  rewrite !N2Z.id in XS;
  replace (rn =? 15) with false in XS by lia; replace (rt0 =? 15) with false in XS by lia. remember (Z.to_N _).
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

Lemma exec_mov:
  forall s s' a r0 c' x
    (XS: exec_stmt armc s (arm2il a (MOV (Z.of_N r0) SP)) c' s' x)
    (R: r0 < 15),
    reset_temps s s' = s[R_PC := a][arm_varid r0 := s R_SP mod 2^32] /\ x = None.
Proof.
  intros.
  cbv [MOV arm2il arm_data_r_il arm_data_op_il arm_data_r_shiftc arm_data_il arm_assign_R arm_cond_il arm_cond_exp arm_R] in XS.
  rewrite N2Z.id in XS.
  simpl in XS.
  replace (_ =? _) with false in XS by lia. unfold arm_varid. destruct_match; try lia;
  simpl in XS; step_stmt XS; destruct XS as [XS _]; step_stmt XS; now rewrite N.shiftl_0_r in XS.
Qed.

Lemma reset_temps_update_r:
  forall s s' n v v', reset_temps s (s'[R_PC := v][arm_varid n := v']) = (reset_temps s s')[R_PC := v][arm_varid n := v'].
Proof.
  intros. unfold reset_temps, arm_varid. now rewrite reset_vars_fchoose, !fchoose_update_distr, !fchoose_update_l by now destruct_match_eqn.
Qed.
Lemma arm_varid_not_pc:
  forall n, n < 15 -> arm_varid n <> R_PC.
Proof.
  intros. unfold arm_varid. destruct_match_eqn; discriminate || lia.
Qed.
Lemma after_arm_table_lookup:
  forall P ti sl sr reg s bi ei b prefix tail
  (B: arm_assemble_all (prefix++arm_table_lookup (Z.of_N ti) sl (Z.of_N sr) (Z.of_N reg)++tail) = Some b)
  (MB: MaintainsBlock b bi (bi + N.of_nat (length prefix)) s)
  (REG: reg < 15)
  (SR: sr < 32)
  (EI: ei = bi + N.of_nat (length prefix))
  (M: models armc s)
  (* block does not wrap around *)
  (I: bi + N.of_nat (length b) < 2 ^ 30)
  (* block continues after arm_table_lookup *)
  (TL: (0 < length tail)%nat)
  (* table does not wrap around *)
  (TB: ti + 2 ^ (32 - sr) < 2 ^ 30)
  (* P holds while still in the block *)
  (IB: (forall xs, InBlockX bi (length b) xs -> P xs))
  (PC: forall n,
    (* the store after arm_table_lookup finishes executing has reg set to Mem[n*4] (endianness depends on R_E) *)
    let s' := s[R_PC := (bi + N.of_nat (length prefix) + 6) * 4][arm_varid reg := getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (n*4)] in
    MaintainsBlock b bi (ei+7) s' ->
    (* n is an index of the table *)
    ti <= n < ti + 2 ^ (32 - sr) ->
    AfterBlock P s' bi (length b) (ei+7)),
  AfterBlock P s bi (length b) ei.
Proof.
  intros. unfold arm_table_lookup in B. cbn [app] in B. move B after PC.
  pose proof (arm_varid_not_pc reg REG) as NOTPC. pose proof (not_eq_sym NOTPC) as NOTPC'. move NOTPC' after REG. move NOTPC after REG.

  assert (B':=B).
  apply arm_assemble_all_split in B as [b_pre [b_tail [? [BPRE B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BPRE. rewrite length_app in I.
  (* UBFX *)
  apply arm_assemble_all_first in B as [z_ubfx [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step; [assumption|lia|..].
  replace_nth (length prefix). now rewrite BPRE, nth_error_app2, Nat.sub_diag, nth_error_O by easy.

  intros ??? XS. left. eapply (pres_frame_exec_stmt M M) in XS as M0; [|apply welltyped_arm2il; lia]. rewrite DECODE in XS; clear DECODE.
  apply UBFX_bound in XS as [reg_val [? [REGBOUND EXIT]]];[|lia ..]; subst; clear c'.
  rewrite reset_temps_update_r, reset_temps_id.
  repeat split; [|shelve]. clear MB; intros MB.

  (* LSL *)
  apply arm_assemble_all_first in B as [z_lsl [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step; [assumption|lia|..].
  replace_nth (length prefix + 1)%nat. rewrite nth_error_app2 by lia. now replace_nth 1%nat.
  simpl in I.
  intros ??? XS. left. eapply (pres_frame_exec_stmt M0 M0) in XS as M1; [|apply welltyped_arm2il; lia]. rewrite DECODE in XS; clear DECODE.
  apply exec_lsl in XS as [S' EXIT]; [|lia]; subst; clear c'.
  rewrite N2Z.id, !update_cancel2, update_updated, reset_temps_update_l, N.shiftl_mul_pow2 in S' by assumption.
  repeat split; [|shelve].
  rewrite <-N.add_assoc, N2Z.id, reset_temps_update_l.
  rewrite N.add_assoc. simpl.
  clear MB; intros MB.

 
  (* arm_add *)
  unfold Z4 in B. rewrite <-app_cons, <-(Z2N.id (_ * _)) in B by lia. simpl.
  eapply after_arm_add.
    easy.
    now apply reset_temps_models.
    shelve.
    rewrite cons_cons, <-app_cons, app_assoc, <-(Z2N.id Z4), <-N2Z.inj_mul in B' by (unfold Z4; lia). apply B'.
    simpl. lia.
    lia.
    rewrite length_app. simpl. apply arm_assemble_all_len in B. simpl in B. lia.
    assumption.
  clear MB; intros s'' MB M2. subst s''.

  (* LDR *)
  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_ldr [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  apply afterblock_step with (z:=z_ldr); [assumption|lia|..].
  replace_nth (length prefix + 6)%nat. rewrite nth_error_app2 by lia. replace_nth 6%nat. rewrite 2nth_error_S. simpl tl. rewrite nth_error_app2 by lia. now rewrite <-BADD.
  intros c' s''' x XS. eapply (pres_frame_exec_stmt M2 M2) in XS as M3; [|apply welltyped_arm2il; rewrite BPRE; rewrite length_app in I; try lia]. rewrite DECODE in XS; clear DECODE.
  apply exec_ldr in XS as [S''' EXIT]; [|lia|assumption]; subst; clear c'.

  rewrite S', !reset_temps_update_l in *. clear S'.
  rewrite N2Z.id, !update_cancel2, update_updated, !update_frame in * by (assumption || unfold arm_varid; destruct_match; discriminate).
   rewrite update_updated in S'''. rewrite S'''.
  left. repeat split; [|shelve].
  rewrite <-3N.add_assoc.

  unfold Z4 in *. rewrite (N.mul_comm _ ti), N.Div0.add_mod_idemp_l, <-N.mul_add_distr_r, <-2(N.add_assoc _ 1). rewrite N.mod_small by lia.
  clear MB; intros MB .  apply PC. assumption. lia.
  Unshelve.
  3: rewrite length_app; simpl; lia.
  all: apply arm_assemble_all_len in B; simpl in B; apply IB.
  all: unfold InBlockX, InBlock; simpl; split; [|apply N.divide_factor_r].
  all: rewrite length_app; simpl; try rewrite length_app; simpl; lia.
Qed.

Definition SafeAfterBlock i2i' pol ai i len s := AfterBlock (SafeDestX i2i' pol ai i len) s (Z.to_N (i2i' i)) len (Z.to_N (i2i' i)).
Lemma find_sr_bound:
  forall dis dis' sl sr a, find_sr dis dis' sl sr = Some a -> (0 <= a <= sr)%Z.
Proof.
  intros ?????. apply find_sr_ind.
    easy.
    intros. inversion H. lia.
    intros. unfold Z1 in *. apply H in H0. lia.
Qed.
Lemma find_hash_bound:
  forall dis dis' sl a b, find_hash dis dis' sl = Some (a, b) -> (0 <= b < 32)%Z.
Proof.
  intros ?????. apply find_hash_ind.
    easy.
    intros. inversion H. subst. unfold Z31 in e0. apply find_sr_bound in e0. lia.
    intros. now apply H.
Qed.
Lemma map2list_len:
  forall m n, length (_map2list m n) = n.
Proof.
  induction n. easy. simpl. now rewrite IHn.
Qed.
Lemma make_jump_table_len:
  forall dis dis' ai sl sr n, length (make_jump_table dis dis' ai sl sr n) = Z.to_nat n.
Proof.
  intros. unfold make_jump_table. rewrite length_rev, map2list_fix. now rewrite map2list_len.
Qed.
Definition SafeTableCache i2i' pol ai tbi (flattened_tables: list Z) (tc: TableCache) :=
  forall si ti sl sr
    (TC: tc (pol si) = Some (ti, sl, sr)),
    exists table,
      extract_table sr tbi ti flattened_tables = Some table /\
      SafeTable i2i' pol ai si table /\
      ((0 <= sr < 32)%Z /\ (0 <= sl)%Z /\ (0 <= ti) /\ (ti + 2 ^ (32 - sr) < 2 ^ 30))%Z.

Lemma table_size_correctness:
  forall sr tbi ti flattened_tables t
    (T: extract_table sr tbi ti flattened_tables = Some t),
    length t = compute_table_size sr.
Proof.
  intros. unfold extract_table in T. destruct_match_in T; try discriminate.
  inversion T. rewrite length_firstn, length_skipn. lia.
Qed.
 
Lemma arm_assemble_all_app:
  forall a b c d,
    arm_assemble_all a = Some b ->
    arm_assemble_all c = Some d ->
    arm_assemble_all (a++c) = Some (b++d).
Proof.
  induction a. intros. simpl. inversion H. now subst.
  intros. simpl. inversion H. destruct arm_assemble eqn:e, arm_assemble_all eqn:f; try discriminate. rewrite (IHa _ _ _ eq_refl H0). now inversion H2.
Qed.

Lemma exec_movwt:
  forall is_w cond imm4 Rd imm12 a s c' s' x
    (XS: exec_stmt armc s (arm2il a (ARM_MOV_WT is_w cond imm4 (Z.of_N Rd) imm12)) c' s' x)
    (M: models armc s)
    (R: Rd < 15)
    (I4: Z.to_N imm4 < 2^4)
    (I12: Z.to_N imm12 < 2^12),
    exists n, n < 2 ^ 32 /\ reset_temps s s' = s[R_PC := a][arm_varid Rd := n] /\ x = None.
Proof.
  intros. cbv[arm2il arm_mov_wt_il arm_cond_il arm_assign_R arm_R] in XS. apply forget_cond in XS.
  unfold arm_varid.
  remember (_ << _). remember (cbits _ _ _).
  destruct_match; try lia; simpl in XS;
  (destruct_match_in XS;
   step_stmt XS; destruct XS as [XS _]; destruct (_ mod _); step_stmt XS;
    destruct XS as [XS _]; eexists; (split; [|apply XS || rewrite <-store_upd_eq by reflexivity; try apply XS]);
    try solve [rewrite update_frame by discriminate; now apply M];[ rewrite Heqn0, <-fold_cbits, N.shiftl_mul_pow2; apply lor_bound; lia |
    apply lor_bound; [apply (N.le_lt_trans _ 65535 _ (N.land_le_r _ _)); lia|change (2^32) with (2^16*2^16); rewrite Heqn, Heqn0, <-fold_cbits, !N.shiftl_mul_pow2; apply N.mul_lt_mono_pos_r; [lia|apply lor_bound;lia]]]).
Qed.
Lemma exec_ldrpc:
  forall s a c' s' x
    (XS: exec_stmt armc s (arm2il a (LDR PC SP Z_8)) c' s' x)
    (D: (4 | getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s R_SP ⊖ 8)))
    (S: (4 | s R_SP)),
    x = Some (Addr (getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s R_SP ⊖ 8))).
Proof.
  intros. cbv[LDR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il arm_cond_il Z1] in XS.
  simpl Z.to_N in XS. cbv[N.eqb orb Pos.eqb arm_cond_exp BXWritePC arm_R arm_varid] in XS . simpl in XS.
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
Lemma exec_align:
  forall a s s' c' x
    (M: models armc s)
    (XS: exec_stmt armc s (arm2il a (ALIGN SP)) c' s' x),
    reset_temps s s' = s[R_PC := a][R_SP := (s R_SP >> 2) * 4] /\ x = None.
Proof.
  intros.
  cbv [ALIGN arm2il arm_data_i_il arm_data_op_il arm_data_i_shiftc arm_data_il SP Z13 arm_cond_il arm_assign_R] in XS. simpl N.eqb in XS. cbn in XS. step_stmt XS. destruct XS as [XS _]. step_stmt XS. simpl in XS.
    change (4294967292) with (N.lnot (2 * (2 * 0 + 1) + 1) 32) in XS.
    rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r, N.mul_assoc, N.mul_comm in XS. simpl. easy.
    specialize (M R_SP _ eq_refl).
    destruct (s R_SP) eqn:E; now try solve [apply N.log2_lt_pow2; lia].
Qed.
Notation "m [ e | a  ]" := (getmem 32 (LorB e) 4 m a) (at level 50, left associativity) : arm7_scope. (* write dword to memory *)
Notation "m [ e | a := v  ]" := (setmem 32 (LorB e) 4 m a v) (at level 50, left associativity) : arm7_scope. (* write dword to memory *)
Check 0[2| 1 := 2].
Check fun x => msub 32 x x.
Lemma land_pow2_lt:
  forall a n, a < 2 ^ n -> N.land a (2^n) = 0.
Proof.
  intros. apply N.bits_inj_0. intros. rewrite N.land_spec. destruct (N.eq_dec n0 n). subst.
  now rewrite <-(N.mod_small _ _ H), N.mod_pow2_bits_high, andb_false_l.
  now rewrite N.pow2_bits_false, andb_false_r.
Qed.

Lemma exec_stmdb3_e:
  forall s s' a c' x r0 r1 r2 r3 r4 r5
  (XS: exec_stmt armc s (arm2il a (STMDB3 SP (unused_reg r0 r1 r2) (unused_reg_high r3 r4 r5) PC)) c' s' x)
  (SP: ~(4|s R_SP)),
    x = Some (Raise 16).
Proof.
  intros.
  cbv[STMDB3 arm2il arm_lsm_il arm_lsm_op_il arm_lsm_op_start arm_lsm_op_type arm_stm_il arm_lsm_il_ arm_cond_il] in XS.
  rewrite !Z.shiftl_mul_pow2, !Z.mul_1_l in XS.
  rewrite <-(N2Z.id 15), <-Z2N.inj_testbit, Z2N.id, !Z.lor_spec, Z.pow2_bits_true, orb_true_r in XS.
  simpl (Z.to_N 0) in XS. simpl (Z.to_N Z14) in XS. cbv[ arm_cond_exp] in XS.
  rewrite !Z2N_inj_lor, !Z2N.inj_pow, (N.mod_small _ (2^16)), !popcount_lor, !popcount_pow2 in XS.
  rewrite !land_pow2_lt in XS. remember (fun i => _). simpl in XS.
  simpl in Heqy. subst y.
  remember (unused_reg _ _ _) as q. remember (unused_reg_high _ _ _) as w. remember (q+w)%Z as e.
  all: unfold unused_reg, unused_reg_high, _unused_reg, Z4, Z3, Z2, Z1, PC, Z15 in *. 2-20: destruct_match; simpl; lia.
  subst q w.
  destruct_match_in Heqe; simpl in XS;
  step_stmt XS; destruct XS as [XS _];
  step_stmt XS; change 3 with (N.ones 2) in XS; rewrite N.land_ones in XS; rewrite <-N.Lcm0.mod_divide in SP; replace (_ =? 0) with false in XS by lia; destruct XS as [XS _];
  now step_stmt XS.
Qed.

Lemma exec_ldmdb3:
  forall r0 r1 r2 r3 r4 r5 s s' c' x a
    (XS: exec_stmt armc s (arm2il a (LDMDB3 (unused_reg_high r3 r4 r5) (unused_reg r0 r1 r2) (unused_reg_high r3 r4 r5) PC)) c' s' x)
    (M: (4|getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid (Z.to_N (unused_reg_high r3 r4 r5))) ⊖ 4 ))),
    x = Some (Addr (getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (s (arm_varid (Z.to_N (unused_reg_high r3 r4 r5))) ⊖ 4 ))) \/ x = Some (Raise 16).
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
  remember (unused_reg _ _ _) as q. remember (unused_reg_high _ _ _) as w. remember (q+w)%Z as e.
  all: unfold unused_reg, unused_reg_high, _unused_reg, Z4, Z3, Z2, Z1, PC, Z15 in *. 2-20: destruct_match; simpl; lia.

  remember (s R_E);
  destruct n eqn:E;
  subst q w; destruct_match_in Heqe; simpl in XS; step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _];
  (destruct N.eqb; [left| step_stmt XS; now right]); step_stmt XS; destruct XS as [XS _]; rewrite <-Heqn, N.shiftr_0_r in XS;
  rewrite !N.Div0.add_mod_idemp_l, <-2N.add_assoc in XS; simpl in XS; simpl in M; inversion M;
  unfold msub in H; simpl in H; rewrite <-N.add_assoc in XS; simpl in XS; rewrite H in XS;  replace (_ mod 2) with 0 in XS by lia; step_stmt XS; destruct XS as [XS _];
  rewrite <-Heqn, N.Div0.add_mod_idemp_l, <-N.add_assoc in XS; simpl in XS; rewrite H in XS; replace (_ =? 1) with false in XS by (simpl;lia);
  step_stmt XS; destruct XS as [[_ XS] _]; rewrite <-Heqn, N.Div0.add_mod_idemp_l, <-N.add_assoc in XS; apply XS.
Qed.

Lemma exec_stmdb3:
  forall s s' a c' x r0 r1 r2 r3 r4 r5
  (XS: exec_stmt armc s (arm2il a (STMDB3 SP (unused_reg r0 r1 r2) (unused_reg_high r3 r4 r5) PC)) c' s' x)
  (SP: (4|s R_SP)),
  reset_temps s s' = s[R_PC := a][V_MEM32 :=
    s V_MEM32 [s R_E|s R_SP ⊖ 12 := s (arm_varid (Z.to_N (unused_reg r0 r1 r2))) ]
              [s R_E|s R_SP ⊖ 8 := s (arm_varid (Z.to_N (unused_reg_high r3 r4 r5))) ]
              [s R_E|s R_SP ⊖ 4 := a ⊕ 8 ]] /\
    x = None.
Proof.
  intros.
  cbv[STMDB3 arm2il arm_lsm_il arm_lsm_op_il arm_lsm_op_start arm_lsm_op_type arm_stm_il arm_lsm_il_ arm_cond_il] in XS.
  rewrite !Z.shiftl_mul_pow2, !Z.mul_1_l in XS.
  rewrite <-(N2Z.id 15), <-Z2N.inj_testbit, Z2N.id, !Z.lor_spec, Z.pow2_bits_true, orb_true_r in XS.
  simpl (Z.to_N 0) in XS. simpl (Z.to_N Z14) in XS. cbv[ arm_cond_exp] in XS.
  rewrite !Z2N_inj_lor, !Z2N.inj_pow, (N.mod_small _ (2^16)), !popcount_lor, !popcount_pow2 in XS.
  rewrite !land_pow2_lt in XS. remember (fun i => _). unfold for_0_14 in XS.
  simpl in XS.
  simpl in Heqy. subst y.


  all: unfold unused_reg, unused_reg_high, _unused_reg, Z4, Z3, Z2, Z1, PC, Z15 in *. 2-20: destruct_match; simpl; lia.
  destruct_match_eqn; simpl in XS;
  remember (s R_E);
  destruct n eqn:E;
  step_stmt XS; destruct XS as [XS _];
  step_stmt XS; destruct XS as [XS _];
  change 3 with (N.ones 2) in XS; inversion SP; rewrite H, N.land_ones, N.Div0.mod_mul in XS; simpl in XS; clear H;
  step_stmt XS; destruct XS as [XS _]; rewrite <-Heqn in XS;
  step_stmt XS; destruct XS as [XS _]; rewrite <-Heqn in XS;
  step_stmt XS; destruct XS as [XS _]; rewrite <-Heqn in XS;
  step_stmt XS; destruct XS as [XS _];
  rewrite !N.Div0.add_mod_idemp_l, <-!N.add_assoc in XS; apply XS.
Qed.
Lemma N2Z_inj_popcount: forall n, Z.of_N (popcount n) = Z_popcount (Z.of_N n).
Proof.
  intros. now destruct n.
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
Lemma for_context:
forall reg_list f c, (forall n m s s' c' x, exec_stmt c s (f n m) c' s' x -> c' = c) ->
  (forall s s' c' x, exec_stmt c s (for_0_14 reg_list f) c' s' x -> c' = c).
Proof.
  intros. destruct reg_list. simpl in H0. inversion H0. easy. simpl in H0. revert H0. generalize 0 at 1, 0 at 2, s. induction p.
    intros. simpl in H0. inversion H0. subst. now apply H in XS. apply H in XS1. subst. now apply IHp in XS0.
    intros. simpl in H0. now apply IHp in H0.
    intros. simpl in H0. now apply H in H0.
Qed.
     
Lemma exec_ldm:
  forall op cond Rn register_list a s s' c' x W
    (R: N.testbit register_list 15 = true)
    (RN: Rn < 15)
    (O: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => False | _ => True end)
    (XS: exec_stmt armc s (arm2il a (ARM_lsm op cond W (Z.of_N Rn) (Z.of_N register_list))) c' s' x),
    (let bc := (Z4 * Z_popcount (Z.of_N (register_list mod 2^16)))%Z in
     let addr := s V_MEM32 [s R_E | s (arm_varid Rn) ⊕ ofZ 32 (arm_lsm_op_start op bc + bc - Z4) ] in
     (4|addr) -> x = Some (Addr addr))
    \/ x = None \/ x = Some (Raise 16).
Proof.
  intros. rewrite <-N2Z_inj_popcount.
  cbv[arm2il arm_lsm_il arm_lsm_op_il arm_lsm_op_type] in XS.
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
    subst q1 q2 c'0 s'0 x'. inversion XS1. inversion E. subst v e c2 s2 a w0 w n3. clear XS XS1. rewrite <-store_upd_eq in XS0 by easy. rename XS0 into XS.
  inversion XS. destruct b.
    step_stmt XS0. right. now left.
    subst e q1 q2 c'0 s'0 x0. clear E0 p XS E. rename XS0 into XS.
  inversion XS. destruct b.
    step_stmt XS0. right. now right.
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
  assert (s2 temp0 = s (arm_varid Rn) ⊕ n0). {
    clear - RN XS1. inversion XS1. subst. apply (noassign_stmt_same temp0) in XS2. inversion XS2.
    clear - RN XS0. destruct N.eqb.
      inversion XS0. subst. inversion XS1. subst. inversion E. subst. unfold arm_R in E1. replace (_ =? _) with false in E1 by lia. inversion E1. subst.
      rewrite typeof_arm_varid in TYP. inversion TYP. subst. simpl in XS2. inversion E2. subst. apply (noassign_stmt_same temp0) in XS2. inversion XS2.
      rewrite update_updated. rewrite update_frame by now apply arm_varid_not_pc. easy. constructor. unfold arm_varid; destruct_match; discriminate.
      inversion XS0. subst. inversion E. subst. inversion E. subst. unfold arm_R in E1. replace (_ =? _) with false in E1 by lia. inversion E1. subst. inversion E2. subst.
      rewrite typeof_arm_varid in TYP. inversion TYP. subst. simpl.
      rewrite update_updated. rewrite update_frame by now apply arm_varid_not_pc. easy.
      apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (s2 V_MEM32 = s V_MEM32). {
    apply (noassign_stmt_same V_MEM32) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  assert (s2 R_E = s R_E). {
    apply (noassign_stmt_same R_E) in XS1. inversion XS1. now rewrite update_frame. constructor. destruct N.eqb. constructor. now constructor.
    constructor. unfold arm_varid; destruct_match; discriminate. constructor. easy. apply for_noassign. constructor. unfold arm_varid; destruct_match; discriminate.
  }
  clear XS1. rewrite (store_upd_eq _ _ _ H), (store_upd_eq _ _ _ H0), (store_upd_eq _ _ _ H1) in XS0.
  cbv [BXWritePC] in XS0.
  left. intros. enough (addr = s V_MEM32 [s R_E | s (arm_varid Rn) ⊕ n0 ⊕ n2]).
  step_stmt XS0. replace (_ mod 2) with 0 in XS0. destruct XS0 as [XS0 _].
  step_stmt XS0. replace (_ =? 1) with false in XS0. destruct XS0 as [XS0 _].
  step_stmt XS0. destruct XS0 as [[_ X] _]. rewrite H3, X. now destruct (s R_E).
  inversion H2. cbv[ N.shiftr Pos.iter]. destruct (s R_E); simpl LorB in H3; rewrite <-H3, H4; lia.
  inversion H2. destruct (s R_E); simpl LorB in H3; rewrite <-H3, H4, N.shiftr_0_r; lia.
  subst n0 n2 addr bc. clear -Heqn. unfold Z4. rewrite N2Z.inj_mul. simpl Z.of_N.
  remember (arm_lsm_op_start _ _). unfold ofZ in *.
  rewrite <-(N.Div0.add_mod_idemp_r _ (4*n-4)), <-(N2Z.id ((4*n-4) mod _)), N.Div0.add_mod_idemp_l, <-N.add_assoc, <-Z2N.inj_add by lia.
  simpl popcount in Heqn.
  rewrite N2Z.inj_mod, N2Z.inj_sub, N2Z.inj_mul by lia. simpl Z.of_N. rewrite <-Z.add_sub_assoc, Z.add_mod by lia.
  symmetry. rewrite <-N.Div0.add_mod_idemp_r. change (2^32) with (Z.to_N (2^32)). rewrite <-Z2N.inj_mod.
  subst. now destruct (s R_E). lia. lia.
Qed.
   
Lemma arm_varid_different:
  forall r0 r1 (R0: r0 < 15) (R1: r1 < 15) (R: r0 <> r1), arm_varid r0 <> arm_varid r1.
Proof.
  intros. unfold arm_varid. destruct_match_eqn; lia || discriminate.
Qed.

Lemma bitb_not0:
  forall z b, (bitb z b =? 0 = false -> bitb z b =? 1 = true)%Z.
Proof.
  intros. unfold bitb in *. rewrite zxbits_eq in *. unfold Z_xbits, Z1 in *. replace (2 ^ _)%Z with (2)%Z in * by (replace (Z.max _ _) with 1%Z by lia; lia). lia.
Qed.
Lemma arm_varid_not_e: forall n, arm_varid n <> R_E. Proof. intro; unfold arm_varid; destruct_match; easy. Qed.
Lemma SafeDest_rewrite_inst:
  forall tc i2i' z pol i ti ai bi txt irm' table tc' s1 tbi flattened_tables
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (irm', table, tc'))
    (TC: SafeTableCache i2i' pol ai tbi flattened_tables tc)
    (AI: (0 <= ai < 2^30)%Z)
    (TI: (0 <= ti)%Z)
    (TI': (ti + Z.of_nat (length table) < 2^30)%Z)
    (I:  (0 <=  i < 2^30)%Z)
    (BI: (0 <= bi < 2^30)%Z)
    (M: models armc s1)
    (MB: MaintainsBlock irm' (Z.to_N (i2i' i)) (Z.to_N (i2i' i)) s1)
    (* abort index is not in this block *)
    (AIB: ~ InBlock (i2i' i) (length irm') (Z.to_N ai * 4))
    (* new indices are in range *)
    (I2I: forall i, (0 <= i2i' i < 2^30-64)%Z)
    (* the block of the next instruction is placed right after the end of this block *)
    (I2I'': (i2i' (i + 1) = i2i' i + Z.of_nat (length irm'))%Z)
    (* no new indices start inside of this block *)
    (I2I''': forall j, (i2i' j <= i2i' i \/ i2i' i + Z.of_nat (length irm') <= i2i' j)%Z)
    (* new table is in memory *)
    (TIM: forall n,
      Z.to_N ti <= n < Z.to_N ti + N.of_nat (length table) ->
      In (Z.of_N (getmem 32 (LorB (s1 R_E)) 4 (s1 V_MEM32) (n*4))) table
    )
    (* everything tc returns is in memory *)
    (TCIM: forall si ti sl sr n t,
      tc si = Some (ti, sl, sr) ->
      extract_table sr tbi ti flattened_tables = Some t ->
      Z.to_N ti <= n < Z.to_N ti + N.of_nat (length t) ->
      In (Z.of_N (getmem 32 (LorB (s1 R_E)) 4 (s1 V_MEM32) (n*4))) t
    )
    (* new table is not writable *)
    (NWT: forall j k,
      Z.to_N ti <= j < Z.to_N ti + N.of_nat (length table) ->
      k ⊖ j * 4 < 4 ->
      N.testbit (s1 A_WRITE) k = false)
    (* nothing tc returns is writable *)
    (NWTC: forall si ti sl sr t j k,
      tc si = Some (ti, sl, sr) ->
      extract_table sr tbi ti flattened_tables = Some t ->
      Z.to_N ti <= j < Z.to_N ti + N.of_nat (length t) ->
      k ⊖ j * 4 < 4 ->
      N.testbit (s1 A_WRITE) k = false),

    SafeAfterBlock i2i' pol ai i (length irm') s1.
Proof.
  intros. apply SafeTable_rewrite_inst in RI as ST.
  specialize (I2I i) as I2I'.

  assert (
    forall l cond, arm_assemble_all_cond l cond = Some irm' ->
      (1 <= length l < 64)%nat ->
      In (Z.add i 1) (pol i) ->
      match arm_assemble_all l with
      | Some b' =>
          forall pre pc,
          (length pre = length irm' - length l)%nat ->
          (models armc s1 -> models armc (s1[R_PC := pc])) ->
          (exists pre', arm_assemble_all pre' = Some pre) ->
          MaintainsBlock (pre ++ b') (Z.to_N (i2i' i))
            (Z.to_N (i2i' i) + N.of_nat (length pre)) (s1[R_PC := pc]) ->
          AfterBlock (SafeDestX i2i' pol ai i (length irm'))
            (s1[R_PC := pc]) (Z.to_N (i2i' i)) (length (pre ++ b'))
            (Z.to_N (i2i' i) + N.of_nat (length pre))
      | None => True
      end ->
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as C. {
    intros. eapply afterblock_cond. apply H. lia. assumption. assumption. assumption.
      intros. unfold SafeDestX, SafeDest. simpl. left. right. exists (i+1)%Z. split. lia. assumption.
      intros. unfold SafeDestX, SafeDest. simpl.
      destruct (Nat.eq_dec (length irm') 1). left. right. exists(i+1)%Z. split. lia. assumption.
      right. unfold InBlock. split. split. lia.
      apply arm_assemble_all_cond_len in H.
      lia. apply N.divide_factor_r.
  }
    Ltac mylia := unfold SafeDestX, SafeDest, InBlockX, InBlock in *;
      repeat match goal with
             | H := _ |- _ => simpl in H; subst H
             end;
             try rewrite length_app in *; simpl length in *;
      repeat match goal with
             | H: arm_assemble_all_cond _ _ = Some _ |- _ => apply arm_assemble_all_cond_len in H; simpl in H
             | H: arm_assemble_all _ = Some _ |- _ => apply arm_assemble_all_len in H; simpl in H; try rewrite <-H in *
             | H: _ = Some (?irm, _, _), H1: _ = Some ?irm |- _ => try apply arm_assemble_all_cond_len in H1; simpl in H1
             end;
             match goal with |- _ /\ (4 | _) => split; [try lia|try apply N.divide_factor_r] | |- _ => try lia end.
  assert (forall l cond imm24
    (I: In (Z.add i 1) (pol i))
    (RB: rewrite_b_bl l cond imm24 i (pol i) i2i' ai tc = Some (irm', table, tc')),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RBBL. {
    intros. unfold rewrite_b_bl in RB. destruct_match_in RB; try discriminate; inversion RB; subst. destruct_match_in e.
    eapply afterblock_step. easy. easy. now replace_nth O. intros ??? XS.
    remember (_ mod _)%Z.
    eapply exec_GOTOz' with (dest:=Z.to_N (i2i' z1)) in XS. destruct XS. right. right. left. eexists. repeat split. apply H. left. right. repeat eexists. rewrite N2Z.inj_mul, Z2N.id.  reflexivity. apply I2I. now apply In_contains in e0. rewrite Z2N.id by apply I2I. mylia. right. left. repeat split. easy. mylia. left. right. exists (i+1)%Z. split. rewrite N2Z.inj_mul, N2Z.inj_add, Z2N.id, I2I''. easy. apply I2I. easy. lia. specialize (I2I z1). lia. rewrite !Z2N.id by apply I2I. apply e.
    eapply afterblock_step. easy. easy. now replace_nth O. intros ??? XS.
    eapply exec_GOTOz' with (dest:=Z.to_N ai) in XS. destruct XS. right. right. left. eexists. repeat split. apply H. left. left. lia. rewrite Z2N.id. easy. lia. right. left. repeat split. easy. mylia. left. right. exists (i+1)%Z. split. rewrite N2Z.inj_mul, N2Z.inj_add, Z2N.id, I2I''. easy. lia. easy. lia. lia. rewrite !Z2N.id. apply e. lia. lia.
    eapply afterblock_step. easy. easy. now replace_nth O. intros ??? XS.
    eapply exec_GOTOz' with (dest:=Z.to_N ai) in XS. destruct XS. right. right. left. eexists. repeat split. apply H. left. left. lia. rewrite Z2N.id. easy. lia. right. left. repeat split. easy. mylia. left. right. exists (i+1)%Z. split. rewrite N2Z.inj_mul, N2Z.inj_add, Z2N.id, I2I''. easy. lia. easy. lia. lia. rewrite !Z2N.id. apply e0. lia. lia.
  }

  assert (forall irm cond
  (RWT: rewrite_w_table irm tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
  (SI: forall ti sl sr
    (IRM: irm cond i ti sl sr = Some irm')
    (TI: (0 <= ti)%Z)
    (TI': Z.to_N ti + 2 ^ (32 - Z.to_N sr) < 2 ^ 30)
    (SR: (0 <= sr < 32)%Z)
    (N: forall n,
      Z.to_N ti <= n < Z.to_N ti + 2 ^ (32 - Z.to_N sr) ->
      SafeEntry i2i' pol ai i (Z.of_N (getmem 32 (LorB (s1 R_E)) 4 (s1 V_MEM32) (n*4)))
    )
    (NW: forall n k,
      Z.to_N ti <= n < Z.to_N ti + 2 ^ (32 - Z.to_N sr) ->
      k ⊖ n * 4 < 4 -> N.testbit (s1 A_WRITE) k = false
    ),
    SafeAfterBlock i2i' pol ai i (length irm') s1),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RWT. {
    intros. unfold rewrite_w_table in RWT. destruct_match_in RWT; try discriminate.
    inversion RWT. subst. apply SI in e2. easy. apply TC in e. now destruct e. apply TC in e. destruct e.
    apply N2Z.inj_lt. rewrite N2Z.inj_add, N2Z.inj_pow, N2Z.inj_sub, !Z2N.id by lia. lia.
    apply TC in e. now destruct e. intros.
    assert (ee:=e).
    apply TC in e as [table [XT ST']]. unfold SafeTable in ST'. rewrite Forall_forall in ST'.
    eapply TCIM in ee. apply ST' in ee. apply ee. easy. apply table_size_correctness in XT as TS. rewrite TS. unfold compute_table_size.
    rewrite Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. simpl Z.to_N. lia.
    intros. assert (ee:=e). apply TC in e as [table [XT ST']]. eapply NWTC. apply ee. apply XT. apply table_size_correctness in XT as TS. rewrite TS.
    unfold compute_table_size. rewrite Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. simpl Z.to_N. apply H. assumption.
    remember (make_jump_table _ _ _ _ _ _).
    apply find_hash_bound in e0.
    unfold Z32 in *. rewrite Z.shiftl_mul_pow2, Z.mul_1_l in Heql0 by lia.
    inversion RWT. subst. apply SI in e2. easy. easy. apply N2Z.inj_lt. rewrite N2Z.inj_add, N2Z.inj_pow, N2Z.inj_sub, !Z2N.id by lia.
    rewrite make_jump_table_len, Z2Nat.id in TI' by lia. lia.
    lia. intros. rewrite make_jump_table_len, Z_nat_N, Z2N.inj_pow, Z2N.inj_sub in TIM by lia.
    apply TIM in H as IN. unfold SafeTable in ST. rewrite Forall_forall in ST. apply ST in IN. apply IN. intros. eapply NWT.
    rewrite make_jump_table_len, Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. apply H. assumption.
  }

  assert (forall j
    (SE: SafeEntry i2i' pol ai i (Z.of_N j)),
    ~InBlock (i2i' i) (length irm') j) as SENIB.
  {
    intros. destruct SE.
      intro. apply AIB.
        rewrite <-(Z2N.id (ai*4)) in H by lia. apply N2Z.inj in H. rewrite Z2N.inj_mul in H by lia. simpl in H. now rewrite H.
      destruct H as [? [? ?]]. intro. specialize (I2I''' x). mylia.
  }
  assert (forall j
    (SE: SafeEntry i2i' pol ai i (Z.of_N j)),
    (4 | j)) as SE4. {
    intros. destruct SE.
      rewrite <-(Z2N.id (ai*4)) in H by lia. apply N2Z.inj in H. rewrite <-H, Z2N.inj_mul by lia. apply N.divide_factor_r.
      destruct H as [? [? ?]]. rewrite <-(Z2N.id (_*_)) in x0 by lia. apply N2Z.inj in x0.
        specialize (I2I x). rewrite <-x0, Z2N.inj_mul by lia. apply N.divide_factor_r.
  }


  assert (forall reg cond
    (RB: rewrite_bx reg tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
    (R: (0 <= reg < 15)%Z)
    (PA: In (Z.add i 1) (pol i)),
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as RBX. {
    intros. eapply RWT.
    apply RB. intros. eapply C. apply IRM. simpl. lia. assumption.
    destruct arm_assemble_all eqn:B; auto. intros.
    destruct H1.
    eapply after_arm_table_lookup with (prefix:=x).
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B by lia. apply arm_assemble_all_app. apply H1. apply B.
    apply arm_assemble_all_len in H1. now rewrite H1. lia. lia. mylia.
    now apply H0.
    mylia. simpl. lia. lia.
    intros. destruct xs, e. right. mylia. simpl in H3. rewrite Z2N.id in H3 by lia. lia. simpl in H3. easy. easy.

    intros.

  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_bx [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    apply afterblock_step with (z:=z_bx).
    easy. lia.
    rewrite nth_error_app2. replace_nth 7%nat. rewrite nth_error_app2. now rewrite <-BADD. lia. lia.
    intros.
  rewrite DECODE in H5. rewrite <-(Z2N.id reg) in H5 by lia.
  epose proof (N _ H4). subst s'.
  apply exec_bx in H5. rewrite update_updated, !update_frame in H5 by discriminate.
  right. right. left. eexists. repeat split. apply H5. left. easy.
  rewrite Z2N.id by lia. replace (length _) with (length irm') by (rewrite length_app; mylia). apply SENIB. easy. lia.
  rewrite update_updated, !update_frame by discriminate. apply SE4. easy.
  }
  assert (forall reg cond
    (RB: rewrite_blx reg tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
    (R: (0 <= reg < 15)%Z)
    (PA: In (Z.add i 1) (pol i)),
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as RBLX. {
    intros. eapply RWT.
    apply RB. intros. eapply C. apply IRM. simpl. lia. assumption.
    destruct arm_assemble_all eqn:B; auto. intros.
    destruct H1.
    eapply after_arm_table_lookup with (prefix:=x).
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B by lia. apply arm_assemble_all_app. apply H1. apply B.
    apply arm_assemble_all_len in H1. now rewrite H1. lia. lia. mylia.
    now apply H0.
    mylia. simpl. lia. lia.
    intros. destruct xs, e. right. mylia. simpl in H3. rewrite Z2N.id in H3 by lia. lia. simpl in H3. easy. easy.

    intros.

  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_bx [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    apply afterblock_step with (z:=z_bx).
    easy. lia.
    rewrite nth_error_app2. replace_nth 7%nat. rewrite nth_error_app2. now rewrite <-BADD. lia. lia.
    intros.
  rewrite DECODE in H5. rewrite <-(Z2N.id reg) in H5 by lia.
  epose proof (N _ H4). subst s'.
  apply exec_blx in H5. rewrite update_updated, !update_frame in H5 by discriminate.
  right. right. left. eexists. repeat split. apply H5. left. easy.
  rewrite Z2N.id by lia. replace (length _) with (length irm') by (rewrite length_app; mylia). apply SENIB. easy. lia.
  rewrite update_updated, !update_frame by discriminate. apply SE4. easy.
  }

  assert (forall sanitized_inst r0 r1 r2 r3 r4 r5 cond
  (RPC: rewrite_pc_sp sanitized_inst (unused_reg r0 r1 r2) (unused_reg_high r3 r4 r5) tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
  (FT: forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a) /\ s' R_E = s R_E)
  (IN: In (Z.add i 1) (pol i)),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RPS. {
    intros. eapply RWT. apply RPC. intros. eapply C. apply IRM. simpl. lia. assumption.
    clear RWT RPC C RBX NWTC NWT TCIM TIM AIB I2I''' TI TI' MB.
    destruct arm_assemble_all eqn:B; auto. intros pre pc L MO P MB. apply MO in M. clear MO. simpl in L. assert (B':=B). move B' after IRM.

    apply arm_assemble_all_first in B as [z_stmdb3 [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth O.
    mylia. intros ??? XS. epose proof (pres_frame_exec_stmt M M (welltyped_arm2il _ _ _) XS) as M'. assert (XS'':=XS).
    rewrite DECODE in XS; clear DECODE.
    destruct (Ndivdec 4 (s1 R_SP)). shelve.
    apply exec_stmdb3_e in XS. right. right. right. now exists 16. now rewrite update_frame by discriminate. Unshelve. mylia.
    apply exec_stmdb3 in XS as [S' X]. rewrite !update_frame, update_cancel in S' by (unfold arm_varid;destruct_match;discriminate).
    rewrite S' in *. remember (update (update _ _ _) _ _) as s_1. subst x.
    left. repeat split. clear MB; intro MB.

    apply arm_assemble_all_first in B as [z_mov [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 1%nat. lia. intros ??? XS.
    eapply reset_temps_models in M'. rewrite S' in M'. epose proof (pres_frame_exec_stmt M' M' (welltyped_arm2il _ _ _) XS) as M''.
    rewrite DECODE in XS; clear DECODE.
    rewrite <-(Z2N.id (unused_reg_high _ _ _)) in XS by (apply unused_reg_bound; unfold Z4; lia).
    apply exec_mov in XS as [S'' X]. subst x. remember (update (update s_1 _ _ ) _ _) as s_2. rewrite S'' in *.
    left. repeat split. clear MB; intro MB.

   
    apply arm_assemble_all_first in B as [z_movw [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 2%nat. lia. intros ??? XS.
    eapply reset_temps_models in M''. rewrite S'' in M''. epose proof (pres_frame_exec_stmt M'' M'' (welltyped_arm2il _ _ _) XS) as M'''.
    rewrite DECODE in XS; clear DECODE.
    rewrite <-(Z2N.id (unused_reg _ _ _ )) in XS. apply exec_movwt in XS as [regval [REGVAL [S''' X]]]. subst x. rewrite S''' in *.
    remember (update (update s_2 _ _) _ _) as s_3.
    left. repeat split. clear MB;intro MB.

    apply arm_assemble_all_first in B as [z_movt [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 3%nat. lia. intros ??? XS.
    eapply reset_temps_models in M'''. rewrite S''' in M'''. epose proof (pres_frame_exec_stmt M''' M''' (welltyped_arm2il _ _ _) XS) as M''''.
    rewrite DECODE in XS; clear DECODE.
    rewrite <-(Z2N.id (unused_reg _ _ _ )) in XS. apply exec_movwt in XS as [regval2 [REGVAL2 [S'''' X]]]. subst x. rewrite S'''' in *.
    remember (update (update s_3 _ _) _ _) as s_4.
    left. repeat split. clear MB;intro MB. shelve. right. mylia. easy. unfold unused_reg, _unused_reg. destruct_match; simpl; lia.
    rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.shiftr_nonneg, Z.land_nonneg. right. unfold Z0xffff. lia.
    unfold Z15; lia. rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.land_nonneg. right. unfold Z0xffff. lia.
    unfold Z4095. lia. unfold unused_reg, _unused_reg. destruct_match; cbv; discriminate. right . mylia. easy. unfold unused_reg, _unused_reg. destruct_match; now cbv. rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.shiftr_nonneg. apply Z.land_nonneg. right. cbv; discriminate. cbv; discriminate. rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.land_nonneg. right. cbv; discriminate. cbv. discriminate. unfold unused_reg, _unused_reg. destruct_match; cbv; discriminate. right. mylia. unfold unused_reg_high, _unused_reg. now destruct_match. right. mylia.
    Unshelve. now rewrite update_frame by discriminate. mylia. mylia. mylia.

    apply arm_assemble_all_first in B as [z_sanitized [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 4%nat. mylia. intros ??? XS.
    eapply reset_temps_models in M''''. rewrite S'''' in M''''. epose proof (pres_frame_exec_stmt M'''' M'''' (welltyped_arm2il _ _ _) XS) as M'''''.
    rewrite DECODE in XS; clear DECODE.
    destruct x. destruct e. eapply FT in XS as [? _]. contradiction. right. right. right. now eexists. left. repeat split. clear MB; intro MB.
    2: right; mylia.
    destruct P as [p P]. assert (XS':=XS).
    eapply FT in XS as [_ E].
    eapply after_arm_table_lookup with (prefix:=p++_). rewrite <-app_assoc. apply arm_assemble_all_app. easy.
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr) in B' by lia. rewrite <-(Z2N.id (unused_reg _ _ _)) in B' by (unfold unused_reg, _unused_reg; destruct_match;cbv;discriminate). apply B'. rewrite length_app. simpl length. replace (N.of_nat _) with (N.of_nat (length pre) + 1+1+1+1+1) by mylia. rewrite !N.add_assoc. easy.
    unfold unused_reg,_unused_reg. now destruct_match. lia. mylia. now apply reset_temps_models. mylia. mylia. mylia.
    intros. destruct xs, e. unfold InBlockX in H. simpl in H. right. mylia. easy. unfold InBlockX in H. now simpl in H.
    clear MB; intros ?? MB NB. remember (length _) in s'4. rewrite length_app in Heqn0. simpl in Heqn0.
    remember (getmem _ _ _ _ _) in s'4. rewrite !reset_temps_not_temp, E in Heqn1 by discriminate. erewrite <-(nonwritable_mem_arm2il _ _ _ _ _ _ _ _ _ _ _ XS') in Heqn1.
    rewrite Heqs_4, !update_frame, Heqs_3, !update_frame, Heqs_2, !update_frame in Heqn1 by (unfold arm_varid; destruct_match;discriminate).
    rewrite <-S', <-(nonwritable_mem_arm2il _ _ _ _ _ _ _ _ _ _ _ XS''), S', Heqs_1, !update_frame in Heqn1.
    shelve. 1-3: discriminate.
    intro. now apply NW.
    rewrite Heqs_4, !update_frame, Heqs_3, !update_frame, Heqs_2, !update_frame, Heqs_1, !update_frame by (unfold arm_varid; destruct_match;discriminate).
    intro. now apply NW. Unshelve. mylia. apply 0.

  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst b; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_str [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step. easy. lia. rewrite nth_error_app2. replace_nth 12%nat. rewrite !nth_error_cons, nth_error_app2, <-BADD. easy. lia. lia.
  intros ??? XS. rewrite DECODE in XS. rewrite <-(Z2N.id (unused_reg _ _ _)), <-(Z2N.id (unused_reg_high _ _ _)) in XS by (apply unused_reg_bound; unfold Z4; lia).
  change Z_4 with (-Z.of_N 4) in XS. apply exec_str in XS as [S''''' X]. subst x.  remember (update (update s'4 _ _) _ _) as s_5. rewrite S''''' in *.
  left. repeat split. clear MB; intro MB.

  shelve. right. mylia. unfold unused_reg, _unused_reg; now destruct_match. unfold unused_reg_high, _unused_reg; now destruct_match. lia.
  subst s'4. apply models_update. rewrite typeof_arm_varid. subst n1. apply typesafe_getmem. apply models_update. simpl. mylia. apply reset_temps_models. easy.
  Unshelve.
  clear DECODE.
  apply arm_assemble_all_first in B as [z_ldmdb3 [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  remember (getmem 32 (LorB (s_5 R_E)) 4 (s_5 V_MEM32) (s_5 (arm_varid (Z.to_N (unused_reg_high r3 r4 r5))) ⊖ 4)) as dest.
  enough (SafeEntry i2i' pol ai i (Z.of_N dest)).
  eapply afterblock_step.  assumption. lia. rewrite nth_error_app2. replace_nth 13%nat. rewrite !nth_error_cons, nth_error_app2, <-BADD. easy. lia. lia.
  intros ??? XS. rewrite DECODE in XS.
  subst dest.
  apply exec_ldmdb3 in XS. destruct XS.  right. right. left. eexists. repeat split. apply H0. now left. replace (length _) with (length irm') by mylia. rewrite Z2N.id by lia. now apply SENIB. right. right. right. now exists 16. now apply SE4. subst dest.
  rewrite Heqs_5, update_updated, !update_frame. subst s'4. rewrite update_updated, !update_frame. rewrite !reset_temps_not_temp.
    rewrite getmem_setmem by lia. subst n1. rewrite N.mod_small by apply typesafe_getmem. now apply N. all: try discriminate.
    all: unfold unused_reg_high, unused_reg, _unused_reg; destruct_match; simpl; discriminate.
  }
  assert (forall sanitized_inst reg cond
  (RPC: rewrite_pc sanitized_inst reg tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
  (FT: forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a) /\ s' R_E = s R_E)
  (R: (0 <= reg < 13)%Z)
  (IN: In (Z.add i 1) (pol i)),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RP. {
    intros. eapply RWT. apply RPC. intros. eapply C. apply IRM. simpl. lia. assumption.
    clear RWT RPC C RBX NWTC NWT TCIM TIM  AIB I2I''' TI TI' MB.
    destruct arm_assemble_all eqn:B; auto. intros pre pc L MO P MB. apply MO in M. clear MO. simpl in L. assert (B':=B). move B' after IRM.

    apply arm_assemble_all_first in B as [z_str [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth O. mylia. intros ??? XS. assert (XS':=XS). rewrite DECODE in XS; clear DECODE.
    change Z_4 with (- Z.of_N 4) in XS. change SP with (Z.of_N 13) in XS.
    rewrite <-(Z2N.id reg) in XS by lia. apply exec_str in XS as [S' X]; [|lia..|now apply M]. rewrite !update_cancel, !update_frame in S' by discriminate. epose proof (pres_frame_exec_stmt M M (welltyped_arm2il _ _ _) XS') as M'. eapply reset_temps_models in M'. rewrite S' in *. remember (update (update _ _ _) _ _) as s_1. Unshelve. 2: mylia.
    left. repeat split. assumption. clear MB; intros MB. subst x.

    apply arm_assemble_all_first in B as [z_movw [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 1%nat. lia. intros ??? XS.
    epose proof (pres_frame_exec_stmt M' M' (welltyped_arm2il _ _ _) XS) as M''. rewrite DECODE in XS;clear DECODE.
    rewrite <-(Z2N.id reg) in XS by lia. apply exec_movwt in XS as [regval [REGVAL [S'' X]]];
    [| assumption| lia| rewrite Z2N_inj_land..]. shelve. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.shiftr_nonneg, Z.land_nonneg. right. unfold Z0xffff. lia. unfold Z15. lia. eapply N.le_lt_trans. apply N.land_le_r.  simpl. lia. apply Z.land_nonneg. right. unfold Z0xffff. lia.   unfold Z4095. lia. right. mylia. Unshelve. mylia.
    eapply reset_temps_models in M''. rewrite S'' in *; clear S'' . remember (update (update s_1 _ _) _ _) as s_2.
    left. repeat split. assumption. clear MB; intros MB.

    apply arm_assemble_all_first in B as [z_movt [b_tail [B [B_B' DECODE]]]]; subst b x; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 2%nat. lia. intros ??? XS. epose proof (pres_frame_exec_stmt M'' M'' (welltyped_arm2il _ _ _) XS) as M'''. Unshelve. rewrite DECODE in XS;clear DECODE.
    rewrite <-(Z2N.id reg) in XS by lia. apply exec_movwt in XS as [regval2 [X1 [S''' X]]];
    [shelve| assumption|..]. lia. rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.shiftr_nonneg, Z.land_nonneg. right. unfold Z0xffff. lia. unfold Z15.  lia. rewrite Z2N_inj_land. eapply N.le_lt_trans. apply N.land_le_r. simpl. lia. apply Z.land_nonneg. right. unfold Z0xffff. lia. unfold Z4095.  lia. right. mylia. mylia. Unshelve. subst x. remember (update (update s_2 _ _) _ _) as s_3.
    left. repeat split. clear MB; intros MB.

    apply arm_assemble_all_first in B as [z_sanitized [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 3%nat. lia. intros ??? XS. destruct x.
      destruct e. rewrite DECODE in XS. now eapply FT in XS as [XS _].  right. right. right. now exists i0.
    left. repeat split. clear MB; intros MB. 2, 3: right; mylia.

    destruct P as [p P].
      eapply reset_temps_models in M'''. epose proof (pres_frame_exec_stmt M''' M''' (welltyped_arm2il _ _ _) XS) as M''''.
    eapply after_arm_table_lookup with (prefix:=p++_).
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B' by lia. rewrite <-app_assoc. apply arm_assemble_all_app. apply P. apply B'. rewrite length_app. simpl length. replace (N.of_nat _) with (N.of_nat (length pre) + 1 + 1 +1 +1) by mylia. rewrite !N.add_assoc. apply MB. lia. lia.
      mylia.
      now apply reset_temps_models.
      mylia.
      simpl. lia.
      lia.
      intros. simpl. destruct xs, e. simpl in H. right. split. mylia. simpl in H. lia. now inversion H. easy.
      clear MB; intros ?? MB NB.

      remember (length _) in s'3. rewrite length_app in Heqn0. simpl length in Heqn0. subst n0. remember (_ _ _ R_E) in s'3. rewrite reset_temps_not_temp in Heqy by discriminate. rewrite DECODE in XS. apply FT in XS as E. rewrite E, S''', Heqs_3, !update_frame, Heqs_2, !update_frame, Heqs_1, !update_frame in Heqy by (unfold arm_varid;destruct_match;discriminate).  subst y. Unshelve. 2: apply 0. 2: mylia. remember (getmem _ _ _ _ _) in s'3. rewrite reset_temps_not_temp in Heqn0 by discriminate. erewrite <-(nonwritable_mem_arm2il _ _ _ _ _ _ _ _ _ _ _ XS) in Heqn0. rewrite S''', Heqs_3, !update_frame, Heqs_2, !update_frame, <-S'  in Heqn0. rewrite reset_temps_not_temp in Heqn0. erewrite <-(nonwritable_mem_arm2il _ _ _ _ _ _ _ _ _ _ _ XS'), update_frame in Heqn0. shelve.
      all: try discriminate. rewrite update_frame by discriminate. intro. now apply NW. 1,2:unfold arm_varid;destruct_match;discriminate. intro. rewrite S''', Heqs_3,Heqs_2, Heqs_1, !update_frame by (unfold arm_varid; destruct_match;discriminate). now apply NW. Unshelve. clear E. subst n0. clear DECODE. clear XS XS'.
  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst b; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_align [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step. simpl in MB. now rewrite <-!N.add_assoc in *. lia. rewrite nth_error_app2. replace_nth 11%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth O. lia. lia.
   intros ??? XS. rewrite DECODE in XS; clear DECODE.
   assert (models armc s'3) as M3. subst s'3. apply models_update. rewrite typeof_arm_varid. apply typesafe_getmem. apply models_update. simpl. mylia. now apply reset_temps_models.
  apply exec_align in XS as [S'''' X]. subst x. remember (update (update s'3 _ _ ) _ _ ) as s_4. rewrite S'''' in *.
  left. repeat split.  clear MB; intros MB. shelve. right. mylia. assumption. Unshelve.

  apply arm_assemble_all_first in B as [z_str' [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step. now rewrite <-!N.add_assoc in *. lia. rewrite nth_error_app2. replace_nth 12%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth 1%nat. lia. lia.
  intros ??? XS. rewrite DECODE in XS; clear DECODE.
  change SP with (Z.of_N 13) in XS. change Z_8 with (-Z.of_N 8) in XS.
  rewrite <-(Z2N.id reg) in XS by lia.
  apply exec_str in XS as [S''''' ?]; [|lia..|]. subst x. remember (update (update s_4 _ _) _ _) as s_5. rewrite S''''' in *.
  left. repeat split. clear MB; intros MB. shelve. right. mylia. rewrite Heqs_4. apply models_update. simpl. specialize (M3 R_SP _ eq_refl). lia. apply models_update. simpl. mylia. assumption. Unshelve.

  apply arm_assemble_all_first in B as [z_ldr [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step. assumption. lia. rewrite nth_error_app2. replace_nth 13%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth 2%nat. lia. lia.
  intros ??? XS. rewrite DECODE in XS; clear DECODE.
  rewrite <-(Z2N.id reg), <-(Z2N.id SP) in XS. change Z_4 with (-Z.of_N 4) in XS. apply exec_ldr' in XS as [S'''''' ?]. subst x.
  remember (update (update s_5 _ _) _ _) as s_6.
  rewrite S'''''' in *.
  left. repeat split. clear MB; intros MB.

  apply arm_assemble_all_first in B as [z_ldr' [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  remember (getmem 32 (LorB (s_6 R_E)) 4 (s_6 V_MEM32) (s_6 R_SP ⊖ 8)) as dest.
  enough (SafeEntry i2i' pol ai i (Z.of_N dest)).
  eapply afterblock_step. assumption. lia. rewrite nth_error_app2 by lia. replace_nth 14%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth 3%nat. lia.
  intros ??? XS. rewrite DECODE in XS; clear DECODE.
  eapply exec_ldrpc in XS.
  right. right. left. eexists. repeat split. apply XS. left. now rewrite <-Heqdest. rewrite <-Heqdest, Z2N.id by lia. replace (length _) with (length irm') by mylia. now apply SENIB. rewrite <-Heqdest. now apply SE4. rewrite Heqs_6, !update_frame, Heqs_5, !update_frame, Heqs_4, update_updated by (unfold arm_varid;destruct_match_eqn;discriminate||lia).  apply N.divide_factor_r.
  subst dest.
  clear MB.
  { rewrite Heqs_6, !update_frame, Heqs_5, !update_frame, update_updated, !update_frame, getmem_setmem, Heqs_4, !update_frame by (unfold arm_varid;destruct_match_eqn;discriminate||lia).
    subst s'3. rewrite update_updated, N.mod_small by apply typesafe_getmem. now apply N.
  }

  right. mylia. lia. unfold SP, Z13. lia. lia. unfold SP, Z13. lia. lia.
    }
  assert (
    forall l cond, arm_assemble_all_cond l cond = Some irm' ->
      (Forall (fun q => forall s c' s' x i a, exec_stmt armc s (arm2il i q) c' s' x  -> x <> Some (Addr a)) l) ->
      (1 <= length l < 64)%nat ->
      In (Z.add i 1) (pol i) ->
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as FT. {
    intros. eapply C. apply H. assumption. assumption.
    destruct arm_assemble_all eqn:e; auto.
    intros. apply afterblock_fallthru.
      apply arm_assemble_all_eq in e. rewrite <-e, Forall_map in H0. assumption.
      intros. cbv[SafeDestX fst]. right.
      apply arm_assemble_all_cond_len in H.  apply arm_assemble_all_len in e. unfold InBlock in *. split. mylia. easy.
        apply arm_assemble_all_len in e. lia. assumption.
        intros. cbv[SafeDestX fst SafeDest]. left. right. exists (i+1)%Z. split. rewrite I2I''. mylia. apply arm_assemble_all_len in e. apply arm_assemble_all_cond_len in H. assumption.
  }
  assert (forall op Rn register_list reg W cond
    (RL: rewrite_ldm_pc op Rn register_list reg (ARM_lsm op cond W Rn register_list) tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
    (R: (0 <= reg < 15)%Z)
    (RN: (0 <= Rn < 15)%Z)
    (RRN: (reg <> Rn))
    (RGL: (0 <= register_list)%Z)
    (OP: match op with | ARM_STMDA | ARM_STMDB | ARM_STMIA | ARM_STMIB => False | _ => True end)
    (R15: (Z.testbit register_list 15 = true))
    (IN: In (Z.add i 1) (pol i)),
    SafeAfterBlock i2i' pol ai i (length irm') s1) as RL. {
    intros. eapply RWT. apply RL. intros. eapply C. apply IRM. simpl. lia. assumption.
    clear RWT RL C RBX NWTC NWT TCIM TIM  AIB I2I''' TI TI' MB RPS RP FT.
    destruct arm_assemble_all eqn:B; auto. intros pre pc L MO P MB. apply MO in M. clear MO. simpl in L. assert (B':=B). move B' after IRM.

    apply arm_assemble_all_first in B as [z_str [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth O. mylia. intros ??? XS. assert (XS':=XS). rewrite DECODE in XS; clear DECODE.
    change Z_4 with (- Z.of_N 4) in XS. change SP with (Z.of_N 13) in XS.
    rewrite <-(Z2N.id reg) in XS by lia. apply exec_str in XS as [S' X]; [|lia..|now apply M]. rewrite !update_cancel, !update_frame in S' by discriminate. epose proof (pres_frame_exec_stmt M M (welltyped_arm2il _ _ _) XS') as M'. eapply reset_temps_models in M'. rewrite S' in *. remember (update (update _ _ _) _ _) as s_1. Unshelve. 2: mylia.
    left. repeat split. assumption. clear MB; intros MB. subst x. 2: right;mylia.

    apply arm_assemble_all_first in B as [z_ldr [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. rewrite nth_error_app2. now replace_nth 1%nat. mylia. intros ??? XS.
    epose proof (pres_frame_exec_stmt M' M' (welltyped_arm2il _ _ _) XS) as M''.
    pose proof (fun j => nonwritable_mem_arm2il _ _ _ _ _ _ _ j 32 (LorB (s1 R_E)) 4 XS).
    rewrite <-S' in H.
    rewrite DECODE in XS; clear DECODE.
    rewrite <-(Z2N.id reg), <-(Z2N.id Rn) in XS by lia.
    apply exec_ldr'' in XS as [? [? X]]. left. repeat split. easy. 2: right; mylia. 2-3: lia.
    clear MB; intro MB.



    destruct P as [p P].
    eapply after_arm_table_lookup with (prefix:=p++_).

    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B' by lia. rewrite <-app_assoc. apply arm_assemble_all_app. apply P. apply B'. rewrite length_app. simpl length. replace (N.of_nat _) with (N.of_nat (length pre) + 1 +1) by mylia. rewrite !N.add_assoc. apply MB. lia. lia. mylia. now apply reset_temps_models. mylia. mylia.
    lia. replace (length _) with (length irm') by mylia. intros. destruct xs, e. right. mylia. simpl in H1. mylia. apply H1. easy.
    intros. remember _ in s'1. rewrite length_app in Heqy. simpl in Heqy. rewrite !update_frame, !reset_temps_not_temp in Heqy.
    all: try discriminate. 2: apply arm_varid_not_pc; lia.

  apply arm_assemble_all_split in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst b; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_str' [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.

  eapply afterblock_step. easy. lia. rewrite nth_error_app2. replace_nth 9%nat. rewrite !nth_error_cons, nth_error_app2, <-BADD. easy. lia. lia.
  intros ??? XS. rewrite DECODE in XS.
  rewrite <-(Z2N.id reg), <-(Z2N.id Rn) in XS by lia. apply exec_str' in XS as [S'' ?]; [| lia..].
  left. repeat split. easy. 2: right; mylia. rewrite S'' in *. remember (update (update s'1 _ _) _ _). clear MB; intro MB.

  clear DECODE.
  apply arm_assemble_all_first in B as [z_ldr' [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step.  easy. lia. rewrite nth_error_app2. replace_nth 10%nat. rewrite !nth_error_cons, nth_error_app2, <-BADD. easy. lia. lia.
  intros ??? XS. rewrite DECODE in XS.
  rewrite <-(Z2N.id reg), <-(Z2N.id SP) in XS by (unfold SP, Z13;lia). change Z_4 with (-Z.of_N 4) in XS. subst x.
  apply exec_ldr' in XS as [S''' X]. left. repeat split. easy. clear MB; intro MB.  rewrite S''' in *. remember (update (update n0 _ _) _ _).

  clear DECODE.
  apply arm_assemble_all_first in B as [z_orig [b_tail [B [B_B' DECODE]]]]; subst b; rename b_tail into b.
  eapply afterblock_step.  easy. lia. rewrite nth_error_app2. replace_nth 11%nat. rewrite !nth_error_cons, nth_error_app2, <-BADD. easy. lia. lia.
  intros ??? XS. rewrite DECODE in XS.
  rewrite <-(Z2N.id Rn), <-(Z2N.id register_list) in XS by lia.
  eapply exec_ldm in XS.
  destruct XS. rewrite Heqn1, !update_frame in H4 by (try (apply arm_varid_different;lia); unfold arm_varid; destruct_match_eqn; lia || discriminate).
  rewrite Heqn0, !update_updated, !update_frame in H4. cbn zeta in H4. rewrite N2Z.inj_mod, Z2N.id in H4 by lia. rewrite getmem_setmem in H4.
  subst s'1. rewrite Heqy, update_updated in H4.
  erewrite <-reset_temps_not_temp, !H0, !update_frame in H4 by (unfold arm_varid; destruct_match;discriminate).
  rewrite <-H in H4.
  rewrite <-(nonwritable_mem_arm2il _ _ _ _ _ _ _ _ _ _ _ XS') in H4. rewrite update_frame in H4 by discriminate.
  rewrite N.mod_small in H4.
  remember (getmem _ _ _ (s1 V_MEM32) _) as dest.
  enough (SafeEntry i2i' pol ai i (Z.of_N dest)).
  right. right. left. exists dest. specialize (SE4 dest H5). apply H4 in SE4. split. easy. split. now left.
  replace (length _) with (length irm') by mylia. rewrite Z2N.id by lia. now apply SENIB.
  subst dest. now apply N. apply typesafe_getmem.
  intro. now eapply NW. intro. rewrite S', !update_frame by discriminate. now eapply NW.
  lia. apply arm_varid_not_pc. lia. unfold arm_varid; destruct_match; discriminate. discriminate. discriminate.
  destruct H4. right. left. repeat split. easy. mylia. left. right. exists (i+1)%Z. eexists. mylia. easy. right. right. right. now exists 16. Unshelve.
  rewrite <-(Z2N.id register_list), <-(Z2N.id 15), Z.testbit_of_N in R15 by lia. simpl in R15. apply R15.
  lia.
  easy. right. mylia. lia. simpl. lia. lia. mylia.
      }

  assert (
    forall sanitized_inst cond reg tc,
      rewrite_pc_no_jump sanitized_inst cond i reg tc = Some (irm', table, tc') ->
      (forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a)) ->
      reg <> 15%Z ->
      In (Z.add i 1) (pol i) ->
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as RPNJ. {
    intros. eapply FT. unfold rewrite_pc_no_jump, wo_table in H. destruct_match_in H; try discriminate.
    inversion H. subst. apply e. faft. simpl. lia. assumption.
  }
  assert (
    forall sanitized_inst cond reg reg2 tc,
      rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc = Some (irm', table, tc') ->
      (forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a)) ->
      (0 <= reg < 15)%Z ->
      (0 <= reg2 < 15)%Z ->
      In (Z.add i 1) (pol i) ->
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as RPSNJ. {
    intros. eapply FT. unfold rewrite_pc_sp_no_jump, wo_table in H. destruct_match_in H; try discriminate.
    inversion H. subst. apply e. faft. simpl. lia. assumption.
  }
  assert (goto_abort (i2i' i) ai tc = Some (irm', table, tc') -> SafeAfterBlock i2i' pol ai i (length irm') s1) as GA.
  {
    intros. unfold goto_abort in H; destruct_match_in H; try discriminate. inversion H; subst.
    eapply afterblock_step. assumption. easy. now replace_nth O. intros. right. right. left. rewrite <-(Z2N.id (i2i' i)), <-(Z2N.id ai) in e by (apply I2I' || lia).
    eapply GOTOz_correct in e. exists (Z.to_N ai * 4). repeat split. apply e. unfold SafeDestX. simpl. left. left. lia. mylia. lia.  lia. apply H0.
  }
  assert (
    irm' = z::nil ->
    In (Z.add i 1) (pol i) ->
    (forall c s c' s' x a, exec_stmt c s (arm2il (Z.to_N (i2i' i) * 4) (arm_decode z)) c' s' x -> x <> Some (Addr a)) ->
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as FTS. {
    intros. subst.
    eapply afterblock_step. assumption. easy. now replace_nth O. intros.
    destruct x eqn:e. destruct e0. now eapply H1 in H. right. right. right. now exists i0. right. left. split. easy. split. simpl. lia.
    unfold SafeDestX, SafeDest. simpl. left. right. exists (Z.add i 1). split. rewrite I2I''. simpl. lia. easy.
  }

  unfold rewrite_inst, PC, Z1, Z15 in RI. destruct_match_in RI; try discriminate;
  match type of RI with
  | context[goto_abort] => now apply GA
  | context[Some (z::nil, _, _)] => apply FTS; [now inversion RI| rewrite negb_false_iff in e; now apply In_contains in e|faft]
  | context[rewrite_mov_lr_pc]=>
    unfold rewrite_mov_lr_pc, wo_table in RI; destruct_match_in RI; try discriminate; inversion RI; subst; eapply FT; [apply e4|faft| simpl; lia|rewrite negb_false_iff in e; now apply In_contains in e]
  | context[wo_table]=>
    unfold wo_table in RI; destruct_match_in RI; try discriminate; inversion RI; subst; eapply FT; [apply e6|faft| simpl; lia|rewrite negb_false_iff in e; now apply In_contains in e]
  | context[rewrite_pc_no_jump] => eapply RPNJ; [apply RI|faft|try apply unused_reg_not_pc;easy ..|rewrite negb_false_iff in e;now apply In_contains in e]
  | context[rewrite_pc_sp_no_jump]=> eapply RPSNJ; [apply RI|faft|try apply unused_reg_bound;easy ..|rewrite negb_false_iff in e;now apply In_contains in e]
  | context[rewrite_bx] => eapply RBX; [apply RI|lia|assumption]
  | _ => clear C FT FTS RPNJ RPSNJ
  end.
  eapply RP. apply RI. split. eapply arm_data_r_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_data_r_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_data_r_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_data_r_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_data_i_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_data_i_fallthru in H. intro. now subst x. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RBBL. rewrite negb_false_iff in e; now apply In_contains in e. apply RI.
  eapply RBX. apply RI. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RBLX. apply RI. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_i_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_i_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_i_fallthru in H. intro. now subst x. left. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_i_fallthru in H. intro. now subst x. left. apply unused_reg_not_pc. lia. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RPS. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RP. apply RI. split. eapply arm_ls_r_fallthru in H. intro. now subst x. left. unfold unused_reg, _unused_reg. now destruct_match. shelve. unfold unused_reg, _unused_reg. now destruct_match. rewrite negb_false_iff in e; now apply In_contains in e.
  intros ?????? XS. rewrite orb_true_iff in e2. destruct e2. eapply arm_lsm_noj in XS. apply XS. rewrite N.testbit_false, <-N.shiftr_div_pow2, (shiftr_mod_xbits _ _ 1), xbits_Z2N. unfold bitb in H. rewrite zxbits_eq in H. simpl in *. lia. lia. eapply arm_lsm_noj' in XS. apply XS. now destruct op.
  eapply RL. apply RI. lia. lia. lia. lia. shelve. rewrite Z.testbit_true, <-Z.shiftr_div_pow2 by lia. apply Z2N.inj. lia. lia. rewrite Z2N.inj_mod, Z2N_inj_shiftr, (shiftr_mod_xbits _ _ 1), xbits_Z2N by (try apply Z.shiftr_nonneg; lia). simpl. rewrite orb_false_iff in e2. destruct e2. apply bitb_not0 in H. unfold bitb in H. rewrite zxbits_eq in H. simpl in *. lia. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RL. apply RI. lia. lia. lia. lia. shelve. rewrite Z.testbit_true, <-Z.shiftr_div_pow2 by lia. apply Z2N.inj. lia. lia. rewrite Z2N.inj_mod, Z2N_inj_shiftr, (shiftr_mod_xbits _ _ 1), xbits_Z2N by (try apply Z.shiftr_nonneg; lia). simpl. rewrite orb_false_iff in e2. destruct e2. apply bitb_not0 in H. unfold bitb in H. rewrite zxbits_eq in H. simpl in *. lia. rewrite negb_false_iff in e; now apply In_contains in e.
  eapply RBBL. rewrite negb_false_iff in e; now apply In_contains in e. inversion RI. reflexivity.
  eapply RBBL. rewrite negb_false_iff in e; now apply In_contains in e. inversion RI. reflexivity.
  Unshelve.
  all: match goal with |- _ R_E = _ R_E =>
  eapply noassign_stmt_same in H; [inversion H;symmetry; apply H1|];
  unfold noassign; cbv[arm2il]; repeat (match goal with |- allassigns _ (_ $; ?a) => unfold_rec a end; destruct_match_eqn); repeat constructor; (discriminate || apply arm_varid_not_e || destruct_match; repeat constructor; discriminate ||
  match goal with H: (Z.to_N (unused_reg ?a ?b ?c) =? 15) = true |- _ => unfold unused_reg in H; epose proof (unused_reg_bound 0 a b c); lia end) | _ => idtac end.

  lia. lia. rewrite orb_false_iff in e2. now destruct op. rewrite orb_false_iff in e2. now destruct op.
Qed.
Print Assumptions SafeDest_rewrite_inst.
