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
  (i * 4 <= Z.of_N da' < (i + Z.of_nat ilen) * 4 /\ N.divide 4 da')%Z.
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
  forall i', InBlock i (length b) (i'*4) ->
    match nth_error b (Z.to_nat (Z.of_N i' - i)) with
    | Some z => arm_prog s (i'*4) = Some (4, arm2il (i'*4) (arm_decode z))
    | None => False
    end.
Definition InBlockX i ilen (x: exit * store) :=
  match fst x with
  | Addr a => InBlock (Z.of_N i) ilen a
  | _ => False
  end.

Lemma inblock_start {i ilen}: InBlock (Z.of_N i) (S ilen) (i*4).
Proof.
  split. lia. now exists i.
Qed.
Lemma inblockx_s:
  forall i ilen x, InBlockX i ilen x /\ fst x <> Addr (i*4) -> InBlockX (i+1) (ilen-1) x.
Proof.
  unfold InBlockX. intros. destruct x, e. simpl in *.
    destruct H as [[[? ?] [? ?]] ?]. repeat split; [destruct (N.eq_dec x i); [now subst | lia] | lia | now exists x].
    easy.
Qed.
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
  destruct (Ndivdec 4 a), (Z_le_dec (i * 4) (Z.of_N a)), (Z_lt_dec (Z.of_N a) ((i + Z.of_nat ilen) * 4)).
  all: (now left) || (now right).
Qed.
Lemma inblockx_dec : forall i ilen a, {InBlockX i ilen a} + {~InBlockX i ilen a}.
Proof.
  intros. destruct a, e. apply inblock_dec. now right.
Qed.

Definition AfterBlock (P: exit * store -> Prop) s bi len ei T :=
  forall t0 t1 a' s'
    (XP: exec_prog arm_prog ((Addr a', s')::t1++(Addr (ei*4), s)::t0))
    (T1: Forall T t1)
    (IB: Forall (InBlockX bi len) (t1++(Addr (ei*4), s)::nil)),
    P (Addr a', s').

Definition DuringBlock P s bi len ei T := AfterBlock (fun xs => P xs \/ ~InBlockX bi len xs) s bi len ei T.
Definition DuringBlock' (P: _ -> Prop) s bi len ei T :=
  forall t0 t1 a' s'
    (XP: exec_prog arm_prog ((Addr a', s')::t1++(Addr (ei*4), s)::t0))
    (T1: Forall T t1)
    (IB: Forall (InBlockX bi len) ((Addr a', s')::t1++(Addr (ei*4), s)::nil)),
    P (Addr a', s').
Lemma db_db': forall P s bi len ei T, DuringBlock P s bi len ei T <-> DuringBlock' P s bi len ei T.
Proof.
  intros. unfold DuringBlock, DuringBlock', AfterBlock. split.
    intros. apply H in XP. destruct XP. easy. now inversion IB. easy. now inversion IB.
    intros. destruct (inblockx_dec bi len (Addr a', s')).
      apply H in XP. now left. easy. constructor. easy. easy.
      now right.
Qed.

Definition MaintainsBlock b bi ei s :=
  ContainsBlock b s (Z.of_N bi) /\ DuringBlock (fun xs => ContainsBlock b (snd xs) (Z.of_N bi)) s bi (length b) ei (fun _ => True).

Lemma containsblock_cons:
  forall b b' s i, ContainsBlock (b::b') s i -> ContainsBlock b' s (i+1).
Proof.
  intros. unfold ContainsBlock, InBlock. intros. specialize (H i').
  rewrite <-(Z.add_simpl_r i 1) in H at 2.
  rewrite Z.sub_sub_distr, Z2Nat.inj_add, Nat.add_1_r, nth_error_S in H by lia. apply H.
  simpl. split. lia. easy.
Qed.

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
Lemma forall_last{A}:
  forall (P: A -> Prop) y x1 t1 t2 x2,
    y::x1::t1 = t2 ++ x2::nil ->
    Forall P (x1::t1) ->
    P x2.
Proof.
  intros. destruct (exists_last (ltac:(discriminate):x1::t1<>nil)) as [? [? ?]].
  rewrite e, app_comm_cons, app_inj_tail_iff in H. destruct H. subst.
  rewrite e, Forall_app in H0. destruct H0. now inversion H0.
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

Definition Reachable i' s' i s bi len :=
  exists t,
    let tt := (Addr (i'*4), s')::t++(Addr (i*4), s)::nil in
    exec_prog arm_prog tt /\
    Forall (InBlockX bi len) tt.
Lemma afterblock_nol:
  forall P s bi len ei,
  (forall s', s = s' \/ Reachable ei s' ei s bi len ->
  AfterBlock P s' bi len ei (fun t => fst t <> Addr (ei *4))) ->
  AfterBlock P s bi len ei (fun _ => True).
Proof.
  intros. unfold AfterBlock. intros. 
  assert (forall x: exit * store, {fst x = Addr (ei*4)} + {fst x <> Addr (ei*4)}) by repeat decide equality.
  destruct (Exists_dec _ t1 X).
  - apply (exsplit X) in e as [? [? [? [? [? ?]]]]]. apply undofst in H1 as [? ?]. subst.
    assert (XP':=XP).
    apply exec_prog_tail in XP. rewrite <-app_assoc in XP. apply exec_prog_split in XP as [XP _].
    rewrite app_cons in XP. apply exec_prog_split in XP as [_ [_ XP]].
    eapply H. right. exists x1. split. apply XP. now rewrite <-app_assoc, Forall_app in IB.
    rewrite app_comm_cons in XP'. apply exec_prog_split in XP' as [_ [_ XP']]. apply XP'. now apply Forall_Exists_neg. apply Forall_app in IB as [IB _].
    apply Forall_app in IB as [? ?]. apply Forall_app. split. easy. constructor. now inversion H1. easy.
  - eapply H. now left. apply XP. now apply Forall_Exists_neg. easy.
Qed.
Lemma xp_splice:
  forall p t t' x, exec_prog p (x::t) -> exec_prog p t' -> ostartof t' = Some x -> exec_prog p (t'++t).
Proof.
  intros. apply exec_prog_app. now apply exec_prog_tail in H. unfold can_step_between. destruct t. easy. rewrite H1. now inversion H. easy.
Qed.

Lemma afterblock_step:
  forall b z s bi ei P T
    (MB: MaintainsBlock b bi ei s)
    (E: bi <= ei)
    (Z: nth_error b (Z.to_nat (Z.of_N ei - Z.of_N bi)) = Some z),
    (forall c' s' x, exec_stmt armc s (arm2il (ei*4) (arm_decode z)) c' s' x ->
        (x = None /\
        (MaintainsBlock b bi (ei+1) (reset_temps s s') -> 
          Reachable (ei+1) (reset_temps s s') ei s bi (length b) ->
          AfterBlock P (reset_temps s s') bi (length b) (ei+1) T) /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
        (x = None /\
        length b = N.to_nat (ei - bi + 1) /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
        (exists a, x = Some (Addr a) /\
        P (Addr a, (reset_temps s s')) /\
        (~ (InBlock (Z.of_N bi) (length b) a) \/ ~ T (Addr a, (reset_temps s s')))) \/
        (exists a, x = Some (Raise a))) ->
    AfterBlock P s bi (length b) ei T.
Proof.
  intros. unfold AfterBlock. intros.
  destruct MB as [CB MB].
  specialize (CB ei) as CB'. rewrite Z in CB'.
  remember (Z.to_nat _). pose proof (proj1 (nth_error_Some b n) ltac:(now rewrite Z)).
  assert (InBlock (Z.of_N bi) (length b) (ei*4)) as IB' by (split; [lia|now exists ei]).
  specialize (CB' IB').
  destruct (@exists_last _ ((Addr a', s')::t1) ltac:(discriminate)) as [? [? ?]]. rewrite app_comm_cons, e, <-app_assoc in XP. simpl in XP.
  assert (XP':=XP). apply exec_prog_split in XP as [XP _].
  inversion XP. inversion H3. rewrite CB' in LU. inversion LU. subst. apply H in XS.
  clear H4 LU H. destruct XS as [[? [? ?]]|[[? [? ?]]|[[? [? [? ?]]]|[? ?]]]]; subst;
    (destruct x; [ inversion e; now try rewrite N.mul_add_distr_r in H2|]).
  {
    inversion e; subst; simpl in XP'.
    eapply H1. 
      pose proof (exec_prog_step _ _ _ (exec_prog_none _ _) H3).
      rewrite <-app_assoc, Forall_app in IB. destruct IB.
      split. apply db_db' in MB. eapply MB. rewrite app_nil_l. apply H. easy. easy.
      intros ???????. eapply MB. rewrite app_cons,app_comm_cons in XP0. apply exec_prog_split in XP0 as [_ [_ ?]].
      eapply (xp_splice _ _ _ _ H H6). now rewrite app_comm_cons, ostartof_niltail, N.mul_add_distr_r. now apply Forall_forall.
      apply Forall_app. split. easy. now apply Forall_app in H5.
      exists nil. split. simpl. apply exec_prog_step. apply exec_prog_none. now rewrite N.mul_add_distr_r.
      rewrite <-app_assoc in IB. simpl in *. rewrite Forall_app in IB. now rewrite N.mul_add_distr_r.
    rewrite N.mul_add_distr_r. apply XP'. now apply Forall_app in T1.
    apply Forall_app in IB. now rewrite N.mul_add_distr_r.
  }
  all: try destruct H2; inversion e; subst; apply Forall_app in IB as [IB _], IB as [_ IB], T1 as [_ T1]; inversion IB; subst;
    unfold InBlockX, InBlock in *; simpl in *; now (lia || inversion T1).
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
Lemma arm_assemble_all_app:
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

Lemma aaa: forall a b c m, b mod m = c mod m -> (a + b) mod m = (a + c) mod m.
Proof.
  intros. now rewrite N.Div0.add_mod, H, <-N.Div0.add_mod.
Qed.
Lemma add: forall i s s' c' x reg imm shift,
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
Lemma reachablecat{i2 s2 i1 s1 i0 s0 bi len}:
  forall
    (R: Reachable i2 s2 i1 s1 bi len)
    (R': Reachable i1 s1 i0 s0 bi len),
    Reachable i2 s2 i0 s0 bi len.
Proof.
  intros. destruct R as [? [?]], R' as [? [?]].
  pose proof (xp_splice _ _ _ _ H1 H ltac:(now rewrite app_comm_cons, ostartof_niltail)).
  simpl in H3. eexists. split. rewrite app_assoc in H3. apply H3. rewrite <-app_assoc, app_comm_cons, Forall_app. split. easy. now inversion H2.
Qed.
Local Ltac r :=
  repeat match goal with
         | [ H: Reachable _ _ ?i ?s ?bi ?len, H1: Reachable ?i ?s _ _ ?bi ?len |- _ ] =>
             let r := fresh "r" in
             pose proof (reachablecat H H1) as r; clear H H1; rename r into H1
         end.

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
Lemma after_arm_add: forall P reg v s bi b pre post T ei
  (MB: MaintainsBlock b bi ei s)
  (M: models armc s)
  (E: ei = bi + N.of_nat (length pre))
  (B: arm_assemble_all (pre++arm_add reg (Z.of_N v)++post) = Some b)
  (L: (0 < length post)%nat)
  (R: (reg < 15)%Z)
  (I: bi + N.of_nat (length pre) + 3 < 2 ^ 30)
  (IB: (forall x, InBlockX bi (length b) x -> P x))
  (PC: forall s',
    MaintainsBlock b bi (ei+4) s' ->
    Reachable (ei+4) s' ei s bi (length b) ->
    models armc s' ->
    reset_temps s s' = s[R_PC := (ei + 3) * 4][arm_varid (Z.to_N reg) := s (arm_varid (Z.to_N reg)) ⊕ v] ->
    AfterBlock P s' bi (length b) (ei+4) T),
  AfterBlock P s bi (length b) ei T.
Proof.
  intros. unfold arm_add, Z4, Z8, Z12, Z14, Z16, Z24, Z32 in B. cbn[app]in B. rewrite !zxbits_eq in B.

  apply arm_assemble_all_app in B as [b_pre [b_tail [? [BPRE B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BPRE.
  apply arm_assemble_all_first in B as [? [? [? [? ?]]]]; subst.
  eapply afterblock_step. easy. lia. 
  replace_nth (length pre). rewrite nth_error_app2 by lia. replace_nth O. reflexivity.

  intros.
  epose proof (reset_temps_models (pres_frame_exec_stmt M M _ H0)) as M'.
  rewrite H1, <-(Z2N.id 4), <-(Z2N.id (Z_xbits _ _ _)) in H0 by (apply Z_xbits_nonneg||lia).
  apply add in H0 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia]. 
  left; repeat split; [easy|intros ? RA|shelve].

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x1.
  eapply afterblock_step. easy. lia.
replace_nth (S(length pre)). rewrite nth_error_app2. replace_nth 1%nat. now subst. lia.

  intros.
  epose proof (reset_temps_models (pres_frame_exec_stmt M' M' _ H2)) as M''.
  rewrite H5, <-(Z2N.id 8), <-(Z2N.id (Z_xbits _ _ _)) in H2 by (apply Z_xbits_nonneg||lia).
  apply add in H2 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia]. 
  left; repeat split; [easy|intros|shelve]. r.

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x3.
  eapply afterblock_step. easy. lia.
  replace_nth (length pre + 2)%nat. rewrite nth_error_app2. replace_nth 2%nat. now subst. lia.

  intros.
  epose proof (reset_temps_models (pres_frame_exec_stmt M'' M'' _ H8)) as M'''.
  rewrite H9, <-(Z2N.id 12), <-(Z2N.id (Z_xbits _ _ _)) in H8 by (apply Z_xbits_nonneg||lia).
  apply add in H8 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia]. 
  left; repeat split; [easy|intros|shelve]. r.

  apply arm_assemble_all_first in H as [? [? [? [? ?]]]]; subst x5.
  eapply afterblock_step. easy. lia.
  replace_nth (length pre + 3)%nat. rewrite nth_error_app2. replace_nth 3%nat. now subst. lia.

  intros.
  epose proof (reset_temps_models (pres_frame_exec_stmt M''' M''' _ H12)) as M''''.
  rewrite H13 in H12.
  replace (Z_xbits (Z.of_N v) 0 8) with (Z.lor (Z.shiftl (Z.of_N 0) 8) (Z_xbits (Z.of_N v) 0 8)) in H12 by now rewrite Z.lor_0_l.
  rewrite <-(Z2N.id (Z_xbits _ _ _)) in H12 by (apply Z_xbits_nonneg||lia).
  apply add in H12 as [? ?]; [|assumption|rewrite Z2N_xbits by lia; apply xbits_bound|lia]. 
  left; repeat split; [easy|intros|shelve]. r.

  rewrite <-3N.add_assoc. apply PC. now rewrite <-3N.add_assoc in H15.
  now rewrite <-3N.add_assoc in RA. apply M''''.


  unfold reset_temps in *.
  rewrite !reset_vars_overwrite_l, !rt in *.
  rewrite reset_vars_overwrite_r, H12, H8, H2, H0.
  fold reset_temps in *.
  assert (arm_varid (Z.to_N reg) <> R_PC) by (unfold arm_varid; destruct_match_eqn; lia || discriminate).
  repeat rewrite update_swap, update_cancel by easy. rewrite <-2N.add_assoc.
  remember ((s'1 _ + _) mod _). remember ((_ + _) mod _). enough (n = n0). now rewrite H17. subst.
  rewrite <-(rt s), H8, update_updated, <-(rt s), H2, update_updated, <-(rt s), H0, update_updated.
  rewrite ! N.Div0.add_mod_idemp_l, <-N.add_assoc, N.Div0.add_mod_idemp_l, <-!N.add_assoc.
  Unshelve. shelve.
  3,6,9,12: apply IB; unfold InBlockX, InBlock; simpl; apply arm_assemble_all_len in H; simpl in H; rewrite length_app; subst; simpl; split; [try lia| apply N.divide_factor_r].
  all: try exact armc; apply welltyped_arm2il; lia.
  Unshelve.
  clear.
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
  (* intros. mystep H; unfold arm_varid in H; destruct_match_in H; simpl in H; cbv [arm_cond_exp arm_assign_R arm_varid] in H; simpl in H; destruct_match_in H; rewrite N2Z.id in H; remember (Z.to_N lsb); remember (n + _); step_stmt H; destruct H; inversion H; exists n1; repeat split; *)
  (* inversion E; inversion E1; rewrite <-H6, <-H11; simpl; subst; replace (widthm1 + 1) with (N.succ (Z.to_N lsb + widthm1) - Z.to_N lsb) by lia; apply xbits_bound. *)
Admitted.
(**)
Lemma UBFX_bound: forall i s s' c' x reg sl sr,
  exec_stmt armc s (arm2il i (UBFX reg reg sl (Z.of_N sr))) c' s' x ->
  (reg <> 15)%Z ->
  (sr < 32) ->
  exists n, s' = s[R_PC := i][arm_varid (Z.to_N reg) := n] /\ n < 2 ^ (32 - sr) /\ x = None.
Proof.
  intros. cbv [UBFX] in H. unfold Z31 in H. rewrite <-(Z2N.id 31) , <-N2Z.inj_sub in H by lia. apply bfx_bound in H. now rewrite <-N.add_sub_swap in H by lia.
Qed.
Lemma reachableduring {P s len bi ei i s'}: Reachable i s' ei s bi len -> DuringBlock P s bi len ei (fun _ => True) -> P (Addr (i*4), s').

Proof.
  intros. apply db_db' in H0. destruct H as [? [? ?]]. eapply H0. rewrite app_cons in H. rewrite app_nil_r in H. apply H. 
  now apply Forall_forall.
  easy.
Qed.
Lemma mt:
  forall b bi ei s s'
    (MB: MaintainsBlock b bi ei s)
    (RA: Reachable ei s' ei s bi (length b)),
    MaintainsBlock b bi ei s'.
Proof.
  unfold MaintainsBlock. intros. destruct MB. split.
  eapply reachableduring in H0. simpl in H0. apply H0. apply RA.

  unfold DuringBlock, AfterBlock in *. intros. destruct RA as [? [? ?]].
  eapply (H0 _ (t1++(Addr (ei*4), s')::x)). 
  rewrite app_cons, app_comm_cons in XP; apply exec_prog_split in XP as [_ [_ XP]].
  pose proof (xp_splice _ _ _ _ H1 XP ltac:(now rewrite app_comm_cons, ostartof_niltail)).
  simpl in H3. rewrite <-app_cons, (app_comm_cons x), app_assoc in H3. apply H3.
  now apply Forall_forall.
  rewrite (app_cons _ x), <-app_assoc.
  apply Forall_app. split. easy. now inversion H2.
Qed.
Lemma afterblock_s:
  forall P s bi len ei
  (Q: InBlock (Z.of_N (bi+1) ) len (ei*4) ), 
  AfterBlock P s (bi+1) len ei (fun t => fst t <> Addr (bi * 4)) ->
  AfterBlock P s bi (len+1) ei (fun t => fst t <> Addr (bi*4)).
Proof.
  unfold AfterBlock. intros. eapply H. apply XP. easy.
  apply Forall_app. split. apply Forall_app in IB as [? ?]. apply Forall_forall. rewrite Forall_forall in H0, T1. intros. unfold InBlockX, InBlock in *. destruct x, e.  apply H0 in H2 as ?. simpl in H3.
  destruct H3. inversion H4. subst. apply T1 in H2. simpl in H2. enough (x <> bi). simpl. split. lia. now exists x. intro. subst. easy. 
     apply H0 in H2. easy. constructor. easy.
     easy.
Qed.
Lemma maintainsblock_s:
  forall a b bi ei s, MaintainsBlock (a::b) bi ei s -> MaintainsBlock b (bi+1) ei s.
Proof.
  unfold MaintainsBlock. intros. destruct H. split. apply containsblock_cons in H. now rewrite N2Z.inj_add.
  rewrite db_db' in *. unfold DuringBlock' in *. intros.
      rewrite N2Z.inj_add. eapply containsblock_cons. eapply H0. apply XP. now rewrite Forall_forall. eapply Forall_impl. simpl. 
      rewrite <-Nat.add_1_r. apply inblockx_ss.
      apply IB. 
Qed.

Lemma afterblock_cond:
  forall P b s i l cond
  (B: arm_assemble_all_cond l cond = Some b)
  (I: i < 2^30 - 64)
  (L: (1 <= length l < 64)%nat)
  (MB: MaintainsBlock b i i s)
  (AB: match arm_assemble_all l with
       | Some b' => forall s',
           let i' := (i + N.of_nat (length b - length b')) in
           (s' = s \/ Reachable i' s' i s i (length b)) ->
           MaintainsBlock b' i' i' s' ->
           AfterBlock P s' i' (length b') i' (fun t => fst t <> Addr (i*4))
       | _ => True
       end)
  (PA: forall s, P (Addr ((i + N.of_nat (length b))*4), s))
  (PS: forall s, P (Addr ((i + 1)*4), s)),
    AfterBlock P s i (length b) i (fun _ => True).
Proof.
  intros.

  unfold arm_assemble_all_cond in B. 
   destruct Z.ltb.

   eapply afterblock_nol.
   intros.
    apply arm_assemble_all_first in B as [? [? [? [? ?]]]]. subst.
    eapply afterblock_step. destruct H. now subst. eapply mt. apply MB. apply H. easy. now rewrite Z.sub_diag, nth_error_O.
    intros.
    rewrite H2 in H1. assert (CP:=H1). mystep H1. mystep H1. destruct N.modulo; mystep H1; destruct H1 as [[? ?] _].
      left. repeat split. assumption. simpl length in AB. rewrite H0, Nat.sub_succ_l, Nat.sub_diag in AB. intros ? ?R.
      subst n. simpl. rewrite <-Nat.add_1_r. eapply afterblock_s. apply arm_assemble_all_len in H0. destruct x0. simpl in H0. lia. apply inblock_start. apply AB. 
      right.
      assert (exec_prog arm_prog ((Addr ((i+1)*4), reset_temps s' s'0)::(Addr (i*4), s')::nil)).
      apply (exec_prog_step _ _ _ (exec_prog_none _ _)).
      rewrite N.mul_add_distr_r.
      eapply (CanStep _ (i*4) s' 4 _ _ _ None). destruct H. subst. destruct MB. specialize (c i inblock_start). rewrite Z.sub_diag, nth_error_O in c. apply c. 
      eapply mt  in MB as [? ?]. specialize (H i inblock_start). rewrite Z.sub_diag, nth_error_O in H. apply H. easy. rewrite H2. subst. apply CP.
      destruct H. exists nil. split. now subst. simpl. constructor. apply arm_assemble_all_len in H0. rewrite <-H0. unfold InBlockX, InBlock. split. lia. apply N.divide_factor_r. constructor. apply inblock_start. easy. destruct H as [? [? ?]]. pose proof (xp_splice _ (x2++(Addr (i*4), s)::nil) _ _ H H5 eq_refl). eexists.
      split. simpl in *. rewrite app_comm_cons in H7. apply H7. constructor. unfold InBlockX, InBlock. split. apply arm_assemble_all_len in H0. lia. apply N.divide_factor_r. simpl. easy. eapply maintainsblock_s. apply H4. lia.
       apply PS.
      assert (n ⊕ 8 ⊕ n0 .& 4294967292 = (i + N.of_nat (S(length l)))*4) as E.
      {
        subst.
        rewrite N.mul_add_distr_r, N.shiftl_mul_pow2. rewrite <-Z_nat_N, Z2Nat.inj_sub, Nat2Z.id, Nat2N.inj_sub, Z_nat_N by easy.
        cbn. rewrite N.mul_sub_distr_r. unfold scast. pose proof (toZ_nonneg). edestruct H3. rewrite H4.
        rewrite (N.mod_small _ (2^26)), N2Z.inj_sub, N2Z.inj_mul, nat_N_Z by lia. cbn. unfold ofZ. rewrite Z2N.inj_mod by lia. replace (Z.to_N (_ - _)) with (N.of_nat (length l) * 4 - 4) by lia. rewrite <-N.Div0.add_mod.
        change 4294967296 with (2^32). rewrite N_land_mod_pow2_move by lia.
        change (_ mod _) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
        rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r. lia. apply N.log2_lt_pow2. lia. lia. enough (N.of_nat (length l) * 4 - 4 < 2^ 25). rewrite N.mod_small by lia. apply H6. lia.
      }
      simpl length in PA. apply arm_assemble_all_len in H0.
      right. right. left. repeat esplit. apply H3. rewrite E, H0. apply PA.
      unfold InBlock. rewrite E. simpl length. lia.

   eapply afterblock_nol. intros.
   simpl in AB. rewrite B, Nat.sub_diag, N.add_0_r in AB. destruct H; apply AB. now left. now subst.
   now right. eapply mt. apply MB. apply H.
Qed.


Lemma afterblock_fallthru:
  forall n P b s bi T,
  Forall (fun z => forall s c' s' x i a, exec_stmt armc s (arm2il i (arm_decode z)) c' s' x -> x <> Some (Addr a)) b ->
  (forall a s, InBlock (Z.of_N bi) (length b) a -> P (Addr a, s)) ->
  (0 < length b)%nat ->
  (MaintainsBlock b bi (bi+(N.of_nat (length b) - 1 - n)) s) ->
  (forall s, P (Addr ((bi + N.of_nat (length b))*4), s)) ->
  AfterBlock P s bi (length b) (bi+(N.of_nat (length b) - 1 - n)) T.
Proof.
  induction n using N.peano_ind. intros. eapply afterblock_step. easy. lia.
  replace_nth (length b - 1)%nat. apply nth_error_nth'. lia.
  intros. rewrite Forall_nth in H. 
  destruct x. destruct e.
  eapply H in H4. easy. lia.
  right. right. right. now exists i.
  right. left. repeat split. lia. rewrite N.sub_0_r, <-N.add_assoc, N.sub_add by lia. apply H3.
  intros. revert H2.
  destruct (N.le_gt_cases (N.of_nat (length b) - 1) n). apply N.sub_0_le in H2. rewrite (proj2 (N.sub_0_le _ _)), <-H2 by lia. intro. now apply IHn.
  intro.
  eapply afterblock_step. easy. lia.
  replace_nth (length b - 1 - N.to_nat (n + 1))%nat. apply nth_error_nth'. lia.
  intros. assert (C:=H). rewrite Forall_nth in H.
  destruct x. destruct e.
  eapply H in H5. easy. lia.
  right. right. right. now exists i.
  destruct (Nat.eq_dec (length b) 1).
  right. left. repeat split. lia. rewrite e, N.sub_diag, N.sub_0_l, N.add_0_r. now replace 1 with (N.of_nat (length b)) by lia.
  left. repeat split. 
  rewrite <-N.add_1_r, N.sub_add_distr, <-N.add_assoc, N.sub_add by lia. intros. now apply IHn.
  apply H0. unfold InBlock. split. lia. apply N.divide_factor_r.
  Unshelve. apply Z0. apply Z0.
Qed.
Lemma afterblock_fallthru':
  forall P b s bi T,
  Forall (fun z => forall s c' s' x i a, exec_stmt armc s (arm2il i (arm_decode z)) c' s' x -> x <> Some (Addr a)) b -> 
  (forall a s, InBlock (Z.of_N bi) (length b) a -> P (Addr a, s)) ->
  (0 < length b)%nat ->
  (MaintainsBlock b bi bi s) ->
  (forall s, P (Addr ((bi + N.of_nat (length b))*4), s)) -> AfterBlock P s bi (length b) bi T.
Proof.
  intros. assert (bi = (bi+(N.of_nat (length b)-1-(N.of_nat (length b)-1)))) by lia.
  rewrite H4 at 2. rewrite H4 in H2 at 2.
  now apply afterblock_fallthru.
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
  forall reg_list start f,
    NoJ start -> (forall n, NoJ (f n)) -> NoJ (for_0_14 reg_list start f).
Proof.
  intros. repeat apply noj_seq; destruct_match_eqn; apply H0 || discriminate || assumption.
Qed.
Lemma arm_lsm_noj:
  forall op cond W Rn register_list a c s c' s' x A
    (XS: exec_stmt c s (arm2il a (ARM_lsm op cond W Rn register_list)) c' s' x),
    (Z.to_N register_list < 2 ^ 15 -> x <> Some (Addr A))%N.
Proof.
  (* intros. noj XS; cbv[arm_lsm_il arm_lsm_op_il arm_lsm_op_type arm_stm_il arm_ldm_il arm_lsm_il_]. easy. time (destruct_match_eqn; *)
  (* nj; try solve [eapply xbits_above in H; rewrite H in e0; lia]; apply noj_ite; now try apply for_0_14_noj). *)
Admitted. (*speed this up*)
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
  Z.to_N (Z.lor (Z.shiftl 1 reg) (Z.shiftl 1 reg2)) < 2 ^ 15.
Proof.
  intros. rewrite Z2N_inj_lor by now apply Z.shiftl_nonneg.
  apply lor_bound; (rewrite Z2N_inj_shiftl, N.shiftl_mul_pow2, N.mul_1_l; [apply N.pow_lt_mono_r| |] ; lia).
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
Local Lemma typeof_arm_varid:
  forall n, arm7typctx (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.
Lemma exec_str :
  forall rt rn s s' a c' x offset
    (XS: exec_stmt armc s (arm2il a (STR (Z.of_N rt) (Z.of_N rn) (-(Z.of_N offset)))) c' s' x)
    (RT: rt < 15)
    (RN: rn < 15)
    (O: 0 < offset)
    (M: models armc s),
    getmem 32 (LorB (s R_E)) 4 (s' V_MEM32) (s (arm_varid rn) ⊖ offset) = s (arm_varid rt).
Proof.
  (* intros. cbv[STR arm2il arm_ls_i_il arm_ls_op_il arm_ls_il Z1 Z14 arm_assign_MemU arm_cond_il arm_cond_exp ] in XS. *)
  (* replace (- _ <? _)%Z with true in XS by lia. *)
  (* simpl Z.to_N in XS. cbv[N.eqb orb Pos.eqb] in XS. simpl in XS. *)
  (* cbv[arm_R] in XS. *)
  (* rewrite !N2Z.id in XS. *)
  (* replace (Z.to_N _) with (offset) in XS by lia. *)
  (* replace (rn =? 15) with false in XS by lia. replace (rt0 =? 15) with false in XS by lia.  *)
  (* specialize (M (arm_varid rt0) _ (typeof_arm_varid _)). unfold arm_varid in *. destruct_match_eqn; try lia; *)
  (* step_stmt XS; destruct XS as [XS _]; step_stmt XS; destruct XS as [XS _]; destruct (s R_E); step_stmt XS; destruct XS as [[? ?] [? _]]; *)
  (* rewrite <-(reset_temps_not_temp _ s), H, update_updated by discriminate; now rewrite getmem_setmem, N.mod_small by lia. *)
Admitted.
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
  forall P ti sl sr reg s bi ei b prefix tail T
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
  (PC: forall s' n,
    MaintainsBlock b bi (ei+7) s' ->
    Reachable (ei+7) s' ei s bi (length b) ->
    (* the store after arm_table_lookup finishes executing has reg set to Mem[n*4] (endianness depends on R_E) *)
    reset_temps s s' = s[R_PC := (bi + N.of_nat (length prefix) + 6) * 4][arm_varid reg := getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (n*4)] ->
    (* n is an index of the table *)
    ti <= n < ti + 2 ^ (32 - sr) ->
    AfterBlock P s' bi (length b) (ei+7) T),
  AfterBlock P s bi (length b) ei T.
Proof.
  intros. unfold arm_table_lookup in B. cbn [app] in B. move B after PC.
  pose proof (arm_varid_not_pc reg REG) as NOTPC. pose proof (not_eq_sym NOTPC) as NOTPC'. move NOTPC' after REG. move NOTPC after REG.

  assert (B':=B).
  apply arm_assemble_all_app in B as [b_pre [b_tail [? [BPRE B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BPRE. rewrite length_app in I.
  (* UBFX *)
  apply arm_assemble_all_first in B as [z_ubfx [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step; [assumption|lia|..].
  replace_nth (length prefix). now rewrite BPRE, nth_error_app2, Nat.sub_diag, nth_error_O by easy. 

  intros ??? XS. left. eapply (pres_frame_exec_stmt M M) in XS as M0; [|apply welltyped_arm2il; lia]. rewrite DECODE in XS; clear DECODE.
  apply UBFX_bound in XS as [reg_val [? [REGBOUND EXIT]]];[|lia ..]; subst; clear c'.
  rewrite reset_temps_update_r, reset_temps_id.
  repeat split; [|shelve]. clear MB; intros MB RA.

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
  (* replace (z_lsl::b) with ((z_lsl::nil)++b) by easy. change (1+1) with (1+N.of_nat (length (z_lsl::nil))). *)
  rewrite N.add_assoc. simpl.
  clear MB; intros MB ?. rewrite N2Z.id in RA. r.

  
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
  clear MB; intros s'' MB ? M2 S''. r.
  rewrite reset_temps_overwrite_l, S', N2Z.id, !update_cancel2, update_updated in S'' by assumption.

  (* LDR *)
  apply arm_assemble_all_app in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_ldr [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  apply afterblock_step with (z:=z_ldr); [assumption|lia|..].
  replace_nth (length prefix + 6)%nat. rewrite nth_error_app2 by lia. replace_nth 6%nat. rewrite 2nth_error_S. simpl tl. rewrite nth_error_app2 by lia. now rewrite <-BADD.
  intros c' s''' x XS. eapply (pres_frame_exec_stmt M2 M2) in XS as M3; [|apply welltyped_arm2il; rewrite BPRE; rewrite length_app in I; try lia]. rewrite DECODE in XS; clear DECODE.
  apply exec_ldr in XS as [S''' EXIT]; [|lia|assumption]; subst; clear c'.

  rewrite <-(reset_temps_not_temp R_E s), <-(reset_temps_not_temp V_MEM32 s), <-(reset_temps_not_temp (arm_varid reg) s) in S''' by (try rewrite typeof_arm_varid; discriminate).
  rewrite S'', update_updated, !update_frame in S''' by (unfold arm_varid; destruct_match_eqn; discriminate).
  rewrite <-(reset_temps_revert s), reset_temps_update_l, reset_temps_update_r, S'', !reset_temps_update_r, !update_cancel2 in S''' by assumption.
  rewrite N.Div0.add_mod_idemp_l, (N.mul_comm _ ti), <-N.mul_add_distr_r in S'''.
  left. repeat split; [|shelve].
  rewrite <-3N.add_assoc. simpl.
  clear MB; intros MB ?. r.

  unfold Z4 in *.
  apply (PC _ (reg_val+ti)). assumption. assumption. rewrite S''', reset_temps_update_r, reset_temps_revert, N.mod_small, <-2N.add_assoc by lia.
  reflexivity.
  lia.

  Unshelve.
  3: rewrite length_app; simpl; lia.
  all: apply arm_assemble_all_len in B; simpl in B; apply IB.
  all: unfold InBlockX, InBlock; simpl; split; [|apply N.divide_factor_r].
  all: rewrite length_app; simpl; try rewrite length_app; simpl; lia.
Qed.

Definition SafeAfterBlock i2i' pol ai i len s := AfterBlock (SafeDestX i2i' pol ai i len) s (Z.to_N (i2i' i)) len (Z.to_N (i2i' i)) (fun _ => True).
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
Lemma afterblock_timpl:
  forall P s bi len ei T T', (forall t, T t -> T' t) -> AfterBlock P s bi len ei T' -> AfterBlock P s bi len ei T.
Proof.
  unfold AfterBlock. intros. eapply H0. apply XP. eapply Forall_impl. apply H. easy. easy.
Qed.
Lemma afterblock_sq:
  forall P s bi len ei
  (Q: InBlock (Z.of_N (bi+1) ) len (ei*4) ), 
  AfterBlock P s (bi+1) len ei (fun t => fst t <> Addr (bi * 4)) ->
    AfterBlock P s bi (S len) ei (fun t => fst t <> Addr (bi*4)).
Proof.
  unfold AfterBlock. intros. eapply H. apply XP. easy.
  apply Forall_app. split. apply Forall_app in IB as [? ?]. apply Forall_forall. rewrite Forall_forall in H0, T1. intros. unfold InBlockX, InBlock in *. destruct x, e.  apply H0 in H2 as ?. simpl in H3.
  destruct H3. inversion H4. subst. apply T1 in H2. simpl in H2. enough (x <> bi). simpl. split. lia. now exists x. intro. subst. easy. 
     apply H0 in H2. easy. constructor. easy.
     easy.
Qed.
Lemma reachablegrow {i2 s2 i1 s1 bi len bi' len'}:
forall
    (RA: Reachable i2 s2 i1 s1 bi len)
    (START: bi' <= bi)
    (END: bi+N.of_nat len <= bi'+N.of_nat len'),
    Reachable i2 s2 i1 s1 bi' len'.
Proof.
  intros. destruct RA as [? [?]]. eexists. split. apply H. eapply Forall_impl. shelve. apply H0. Unshelve.
  unfold InBlockX, InBlock. intros. destruct fst. split. lia. easy. easy.
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
    (NWT: DuringBlock (fun xs => forall n e,
      Z.to_N ti <= n < Z.to_N ti + N.of_nat (length table) ->
      getmem 32 e 4 (snd xs V_MEM32) (n*4) = getmem 32 e 4 (s1 V_MEM32) (n*4)) s1 (Z.to_N (i2i' i)) (length irm') (Z.to_N (i2i' i)) (fun _ => True)
    )
    (* nothing tc returns is writable *)
    (NWTC: forall si ti sl sr t,
      tc si = Some (ti, sl, sr) ->
      extract_table sr tbi ti flattened_tables = Some t ->
      DuringBlock (fun xs => forall n e, Z.to_N ti <= n < Z.to_N ti + N.of_nat (length t) -> getmem 32 e 4 (snd xs V_MEM32) (n*4) = getmem 32 e 4 (s1 V_MEM32) (n*4)) s1 (Z.to_N (i2i' i)) (length irm') (Z.to_N (i2i' i)) (fun _ => True))
    (* endian flag does not change *)
    (E: DuringBlock (fun xs => snd xs R_E = s1 R_E) s1 (Z.to_N (i2i' i)) (length irm') (Z.to_N (i2i' i)) (fun _ => True)),

    SafeAfterBlock i2i' pol ai i (length irm') s1.
Proof.
  intros. apply SafeTable_rewrite_inst in RI as ST.
  specialize (I2I i) as I2I'.

  assert (
    forall l cond, arm_assemble_all_cond l cond = Some irm' ->
      (1 <= length l < 64)%nat ->
      In (Z.add i 1) (pol i) ->
      match arm_assemble_all l with
      | Some b' => forall s,
          let i' := (Z.to_N (i2i' i) + N.of_nat (length irm' - length b')) in
        (s = s1 \/ Reachable i' s (Z.to_N (i2i' i)) s1 (Z.to_N (i2i' i)) (length irm')) ->
        MaintainsBlock b' i' i' s ->
        AfterBlock (SafeDestX i2i' pol ai i (length irm')) s i' (length b') i' (fun xs => fst xs <> Addr (Z.to_N (i2i' i) * 4))
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

  assert (forall irm cond
  (RWT: rewrite_w_table irm tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
  (SI: forall ti sl sr
    (IRM: irm cond i ti sl sr = Some irm')
    (TI: (0 <= ti)%Z)
    (TI': Z.to_N ti + 2 ^ (32 - Z.to_N sr) < 2 ^ 30)
    (SR: (0 <= sr < 32)%Z)
    (N: forall n s i',
      Z.to_N ti <= n < Z.to_N ti + 2 ^ (32 - Z.to_N sr) ->
      s = s1 \/
      Reachable i' s (Z.to_N (i2i' i)) s1 (Z.to_N (i2i' i)) (length irm') ->
      SafeEntry i2i' pol ai i (Z.of_N (getmem 32 (LorB (s R_E)) 4 (s V_MEM32) (n*4)))
    ),
    SafeAfterBlock i2i' pol ai i (length irm') s1),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RWT. {
    intros. unfold rewrite_w_table in RWT. destruct_match_in RWT; try discriminate.
    inversion RWT. subst. apply SI in e2. easy. apply TC in e. now destruct e. apply TC in e. destruct e.
    apply N2Z.inj_lt. rewrite N2Z.inj_add, N2Z.inj_pow, N2Z.inj_sub, !Z2N.id by lia. lia.
    apply TC in e. now destruct e. intros.
    assert (ee:=e).
    apply TC in e as [table [XT ST']]. unfold SafeTable in ST'. rewrite Forall_forall in ST'.
    specialize (NWTC _ _ _ _ _ ee XT).
    apply table_size_correctness in XT as TS. unfold compute_table_size in TS.
    eapply TCIM in ee. apply ST' in ee. destruct H0. rewrite e. apply ee. 
    apply (reachableduring r) in E. simpl in E. rewrite E. 
    eapply (reachableduring r) in NWTC. simpl in NWTC. rewrite NWTC. easy. rewrite TS.
    rewrite Z_nat_N, Z2N.inj_pow, Z2N.inj_sub. easy. easy. lia. lia.
    easy. rewrite TS, Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. easy.
    remember (make_jump_table _ _ _ _ _ _).
    apply find_hash_bound in e0. 
    unfold Z32 in *. rewrite Z.shiftl_mul_pow2, Z.mul_1_l in Heql0 by lia.
    inversion RWT. subst. apply SI in e2. easy. easy. apply N2Z.inj_lt. rewrite N2Z.inj_add, N2Z.inj_pow, N2Z.inj_sub, !Z2N.id by lia. 
    rewrite make_jump_table_len, Z2Nat.id in TI' by lia. lia.
    lia. intros. rewrite make_jump_table_len, Z_nat_N, Z2N.inj_pow, Z2N.inj_sub in TIM by lia. 
    apply TIM in H as IN. unfold SafeTable in ST. rewrite Forall_forall in ST. apply ST in IN. destruct H0. rewrite H0. easy.
    apply (reachableduring H0) in NWT. rewrite NWT. apply (reachableduring H0) in E. simpl in E. rewrite E. easy. 
    rewrite make_jump_table_len. rewrite Z_nat_N, Z2N.inj_pow, Z2N.inj_sub by lia. apply H.
  }

  assert (forall j
    (SE: SafeEntry i2i' pol ai i (Z.of_N j)),
    ~InBlock (i2i' i) (length irm') j \/ j = Z.to_N (i2i' i * 4)%Z) as SENIB.
  {
    intros. destruct SE.
      left. intro. apply AIB.
        rewrite <-(Z2N.id (ai*4)) in H by lia. apply N2Z.inj in H. rewrite Z2N.inj_mul in H by lia. simpl in H. now rewrite H.
      destruct H as [? [? ?]]. edestruct inblock_dec. shelve.
        left. apply n.
        Unshelve. right. unfold InBlock in *. specialize (I2I''' x). lia.
  }
  assert (forall j
    (SE: SafeEntry i2i' pol ai i (Z.of_N j)),
    (4 | j)) as SE4. {
    intros. destruct SE.
      rewrite <-(Z2N.id (ai*4)) in H by lia. apply N2Z.inj in H. rewrite <-H, Z2N.inj_mul by lia. apply N.divide_factor_r.
      destruct H as [? [? ?]]. rewrite <-(Z2N.id (_*_)) in x0 by lia. apply N2Z.inj in x0.
        specialize (I2I x). rewrite <-x0, Z2N.inj_mul by lia. apply N.divide_factor_r.
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

  assert (forall reg cond
    (RB: rewrite_bx reg tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
    (R: (0 <= reg < 15)%Z)
    (PA: In (Z.add i 1) (pol i)),
    SafeAfterBlock i2i' pol ai i (length irm') s1
  ) as RBX. {
    intros. eapply RWT.
    apply RB. intros. eapply C. apply IRM. simpl. lia. assumption.
    destruct arm_assemble_all eqn:B; auto. intros.
    eapply after_arm_table_lookup with (prefix:=nil). 
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B by lia. rewrite app_nil_l. apply B.
    now rewrite N.add_0_r. lia. lia. simpl; lia.
    destruct H. now rewrite H. destruct H as [? [? ?]]. apply (preservation_exec_prog arm_prog welltyped_arm_prog _ _ _ _ _ H ltac:(now rewrite startof_niltail) M).
    mylia. 
    simpl. lia. lia. 
    intros. destruct xs, e. right. unfold i' in H1. cbn in H1. unfold InBlock in *. split. apply arm_assemble_all_cond_len in IRM. simpl in IRM. apply arm_assemble_all_len in B. simpl in B. inversion RB. subst. lia. now destruct H1. easy.

    intros ??? RA ??. 

  apply arm_assemble_all_app in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_bx [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    apply afterblock_step with (z:=z_bx).
    easy. lia.
    replace_nth 7%nat. rewrite nth_error_app2. now rewrite <-BADD. lia.
    intros.
  rewrite DECODE in H4. rewrite <-(Z2N.id reg) in H4 by lia. 
  apply exec_bx in H4.
  rewrite <-(reset_temps_not_temp _ s), H2, update_updated in H4 by (rewrite typeof_arm_varid; discriminate).
  right. right. left. eexists. repeat split. apply H4. left. eapply (N _ _ _ H3 H). 
  destruct (SENIB _ (N _ _ _ H3 H)). left. intro. apply H5. mylia. easy. right. now rewrite H5, Z2N.inj_mul by lia.
  lia. rewrite <-(rt s), H2, update_updated. apply (SE4 _ (N _ _ _ H3 H)).
  }


  assert (forall sanitized_inst reg cond
  (RPC: rewrite_pc sanitized_inst reg tc (pol i) i2i' cond i ti ai = Some (irm', table, tc'))
  (FT: forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a))
  (R: (0 <= reg < 15)%Z)
  (IN: In (Z.add i 1) (pol i)),
  SafeAfterBlock i2i' pol ai i (length irm') s1) as RP. {
    intros. eapply RWT. apply RPC. intros. eapply C. apply IRM. simpl. lia. assumption.
    destruct arm_assemble_all eqn:B; auto. clear MB. intros s i' RA MB. assert (B':=B).

    apply arm_assemble_all_first in B as [z_str [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. now replace_nth O. intros ??? XS. rewrite DECODE in XS; clear DECODE.
    eapply arm_ls_i_fallthru in XS; [|right;discriminate].
    left. repeat split. assumption. rename MB into MM. rename RA into RR. intros MB RA.

    apply arm_assemble_all_first in B as [z_movw [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. now replace_nth 1%nat. intros ??? XS. rewrite DECODE in XS;clear DECODE.
    apply arm_movwt_fallthru in XS.
    left. repeat split. assumption. rewrite reset_temps_overwrite_l. clear MB; intros MB ?. r.

    apply arm_assemble_all_first in B as [z_movt [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. now replace_nth 2%nat. intros ??? XS. rewrite DECODE in XS;clear DECODE.
    apply arm_movwt_fallthru in XS.
    left. repeat split. assumption. rewrite reset_temps_overwrite_l. clear MB; intros MB ?. r.

    apply arm_assemble_all_first in B as [z_sanitized [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
    eapply afterblock_step. assumption. lia. now replace_nth 3%nat. intros ??? XS. destruct x.
      destruct e. now eapply FT in XS. right. right. right. now exists i0.
    left. repeat split. rewrite reset_temps_overwrite_l. clear MB; intros MB ?. r.

    eapply after_arm_table_lookup. 
    rewrite <-(Z2N.id ti0), <-(Z2N.id sr), <-(Z2N.id reg) in B' by lia. apply B'.
      now rewrite <-3N.add_assoc in MB.
      lia.
      lia.
      simpl. lia.
      shelve.
      mylia.
      simpl. lia.
      lia.
      intros. simpl. destruct xs, e. simpl in H. right. split. mylia. simpl in H. lia. now inversion H. easy.
      clear MB; intros ?? MB ? AAA NB. simpl in AAA. rewrite reset_temps_overwrite_l in AAA.

  apply arm_assemble_all_app in B as [b_add [b_tail [B_add_tail [BADD B]]]]; subst; rename b_tail into b.
  apply arm_assemble_all_len in BADD. simpl in BADD.
  apply arm_assemble_all_first in B as [z_str' [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step. simpl in MB. now rewrite <-!N.add_assoc in *. lia. replace_nth 11%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth O. lia.
  clear XS. intros ??? XS. rewrite DECODE in XS; clear DECODE.
  change SP with (Z.of_N 13) in XS. change Z_8 with (-Z.of_N 8) in XS.
  rewrite <-(Z2N.id reg) in XS by lia. 
  apply exec_str in XS as ?; [|lia..|]. r.
  apply arm_ls_i_fallthru in XS; [|right;discriminate].
  left. repeat split. assumption. clear MB; intros MB ?. r.

  apply arm_assemble_all_first in B as [z_ldr [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step. assumption. lia. replace_nth 12%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth 1%nat. lia.
  intros ??? XS. rewrite DECODE in XS; clear DECODE.
  apply arm_ls_i_fallthru in XS; [|left;lia].
  left. repeat split. assumption. rewrite reset_temps_overwrite_l. clear MB; intros MB ?. r.

  apply arm_assemble_all_first in B as [z_ldr' [b_tail [B [B_B' DECODE]]]]; subst; rename b_tail into b.
  eapply afterblock_step. assumption. lia. replace_nth 13%nat. rewrite !nth_error_cons, nth_error_app2. now replace_nth 2%nat. lia.
  intros ??? XS. rewrite DECODE in XS; clear DECODE.
  eapply exec_ldrpc in XS.
  right. right. left. eexists. repeat split. apply XS. simpl in RA. shelve. shelve. shelve. shelve. right. mylia. right. mylia. shelve. right. mylia.
  right. mylia. right. mylia. right. mylia.
  Unshelve. shelve. all: admit.
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
    intros. apply afterblock_fallthru'.
      apply arm_assemble_all_eq in e. rewrite <-e, Forall_map in H0. assumption.
      intros. cbv[SafeDestX fst]. right.
      apply arm_assemble_all_cond_len in H.  apply arm_assemble_all_len in e. unfold InBlock in *. split. lia. easy.
        apply arm_assemble_all_len in e. lia. assumption.
        intros. cbv[SafeDestX fst SafeDest]. left. right. exists (i+1)%Z. split. rewrite I2I''. subst i'. apply arm_assemble_all_len in e. apply arm_assemble_all_cond_len in H. lia. assumption.
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
    eapply GOTOz_correct in e. exists (Z.to_N ai * 4). repeat split. apply e. unfold SafeDestX. simpl. left. left. lia. left. now rewrite Z2N.id by apply I2I'. lia. lia. apply H0.
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
  | _ => clear C GA FT FTS RPNJ RPSNJ
  end.
Admitted.

