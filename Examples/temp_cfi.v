Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import -(notations) arm7_cfi2.
Require Import Picinae_armv7.
Require Import Lia ZifyN ZifyNat.
Import ARM7Notations.
Import ListNotations.
Require Import Nat.

Open Scope N.

Definition to_a := Z.mul 4.
Definition i2a' i2i' (i: Z) := to_a (i2i' i).
Definition compute_table_size sr := Z.to_nat (2 ^ (32 - sr)).
Definition compute_table_start_index tbi ti := Z.to_nat (ti - tbi).
Definition SafeEntry i2i' (pol: Z -> list Z) ai si a :=
  to_a ai = a \/ exists di (D: i2a' i2i' di = a), In di (pol si).
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

Definition ContainsBlock (p: program) b s i :=
  forall i', InBlock i (length b) (i'*4) ->
    match nth_error b (Z.to_nat (Z.of_N i' - i)) with
    | Some z => p s (i'*4) = Some (4, arm2il (i'*4) (arm_decode z))
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
Lemma inblockx_cons:
  forall i (b:Z) b' x,
    InBlockX (i + 1) (length b') x -> InBlockX i (length (b :: b')) x.
Proof.
  intros. destruct x, e.
    unfold InBlockX, InBlock in *. simpl in *. split. lia. easy.
    easy.
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
Lemma inblockx_dec : forall i ilen a, {InBlockX i ilen a} + {~InBlockX i ilen a}.
Proof.
  intros. destruct a, e.
  unfold InBlockX, InBlock. simpl.
  destruct (Ndivdec 4 a), (Z_le_dec (Z.of_N i * 4) (Z.of_N a)), (Z_lt_dec (Z.of_N a) (((Z.of_N i) + Z.of_nat ilen) * 4)).
  all: (now left) || (now right).
Qed.

(* for prog p that contains block b, after starting at entry index ei with store s,
   prop P holds for all states constrained to the block as well as the first step outside the block *)
Definition AfterBlock (P: exit * store -> Prop) b p s bi ei :=
  forall t0 t1 a' s'
    (XP: exec_prog p ((Addr a', s')::t1++t0))
    (SO: ostartof t1 = Some (Addr (ei*4), s))
    (CB: ContainsBlock p b s (Z.of_N bi))
    (IB: Forall (InBlockX bi (length b)) t1),
    P (Addr a', s').

(* like AfterBlock, but ignores the first step outside the block *)
Definition DuringBlock P b p s bi ei := AfterBlock (fun xs => P xs \/ ~InBlockX bi (length b) xs) b p s bi ei.
(* an alternative definition that we prove is equivalent *)
Definition DuringBlock' (P: _ -> Prop) b p s bi ei :=
  forall t0 t1 a' s'
    (XP: exec_prog p ((Addr a', s')::t1++t0))
    (SO: ostartof t1 = Some (Addr (ei*4), s))
    (CB: ContainsBlock p b s (Z.of_N bi))
    (IB: Forall (InBlockX bi (length b)) ((Addr a', s')::t1)),
    P (Addr a', s').
Lemma db_db': forall P b p s bi ei, DuringBlock P b p s bi ei <-> DuringBlock' P b p s bi ei.
Proof.
  intros. unfold DuringBlock, DuringBlock', AfterBlock. split.
    intros. apply H in XP. destruct XP. easy. now inversion IB. easy. easy. now inversion IB.
    intros. destruct (inblockx_dec bi (length b) (Addr a', s')).
      apply H in XP. now left. easy. easy. constructor. easy. easy.
      now right.
Qed.

(* the given block does not change as long as we are still in the block

   note that we use DuringBlock instead of AfterBlock,
   since we need to assume this property to prove that blocks go to a safe destination,
   but to prove that the block is maintained even after exiting the block,
   we need to know that indirect jumps always load from the table *)
Definition MaintainsBlock p b bi ei s :=
  DuringBlock (fun xs => ContainsBlock p b (snd xs) (Z.of_N bi)) b p s bi ei.

Lemma containsblock_cons:
  forall p b b' s i, ContainsBlock p (b::b') s i -> ContainsBlock p b' s (i+1).
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
  forall a (b:A), ostartof a = Some b -> exists c, a = c ++ [b].
Proof.
  destruct a. easy. intros. destruct (@exists_last _ (a::a0)). easy. destruct s. exists x. rewrite e, ostartof_niltail in H. inversion H. now rewrite <-H1.
Qed.
Lemma single_element{A}:
  forall (a: A) b c,
    [a] = b ++ [c] ->
    a = c.
Proof.
  intros. destruct b; simpl in H; inversion H; auto. now apply app_cons_not_nil in H2.
Qed.
Lemma forall_last{A}:
  forall (P: A -> Prop) y x1 t1 t2 x2,
    y::x1::t1 = t2 ++ [x2] ->
    Forall P (x1::t1) ->
    P x2.
Proof.
  intros. destruct (exists_last (ltac:(discriminate):x1::t1<>[])) as [? [? ?]].
  rewrite e, app_comm_cons, app_inj_tail_iff in H. destruct H. subst.
  rewrite e, Forall_app in H0. destruct H0. now inversion H0.
Qed.


(* if there is at least one element in l where P holds,
   we can split l into two lists where the first does not have any such element,
   and the second list starts with one *)
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
Lemma cons_cons{A}: forall (a:A) b c, a::b::c = [a;b]++c. Proof. easy. Qed.
Lemma app_cons{A}: forall (a:A) b c, c++a::b = (c++[a])++b.
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

(* if the initial store does not matter,
   we only need to consider traces that do not contain the entry more than once to prove AfterBlock *)
Lemma afterblock_noloop:
  (forall P b p s bi ei,
    (forall t0 t1 t2 t3 t4 a' s0 s'
      (* the trace through the block does not loop back to the entry *)
      (NL: ~ Exists (fun x => fst x = Addr (ei*4)) t1)
      (* the store we start with is reachable by some trace through the block *)
      (RA: s = s0 \/ (Forall (InBlockX bi (length b)) t3 /\ exec_prog p (t4++(Addr (ei*4), s0)::t3++(Addr (ei*4), s)::t2)))

      (XP: exec_prog p ((Addr a', s')::t1++(Addr (ei*4), s0)::t0))
      (CB: ContainsBlock p b s (Z.of_N bi))
      (IB: Forall (InBlockX bi (length b)) t1),
      P (Addr a', s')) ->
    AfterBlock P b p s bi ei)%N.
Proof.
  intros. unfold AfterBlock. intros.
  assert (forall x: exit * store, {fst x = Addr (ei*4)} + {fst x <> Addr (ei*4)}) by repeat decide equality.
  destruct (Exists_dec _ t1 X).
  - apply (exsplit X) in e as [? [? [? [? [? ?]]]]]. apply undofst in H1 as [? ?]. subst.
      rewrite <-app_assoc in XP. apply Forall_app in IB as [? ?].
      rewrite ostartof_app in SO. apply ostartof_last in SO as [? ?]. destruct x0.
      + inversion H3. eapply (H t0 x nil nil nil). apply H2. now left. subst. apply XP. assumption. assumption.
      + rewrite H3 in XP. eapply H. apply H2. right. inversion H3. subst.
        rewrite <-app_assoc, app_comm_cons in XP. split. inversion H1. apply Forall_app in H7 as [? ?]. apply H7.
        apply XP. inversion H3. subst. apply XP. assumption. assumption.
  - apply ostartof_last in SO as [? ?]. subst. exfalso. apply n. apply Exists_app. right. now constructor.
Qed.
Lemma afterblock_impl:
  forall P Q p b s bi ei
    (I: forall x, P x -> Q x)
    (AB: AfterBlock P p b s bi ei),
    AfterBlock Q p b s bi ei.
Proof.
  unfold AfterBlock. intros. apply I. eapply AB. apply XP. all: easy.
Qed.

Lemma afterblock_suffix{P b p s bi ei ei' s' t0 t2}:
  forall t1
    (AB: AfterBlock P b p s bi ei)
    (XP: exec_prog p (t2++(Addr (ei'*4), s')::t1++t0))
    (SO: ostartof t1 = Some (Addr (ei * 4), s))
    (CB: ContainsBlock p b s (Z.of_N bi))
    (IB: Forall (InBlockX bi (length b)) t1),
    AfterBlock P b p s' bi ei'.
Proof.
  intros; unfold AfterBlock; intros.
  eapply (AB t0 (t4++t1)).
  - rewrite <-app_assoc, app_comm_cons. rewrite app_cons in XP. apply exec_prog_split in XP as [? [? ?]]. apply exec_prog_app.
      easy.
      unfold can_step_between in *. destruct app eqn:e; auto. erewrite ostartof_some_cons. rewrite ostartof_niltail in H0. apply H0.
      easy.
      rewrite app_comm_cons in XP0. now apply exec_prog_split in XP0.
  - apply ostartof_last in SO as [? ?]. now rewrite H, app_assoc, ostartof_niltail.
  - now destruct t4.
  - now rewrite Forall_app.
Qed.
Lemma xp_splice:
  forall p t t' x, exec_prog p (x::t) -> exec_prog p t' -> ostartof t' = Some x -> exec_prog p (t'++t).
Proof.
  intros. apply exec_prog_app. now apply exec_prog_tail in H. unfold can_step_between. destruct t. easy. rewrite H1. now inversion H. easy.
Qed.

(* for a block b that is maintained through the entire execution through b, where the instruction at our entry index is z, if
      1) z falls through to z' inside the block, P is true for this step, and P always holds after executing from z'
      2) z goes to a state outside the block where P holds
   or 3) z raises an exception
   then P always holds after b if we start at z *)
Lemma afterblock_step:
  forall p b z s bi ei P
    (MB: MaintainsBlock p b bi ei s)
    (E: bi <= ei)
    (Z: nth_error b (Z.to_nat (Z.of_N ei - Z.of_N bi)) = Some z),
    (forall c' s s' x, exec_stmt armc s (arm2il (ei*4) (arm_decode z)) c' s' x ->
      (* case 1 *)
        (x = None /\
        (MaintainsBlock p b bi (ei+1) (reset_temps s s') -> AfterBlock P b p (reset_temps s s') bi (ei+1)) /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
      (* case 2 (fallthru) *)
        (x = None /\
        length b = 1%nat /\
        P (Addr ((ei+1)*4), (reset_temps s s'))) \/
      (* case 2 (jump) *)
        (exists a, x = Some (Addr a) /\
        P (Addr a, (reset_temps s s')) /\
        ~ (InBlock (Z.of_N bi) (length b) a)) \/
      (* case 3 *)
        (exists a, x = Some (Raise a))) ->
    AfterBlock P b p s bi ei.
Proof.
  intros. unfold AfterBlock. intros.
  specialize (CB ei) as CB'. rewrite Z in CB'.
  remember (Z.to_nat _). pose proof (proj1 (nth_error_Some b n) ltac:(now rewrite Z)).
  assert (InBlock (Z.of_N bi) (length b) (ei*4)) as IB' by (split; [lia|now exists ei]).
  specialize (CB' IB').
  apply ostartof_last in SO as [? ?]. rewrite H1, 2 app_comm_cons in XP.
  destruct (@exists_last _ ((Addr a', s')::x) ltac:(discriminate)) as [? [? ?]]. rewrite e, <-2app_assoc in XP.
  assert (XP':=XP). apply exec_prog_split in XP as [XP _]. simpl in XP.
  inversion XP. inversion H4. rewrite CB' in LU. inversion LU. subst. apply H in XS.
  clear H4 H5 LU H. destruct XS as [[? [? ?]]|[[? [? ?]]|[[? [? [? ?]]]|[? ?]]]]; subst;
    (destruct x; [ apply single_element in e; inversion e; now try rewrite N.mul_add_distr_r in H2|]).
  {
    eapply H1.
    eapply (afterblock_suffix [_] MB); [ rewrite N.mul_add_distr_r, app_nil_l; apply XP | now try constructor .. ].
    rewrite app_assoc, <-e in XP'. simpl in XP'. rewrite app_comm_cons in XP'. apply XP'.
    now erewrite <-ostartof_app, <-app_cons, app_nil_l, e, ostartof_app, N.mul_add_distr_r.
    apply db_db' in MB. eapply MB; [rewrite <-app_cons, app_nil_l; apply XP| auto .. ];
      apply (forall_last (InBlockX bi (length b))) in e;
        [apply (Forall_cons _ e); constructor; now try apply IB'|].
    all: now apply Forall_app in IB.
  }
  all: apply (forall_last (InBlockX bi (length b))) in e;
    unfold InBlockX, InBlock in e; simpl in e; [now try lia|now apply Forall_app in IB].
Qed.

(* like afterblock_step, but we can forget about the first instruction of the block *)
Lemma afterblock_cons:
  forall p b b' s i P
    (MB: MaintainsBlock p (b::b') i i s),
    (forall c' s s' x, exec_stmt armc s (arm2il (i*4) (arm_decode b)) c' s' x ->
      (* case 1 *)
        (x = None /\
        (MaintainsBlock p b' (i+1) (i+1) (reset_temps s s') -> AfterBlock P b' p (reset_temps s s') (i+1) (i+1)) /\
        P (Addr ((i+1)*4), (reset_temps s s'))) \/
      (* case 2 (fallthru) *)
        (x = None /\
        b' = nil /\
        P (Addr ((i+1)*4), (reset_temps s s'))) \/
      (* case 2 (jump) *)
        (exists a, x = Some (Addr a) /\
        P (Addr a, (reset_temps s s')) /\
        ~ (InBlock (Z.of_N i) (length (b::b')) a)) \/
      (* case 3 *)
        (exists a, x = Some (Raise a))) ->
    AfterBlock P (b::b') p s i i.
Proof.
  (* todo: clean this proof up *)
  intros. apply afterblock_noloop.
  intros. assert (XP':=XP). assert(CB':=CB). rewrite app_comm_cons in XP.
  remember (_::t1). destruct (@exists_last _ l ltac:(now subst)) as [? [? ?]]. subst.
  rewrite e, <-app_assoc in XP. simpl in XP. apply exec_prog_split in XP as [XP _]. inversion XP. clear x1 l H3 H0 H1. inversion H2. clear H2. subst.
  assert (Some(sz, q) = p s (i*4)).
  { destruct RA. now rewrite H0. destruct H0. unfold MaintainsBlock, DuringBlock in MB. specialize (MB t2 (t3++[(Addr (i*4), s)])).
    simpl in MB. rewrite <-app_assoc in MB. simpl in MB. apply exec_prog_split in H1 as [? _]. eapply MB in H1. shelve. now rewrite ostartof_niltail. easy. apply Forall_app. split. easy. constructor. apply inblock_start. easy. Unshelve. destruct H1.
    specialize (CB i (inblock_start)). specialize (H1 i (inblock_start)). rewrite Z.sub_diag, nth_error_O in CB, H1. simpl in CB, H1. now rewrite <-LU, H1, CB. exfalso.  apply H1. apply inblock_start.
    }
  specialize (CB i (inblock_start )). rewrite Z.sub_diag, nth_error_O in CB. simpl in CB. rewrite CB in H0. inversion H0.
  subst. apply H in XS. destruct XS as [?|[?|[?|?]]].
  shelve.
  - destruct H1 as [? [? ?]]. destruct t1. apply single_element in e. inversion e. subst. rewrite H5. now rewrite N.mul_add_distr_r in H3.
    apply forall_last with (P:=InBlockX i (length (b::b'))) in e.
    subst. simpl in e. unfold InBlockX in e. simpl in e. unfold InBlock in e. lia. easy.
  - destruct H1 as [? [? [? ?]]]. destruct t1. apply single_element in e. inversion e. subst. now rewrite H5.
    apply forall_last with (P:=InBlockX i (length (b::b'))) in e.
    subst. simpl in e. unfold InBlockX in e. simpl in e. contradiction. easy.
  - destruct H1. subst. destruct t1. apply single_element in e. easy.
    apply forall_last with (P:=InBlockX i (length (b::b'))) in e. easy. easy.
    Unshelve.
    destruct H1 as [? [? ?]].


    destruct t1. apply single_element in e. inversion e. rewrite H5. subst. simpl.  rewrite N.mul_add_distr_r in H3. easy.
    subst; simpl in *. eapply H2. shelve. rewrite 2 app_comm_cons in XP'. apply XP'. now erewrite <-ostartof_app, <-app_cons, app_nil_l, e, ostartof_app, N.mul_add_distr_r. rewrite N2Z.inj_add. eapply containsblock_cons. remember (_::_::_). replace l with
      ([(Addr (i * 4 + 4), reset_temps s0 s'0) ; (Addr (i * 4), s0)] ++ t0)%N in XP. destruct RA. apply db_db' in MB. eapply MB. apply XP. now rewrite e0. easy. 
      apply forall_last with (P:=InBlockX i (length (b::b'))) in e. constructor. assumption. constructor. apply inblock_start. easy. assumption. apply db_db' in MB. eapply MB.
      destruct a. apply exec_prog_split in e0 as [? _]. apply exec_prog_split in XP as [_ [_ ?]]. 

      enough (exec_prog p (([(Addr (i * 4 + 4), reset_temps s0 s'0);(Addr (i * 4), s0)]++t3++[(Addr (i*4), s)])++t2)). apply H5. rewrite <-app_assoc.
      apply exec_prog_app. rewrite <-app_cons. now apply exec_prog_tail in H1. unfold can_step_between. simpl. rewrite <-app_assoc. destruct app; auto. now inversion H1. easy. simpl. now rewrite startof_niltail. assumption.
    apply forall_last with (P:=InBlockX i (length (b::b'))) in e. constructor. easy. constructor. apply inblock_start. apply Forall_app. split. easy. constructor. apply inblock_start. easy. easy.
      eapply Forall_impl. replace (length b') with ((length (b::b'))-1)%nat. apply inblockx_s. simpl. lia. apply Forall_Exists_neg in NL. now apply Forall_and.
      Unshelve.
      clear H NL CB H0 H2 H3 LU. apply db_db'. apply db_db' in MB. unfold DuringBlock', DuringBlock in *. intros. rewrite N2Z.inj_add. eapply containsblock_cons.
      destruct RA; eapply MB; rewrite app_comm_cons in XP0; apply exec_prog_split in XP0 as [_ [_ ?]]; pose proof (xp_splice _ _ _ _ XP H); eapply ostartof_some_cons in SO; rewrite N.mul_add_distr_r in SO; apply H0 in SO. rewrite <-app_comm_cons, app_cons in SO. apply SO. now rewrite ostartof_niltail, e0. assumption.
      rewrite app_comm_cons, Forall_app. split. eapply Forall_impl in IB0. apply IB0. apply inblockx_cons. constructor. apply inblock_start. easy.
      destruct a. apply exec_prog_split in e0 as [? _]. rewrite <-app_comm_cons, app_cons , app_comm_cons in SO. apply exec_prog_split in SO as [_ [_ ?]].  pose proof (xp_splice _ _ _ _ H1 H2). rewrite app_comm_cons, ostartof_niltail, <-app_comm_cons, (app_cons (_, s)) in H3. 
      rewrite <-app_comm_cons, (app_assoc (t6++_)) in H3. apply (H3 eq_refl). now rewrite app_assoc, ostartof_niltail. assumption. constructor.
      apply inblockx_cons. now inversion IB0. repeat (rewrite Forall_app; split). eapply Forall_impl. apply inblockx_cons. now inversion IB0. constructor. apply inblock_start. easy. easy. constructor. apply inblock_start. easy.
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
Lemma afterblock_cond:
  forall P b p s i l cond
  (B: arm_assemble_all_cond l cond = Some b)
  (I: i < 2^30 - 64)
  (L: (1 <= length l < 64)%nat)
  (MB: MaintainsBlock p b i i s)
  (AB: match arm_assemble_all l with
       | Some b' => forall s,
           MaintainsBlock p b' (i + N.of_nat (length b - length b')) (i + N.of_nat (length b - length b')) s ->
           AfterBlock P b' p s (i + N.of_nat (length b - length b')) (i + N.of_nat (length b - length b'))
       | _ => True
       end)
  (PA: forall s, P (Addr ((i + N.of_nat (length b))*4), s))
  (PS: forall s, P (Addr ((i + 1)*4), s)),
    AfterBlock P b p s i i.
Proof.
  intros.

  unfold arm_assemble_all_cond in B. destruct Z.ltb. 
    apply arm_assemble_all_first in B as [? [? [? [? ?]]]]. subst.
    apply afterblock_cons. assumption. intros.
    rewrite H1 in H0.
    cbv[arm2il arm_b_il BranchWritePC arm_R] in H0. apply forget_cond in H0. remember (i*4). remember (scast _ _ _). step_stmt H0.
    destruct N.modulo; destruct H0 as [H0 _]; step_stmt H0; destruct H0 as [[_ ?] _].

      left. repeat split. assumption. simpl length in AB. rewrite H, Nat.sub_succ_l, Nat.sub_diag in AB. intro. apply AB. assumption. lia. easy.

      assert (n ⊕ 8 ⊕ n0 .& 4294967292 = (i + N.of_nat (S(length l)))*4) as E.
      {
        subst.
        rewrite N.mul_add_distr_r, N.shiftl_mul_pow2. rewrite <-Z_nat_N, Z2Nat.inj_sub, Nat2Z.id, Nat2N.inj_sub, Z_nat_N by easy.
        cbn. rewrite N.mul_sub_distr_r. unfold scast. epose proof (proj1 (toZ_nonneg _ _)). rewrite H0.
        rewrite (N.mod_small _ (2^26)), N2Z.inj_sub, N2Z.inj_mul, nat_N_Z by lia. cbn. unfold ofZ. rewrite Z2N.inj_mod by lia. replace (Z.to_N (_ - _)) with (N.of_nat (length l) * 4 - 4) by lia. rewrite <-N.Div0.add_mod.
        change 4294967296 with (2^32). rewrite N_land_mod_pow2_move by lia.
        change (4294967292 mod 2 ^ 32) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
        rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r. lia. apply N.log2_lt_pow2. lia. lia. enough (N.of_nat (length l) * 4 - 4 < 2^ 25). rewrite N.mod_small by lia. apply H2. lia.
      }
      simpl length in PA. apply arm_assemble_all_len in H.
      right. right. left. repeat esplit. apply H0. rewrite E, H. apply PA.
      unfold InBlock. rewrite E. simpl length. lia.

   rewrite B, Nat.sub_diag, N.add_0_r in AB. apply AB, MB.
Qed.


Lemma afterblock_fallthru:
  forall P b b' p s bi, Forall (fun z => forall s c' s' x i a, exec_stmt armc s (arm2il i (arm_decode z)) c' s' x -> x <> Some (Addr a)) (b++[b']) ->
  (forall a s, InBlock (Z.of_N bi) (length (b++[b'])) a -> P (Addr a, s)) ->
  (MaintainsBlock p (b++[b']) bi bi s) ->
  (forall s, P (Addr ((bi + N.of_nat (length (b++[b'])))*4), s)) -> AfterBlock P (b++[b']) p s bi bi.
Proof.
  induction b. - intros. simpl. apply afterblock_cons. simpl in H0. assumption. intros. destruct x. destruct e. inversion H. apply (H6 _ _ _ _ _ a) in H3. contradiction.
  right. right. right. now exists i. right. left. repeat split. apply H2.
  - simpl. intros. apply afterblock_cons. assumption. intros. destruct x. destruct e. inversion H. apply (H6 _ _ _ _ _ a0) in H3. contradiction.
  right. right. right. now exists i. left. repeat split. intro. apply IHb. inversion H. assumption. intros. apply H0. unfold InBlock in *. split. lia. easy. assumption.
  remember (length _). 
  Search (_ + N.of_nat _). intros. 
  rewrite <-(N2Nat.id 1), <-N.add_assoc, <- Nat2N.inj_add. apply H2. apply H0. split. rewrite length_app. simpl. lia. apply N.divide_factor_r.
Qed.
Lemma afterblock_fallthru':
  forall P b p s bi, Forall (fun z => forall s c' s' x i a, exec_stmt armc s (arm2il i (arm_decode z)) c' s' x -> x <> Some (Addr a)) b -> 
  (forall a s, InBlock (Z.of_N bi) (length b) a -> P (Addr a, s)) ->
  (1 <= length b)%nat ->
  (MaintainsBlock p b bi bi s) ->
  (forall s, P (Addr ((bi + N.of_nat (length b))*4), s)) -> AfterBlock P b p s bi bi.
Proof.
  intros. destruct b. now simpl in H1. destruct (exists_last (ltac:(discriminate):z::b<>[])) as [? [? ?]]. rewrite e in *. now apply afterblock_fallthru.
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

Definition SafeAfterBlock i2i' pol ai i irm p s := AfterBlock (SafeDestX i2i' pol ai i (length irm)) irm p s (Z.to_N (i2i' i)) (Z.to_N (i2i' i)).
Lemma SafeDest_rewrite_inst:
  forall tc i2i' z pol i ti ai bi txt irm' table tc' p s1
    (TC: True) (* table cache is consistent with memory *)
    (AI: (0 <= ai < 2^30)%Z)
    (TI: (0 <= ti < 2^30)%Z)
    (I:  (0 <=  i < 2^30)%Z)
    (BI: (0 <= bi < 2^30)%Z)
    (AIB: ~ InBlock (i2i' i) (length irm') (Z.to_N ai * 4))
    (I2I': (0 <= i2i' i < 2^30)%Z)
    (I2I'': (i2i' (i + 1) = i2i' i + Z.of_nat (length irm'))%Z)
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (irm', table, tc'))
    (MB: MaintainsBlock p irm' (Z.to_N (i2i' i)) (Z.to_N (i2i' i)) s1),

    SafeAfterBlock i2i' pol ai i irm' p s1.
Proof.
  intros.

  assert (
    forall l cond, arm_assemble_all_cond l cond = Some irm' ->
      (1 <= length l < 64)%nat ->
      In (Z.add i 1) (pol i) ->
      match arm_assemble_all l with
      | Some b' => forall s,
        MaintainsBlock p b'
          (Z.to_N (i2i' i) + N.of_nat (length irm' - length b'))
          (Z.to_N (i2i' i) + N.of_nat (length irm' - length b')) s ->
        AfterBlock (SafeDestX i2i' pol ai i (length irm')) b' p s
          (Z.to_N (i2i' i) + N.of_nat (length irm' - length b'))
          (Z.to_N (i2i' i) + N.of_nat (length irm' - length b'))
      | None => True
      end ->
    SafeAfterBlock i2i' pol ai i irm' p s1
  ) as C. {
    intros. eapply afterblock_cond. apply H. admit. assumption. assumption. assumption. 
      intros. unfold SafeDestX, SafeDest. simpl. left. right. exists (i+1)%Z. split. unfold i2a', to_a. lia. assumption.
      intros. unfold SafeDestX, SafeDest. simpl. 
      destruct (Nat.eq_dec (length irm') 1). left. right. exists(i+1)%Z. split. unfold i2a', to_a. lia. assumption.
      right. unfold InBlock. split. split. lia.
      apply arm_assemble_all_cond_len in H.
      lia. apply N.divide_factor_r.
  }
  assert (
    forall l cond, arm_assemble_all_cond l cond = Some irm' ->
      (Forall (fun q => forall s c' s' x i a, exec_stmt armc s (arm2il i q) c' s' x  -> x <> Some (Addr a)) l) ->
      (1 <= length l < 64)%nat ->
      In (Z.add i 1) (pol i) ->
    SafeAfterBlock i2i' pol ai i irm' p s1
  ) as FT. {
    intros. eapply C. apply H. assumption. assumption.
    destruct arm_assemble_all eqn:e; auto.
    intros. apply afterblock_fallthru'.
      apply arm_assemble_all_eq in e. rewrite <-e, Forall_map in H0. assumption.
      intros. cbv[SafeDestX fst]. right.
        rewrite N2Z.inj_add, Z2N.id, nat_N_Z in H4 by lia. apply arm_assemble_all_cond_len in H.  apply arm_assemble_all_len in e.
        remember (_ - _)%nat. assert (n = 0 \/ n = 1)%nat. destruct n. now left. right.  lia. destruct H5. replace (length irm') with (length l0) by lia. now rewrite H5, Z.add_0_r in H4. unfold InBlock in *. split. lia. easy. apply arm_assemble_all_len in e. lia.
        assumption.
        intros. cbv[SafeDestX fst SafeDest]. left. right. exists (i+1)%Z. split. unfold i2a', to_a. rewrite <- N.add_assoc, <- Nat2N.inj_add, <-Nat.sub_sub_distr, Nat.sub_diag, Nat.sub_0_r, I2I''. lia. lia. apply arm_assemble_all_cond_len in H. apply arm_assemble_all_len in e. lia. assumption.
  }

  assert (
    forall sanitized_inst cond reg tc,
      rewrite_pc_no_jump sanitized_inst cond i reg tc = Some (irm', table, tc') ->
      (forall s c' s' x i a, exec_stmt armc s (arm2il i sanitized_inst) c' s' x  -> x <> Some (Addr a)) ->
      reg <> 15%Z ->
      In (Z.add i 1) (pol i) ->
    SafeAfterBlock i2i' pol ai i irm' p s1
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
    SafeAfterBlock i2i' pol ai i irm' p s1
  ) as RPSNJ. {
    intros. eapply FT. unfold rewrite_pc_sp_no_jump, wo_table in H. destruct_match_in H; try discriminate.
    inversion H. subst. apply e. faft. simpl. lia. assumption.
  }
  assert (goto_abort (i2i' i) ai tc = Some (irm', table, tc') -> SafeAfterBlock i2i' pol ai i irm' p s1) as GA.
  {
    intros. unfold goto_abort in H; destruct_match_in H; try discriminate. inversion H; subst.
    apply afterblock_cons. assumption. intros. right. right. left. rewrite <-(Z2N.id (i2i' i)), <-(Z2N.id ai) in e by (apply I2I' || lia).
    eapply GOTOz_correct in e. exists (Z.to_N ai * 4). repeat split. apply e. unfold SafeDestX. simpl. left. left. unfold to_a. lia. now rewrite Z2N.id by apply I2I'. lia. lia. apply H0.
  }
  assert (
    irm' = [z] ->
    In (Z.add i 1) (pol i) ->
    (forall c s c' s' x a, exec_stmt c s (arm2il (Z.to_N (i2i' i) * 4) (arm_decode z)) c' s' x -> x <> Some (Addr a)) ->
    SafeAfterBlock i2i' pol ai i irm' p s1
  ) as FTS. {
    intros. subst.
    apply afterblock_cons. assumption. intros.
    destruct x eqn:e. destruct e0. now eapply H1 in H. right. right. right. now exists i0. right. left. split. easy. split. easy.
    unfold SafeDestX, SafeDest. simpl. left. right. exists (Z.add i 1). split. unfold i2a', to_a. rewrite N2Z.inj_mul, N2Z.inj_add, Z2N.id, I2I'', Z.mul_comm. easy.
    apply I2I'. assumption.
  }

  unfold rewrite_inst, PC, Z1, Z15 in RI. destruct_match_in RI; try discriminate;
  match type of RI with
  | context[goto_abort] => now apply GA
  | context[Some ([z], _, _)] => apply FTS; [now inversion RI| rewrite negb_false_iff in e; now apply In_contains in e|faft]
  | context[rewrite_mov_lr_pc]=>
    unfold rewrite_mov_lr_pc, wo_table in RI; destruct_match_in RI; try discriminate; inversion RI; subst; eapply FT; [apply e4|faft| simpl; lia|rewrite negb_false_iff in e; now apply In_contains in e]
  | context[wo_table]=>
    unfold wo_table in RI; destruct_match_in RI; try discriminate; inversion RI; subst; eapply FT; [apply e6|faft| simpl; lia|rewrite negb_false_iff in e; now apply In_contains in e]
  | context[rewrite_pc_no_jump] => eapply RPNJ; [apply RI|faft|try apply unused_reg_not_pc;easy ..|rewrite negb_false_iff in e;now apply In_contains in e]
  | context[rewrite_pc_sp_no_jump]=> eapply RPSNJ; [apply RI|faft|try apply unused_reg_bound;easy ..|rewrite negb_false_iff in e;now apply In_contains in e]
  | _ => clear C GA FT FTS RPNJ RPSNJ
  end.
