Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import PArith.
Require Import Picinae_armv7.
Require Import memset_arm.

Import ARMNotations.
Open Scope N.
Open Scope list_scope.
Import List.ListNotations.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

Theorem strlen_nwc: forall s2 s1, memset_arm s1 = memset_arm s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog armtypctx memset_arm.
Proof.
  Picinae_typecheck.
Qed.

(* ARMv7 calling convention specifies variable registers to be preserved during calls. *)
Definition armcc_vreg :=
  [R_R4; R_R5; R_R6; R_R7; R_R8; R_R10; R_R11].
(*   v1    v2    v3    v4    v5     v7     v8*)
(* R_R9/v6 is a special case, its behavior is platform-specific *)

(* TODO: correct way to do this? *)
Definition cons_eq :
  forall {A} (x : A) xs y ys, x = y -> xs = ys -> x::xs = y::ys.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Definition arm_vreg_preserves prog :=
  forall s n s' x,
    exec_prog fh prog 0 s n s' x
    -> List.map s' armcc_vreg = List.map s armcc_vreg.

Theorem memset_preserves_vreg : arm_vreg_preserves memset_arm.
  unfold arm_vreg_preserves.
  intros.
  compute.
  repeat apply cons_eq;
    try reflexivity;
    (eapply noassign_prog_same; [|eassumption]; prove_noassign).
Qed.

Theorem memset_preserves_rsp :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_SP = s R_SP.
  intros.
  eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Theorem memset_ret :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_R0 = s R_R0.
  intros.
  eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Definition memfilled (m:addr->N) (s:addr) (c:N) n :=
  forall i, i < n -> m (s⊕i) = c.

Definition memset_bytedup c :=
  (c .| ((c << 8) mod 2 ^ 32)
     .| ((c .| ((c << 8) mod 2 ^ 32) << 16) mod 2 ^ 32)).
(* Definition memset_bytedup b := *)
(*   let c := b mod (2 ^ 8) *)
(*   in c .| c<<8 .| c<<16 .| c<<24. *)

Definition memset_invs (s:addr) (c:N) n (a:addr) (st:store) :=
  let common_inv :=
      exists r1 r2 r3 prog m,
        st V_MEM32 = Ⓜm
        /\ st R_R0 = Ⓓs
        /\ st R_R1 = Ⓓr1
        /\ st R_R2 = Ⓓr2
        /\ st R_R3 = Ⓓr3
        /\ r3 = s ⊕ prog
        /\ c = r1 mod (2^8)
        /\ Ⓓ(s ⊕ n) = Ⓓ(r3 ⊕ r2)
        /\ memfilled m s c prog
  in match a with
     | 0 => Some (exists m ci,
                     st V_MEM32 = Ⓜm
                     /\ st R_R0 = Ⓓs
                     /\ st R_R1 = Ⓓci
                     /\ st R_R2 = Ⓓn
                     /\ c = ci mod (2^8))
     (* | 4 => Some (st R_R2 = Ⓓn /\ common_inv) *)
     | 12 => Some common_inv
     | 44 => Some (st R_R1 = Ⓓ(memset_bytedup c)
                   /\ st R_R1 = st R_R12
                   /\ common_inv)
     | 84 => Some common_inv
     | _ => None
     end.

Definition memset_post s c n (_:exit) (st:store) :=
  exists m, st V_MEM32 = Ⓜm /\ st R_R0 = Ⓓs /\ memfilled m s c n.

Definition memset_invset s c n :=
  invs (memset_invs s c n) (memset_post s c n).

Theorem mod_greater (n d1 d2:N) :
  d1 ≠ 0 -> d1 <= d2 -> (n mod d1) mod d2 = n mod d1.
  intros.
  apply N.mod_small.
  eapply N.lt_le_trans; eauto.
  apply N.mod_upper_bound.
  exact H.
Qed.

Theorem mod_same (n d:N) : d ≠ 0 -> (n mod d) mod d = n mod d.
  intros.
  apply mod_greater; auto.
  apply N.le_refl.
Qed.

Lemma memfilled_split :
  forall m s c n1 n2,
    memfilled m s c n1
    -> memfilled m (s + n1) c n2
    -> memfilled m s c (n1 + n2).
  intros.
  unfold memfilled in *.
  intros.
  destruct (N.lt_ge_cases i n1); auto.
  rewrite <- (H0 (i - n1)).
  (* rewrite (N.add_comm n0). *)
  rewrite <- N.add_assoc.
  rewrite (N.add_comm n1).
  rewrite N.sub_add; auto.
  eapply N.le_lt_add_lt.
  apply N.le_refl.
  rewrite N.sub_add; auto.
  rewrite N.add_comm.
  assumption.
Qed.

Lemma memfilled_mod :
  forall m s c n,
    memfilled m s c n
    -> memfilled m s c (n mod (2^32)).
  unfold memfilled.
  intros.
  apply H.
  destruct (N.lt_ge_cases n (2^32)).
  rewrite N.mod_small in H0; auto.
  eapply N.lt_trans; try eassumption.
  eapply N.lt_le_trans; try eassumption.
  apply N.mod_upper_bound; auto.
  discriminate.
Qed.

Lemma memfilled_update :
  forall m s c n a,
    memfilled m s c n
    -> memfilled (m[Ⓑ a := c]) s c n.
  rewrite setmem_1.
  unfold update,memfilled.
  intros.
  destruct (_ == _); auto.
Qed.

Lemma xplus_assoc : forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c.
  simpl.
  intros.
  rewrite N.add_mod_idemp_r, N.add_mod_idemp_l, N.add_assoc;
    reflexivity + discriminate.
Qed.

Fixpoint posmod2 p w :=
  match p,w with
  | xH,_ | xI _,xH => 1
  | xO _,xH => 0
  | xO p',_ => N.double (posmod2 p' (Pos.pred w))
  | xI p',_ => N.succ (N.double (posmod2 p' (Pos.pred w)))
  end.

Definition mod2 n w :=
  match n,w with | 0,_ | _,0 => 0 | N.pos n',N.pos w' => posmod2 n' w' end.

Theorem npossucc p : N.pos (Pos.succ p) = N.succ (N.pos p). auto. Qed.

Theorem mod2_eq : forall n w, mod2 n w = n mod 2^w.
  destruct n as [|n],w as [|w]; auto using N.mod_1_r.
  unfold mod2.
  generalize dependent n.
  induction w using Pos.peano_ind.
  intros.
  rewrite <- N.bit0_mod.
  simpl.
  destruct n; reflexivity.
  intros.
  Search N.succ Pos.succ.
  rewrite npossucc.
  Search "^" N.succ.
  rewrite N.pow_succ_r; try discriminate.
  Search (_ mod (_ * _)).
  rewrite N.mod_mul_r; try discriminate.
  simpl.
  Search (_ / 2).
  rewrite <- N.div2_div.
  rewrite <- N.bit0_mod.
  destruct n; simpl; try rewrite Pos.pred_succ; try rewrite IHw; simpl; auto;
    destruct (_ mod _),w; simpl; reflexivity.
Qed.

Definition typType t :=
  match t with | NumT _ => N | MemT _ => addr -> N end.
Print armtypctx.
Definition opTypType t :=
  match t with | None => value | Some t' => typType t' end.

Print hastyp_val.
Print welltyped_memory.

Print VaM.
Print unit.

Print hastyp_val.
Program Definition wtgetval v t : hastyp_val v t -> typType t :=
  match t as t return hastyp_val v t -> typType t with
  | NumT w => fun H => match v with VaN n _ => n | _ => False_rec _ _ end
  | MemT _ => fun H => match v with VaM m _ => m | _ => False_rec _ _ end
  end.
Next Obligation. inversion H. subst. eapply H0. reflexivity. Qed.
Next Obligation. inversion H. subst. eapply H1. reflexivity. Qed.
Print models.

Print typctx.
Print models.

Definition hasoptyp_val v t :=
  match t with None => True | Some t' => hastyp_val v t' end.

Definition wtgetoptval v t : hasoptyp_val v t -> opTypType t :=
  match t with
  | Some t' => fun H => wtgetval v t' H
  | None => fun _ => v
  end.

Definition wtref' tc st id (H : models tc st)
  : opTypType (tc id) :=
  let v := st id in
  wtgetoptval v (tc id)
              (match tc id as t
                     return (forall t', t = Some t' -> hasoptyp_val v (Some t'))
                            -> hasoptyp_val (st id) t with
               | None => fun _ => I
               | Some t' => fun H => H t' eq_refl
               end (H id)).
Print False_rec.
(* Program Definition wtref' tc st id (H : models tc st) *)
(*   : opTypType (tc id) := *)
(*   (match tc id as t *)
(*          return match t with None => unit | Some t' => hastyp_val (st id) t' end *)
(*                 -> opTypType t *)
(*    with *)
(*    | None => fun _ => st id *)
(*    | Some tc' => wtgetval (st id) tc' *)
(*    end) _. *)
(* Next Obligation. specialize (H id). destruct (tc id); auto. constructor. Qed. *)

Print store.
Definition wtstore ctx := { st | models ctx st }.

Locate "{ _ | _ }".
Print sig.
Definition wtref tc wts id :=
  match wts with | exist _ st H => wtref' tc st id H end.

Print store.
Print wtref.

Definition wtutref tc wts id : value :=
  match tc id as tc' return opTypType tc' -> value with
  | Some (NumT w) => fun n => VaN n w
  | Some (MemT w) => fun m => VaM m w
  | None => fun v => v
  end (wtref tc wts id).

Theorem wtntref : forall ctx st id MDL,
    st id = wtutref ctx (exist _ st MDL) id.
  intros.
  unfold wtutref,wtref,wtref'.
  simpl.
  unfold models in *.
  generalize (MDL id).
  intros.
  destruct (ctx id); auto.
  generalize dependent (h t eq_refl).
  clear MDL h.
  intros.
  destruct (st id),t; simpl; inversion h; subst; reflexivity.
Qed.

Compute (fun st => wtref armtypctx st R_R0).
Compute (opTypType (armtypctx R_R0)).

Definition memset_invs_alt' (s:addr) (c:N) n (a:addr) (st:store) :=
  let wts MDL := wtref armtypctx (exist _ st MDL) in
  let common_inv MDL :=
      exists prog,
        (* st V_MEM32 = Ⓜm *)
        (* /\ st R_R0 = Ⓓs *)
        (* /\ st R_R1 = Ⓓr1 *)
        (* /\ st R_R2 = Ⓓr2 *)
        (* /\ st R_R3 = Ⓓr3 *)
        s = wts MDL R_R0
        /\ c = wts MDL R_R1 mod 2^8
        /\ wts MDL R_R3 = s ⊕ prog
        /\ memfilled (wts MDL V_MEM32) s c (n - wts MDL R_R2)
  in match a with
     | 0 => Some (fun MDL =>
                    s = wts MDL R_R0
                    /\ c = wts MDL R_R1 mod 2^8
                    /\ n = wts MDL R_R2)
     (* | 4 => Some (st R_R2 = Ⓓn /\ common_inv) *)
     | 12 => Some common_inv
     | 44 => Some (fun MDL =>
                     wts MDL R_R1 = memset_bytedup c
                     /\ wts MDL R_R12 = wts MDL R_R1
                     /\ common_inv MDL)
     | 84 => Some common_inv
     | _ => None
     end.

Definition memset_invs_alt s c n a st :=
  option_map (fun P => exists MDL, P MDL) (memset_invs_alt' s c n a st).

Definition memset_invset_alt s c n :=
  invs (memset_invs_alt s c n) (memset_post s c n).

Check wtref'.
Check hastyp_val.
Theorem hastyp_preserve : forall tc st a v,
    models tc st
    -> match (tc a) with | Some t => hastyp_val v t | _ => True end
    -> models tc (update st a v).
  intros.
  unfold models in *.
  intros.
  specialize (H v0 t CV).
  unfold update.
  simpl.
  destruct vareq; subst; auto.
  rewrite CV in H0.
  assumption.
Qed.

Print iseq.
Print sumbool.

Theorem wtupdate : forall tc st a v,
    models tc st -> hasoptyp_val v (tc a) -> models tc (update st a v).
  intros.
  unfold models in *.
  intros.
  specialize (H v0 t CV).
  unfold update.
  destruct (_ == _); subst; auto.
  rewrite CV in H0.
  assumption.
Qed.

Theorem wtref'_update' : forall tc st id a v H1 H2 H3,
    wtref' tc (update st a v) id H3 =
    match (iseq id a) with
    | left eq_refl => wtgetoptval v _ H2
    | _ => wtref' tc st id H1
    end.
  unfold update.
  simpl.
  intros.
  unfold wtref'.
  simpl.
  generalize (H3 id),(H1 id).
  destruct vareq; intros; simpl; destruct (tc id); subst; auto; simpl.
  simpl in H2.
  destruct v,t; inversion H2; subst; reflexivity.
  generalize (h t eq_refl).
  intros.
  destruct (st id),t; inversion h1; subst; reflexivity.
Qed.
Check wtref'_update'.

Require Import Program.

Theorem wtref'_update : forall tc st id a v H1 H2,
    wtref' tc (update st a v) id (wtupdate tc st a v H1 H2) =
    match (iseq id a) return hasoptyp_val v (tc a) -> opTypType (tc id) with
    | left p => match p with eq_refl => fun H2 => wtgetoptval v _ H2 end
    | _ => fun _ => wtref' tc st id H1
    end H2.
  intros.
  generalize (wtupdate tc st a v H1 H2).
  intros.
  unfold models,update in *.
  simpl.
  unfold wtref'.
  simpl.
  unfold wtgetoptval.
  simpl.
  generalize (H1 id).
  generalize (m id).
  intros.
  destruct st.
  destruct (h0 (tc id)).
  destruct (tc id).
  destruct t.
  specialize (h0 (NumT w0) eq_refl).
  inversion h0; subst; auto.
  specialize (h0 (MemT w0) eq_refl).
  inversion h0.
  inversion h0.
  subst.
  inversion h0.
  reflexivity.
  inversion h0.
  destruct (st id).
  destruct (tc id).
  assert (X := vareq id a).
  destruct X.
  subst.
  assert (forall x, exists y, vareq x x = left y).
  intros.
  destruct vareq.
  exists e.
  reflexivity.
  destruct n.
  reflexivity.
  specialize (H a).
  destruct H.
  2: { destruct vareq.
  destruct (vareq a a),(tc a).
  rewrite H.
  dependent rewrite (H a).
  rewrite H0.
  destruct x; econstructor; try reflexivity.
  destruct vareq.
  simpl.
  assert (forall m, N.eq_dec m m = left eq_refl).
  intros.
  destruct N.eq_dec; try discriminate.
  compute.
  dependent destruction e.
  auto.
  reflexivity.
  destruct N.eq_dec; simpl.
  reflexivity.
  simpl.
  destruct n; auto.
  simpl.
  destruct (V_TEMP n); auto.
  Print V_TEMP.
  destruct (V_TEMP n).
  fold (iseq a a).
  destruct vareq.
  destruct vareq as [[]|[]].
  unfold update.
  intros.
  (* destruct id,a; compute. *)
  unfold wtref',wtgetoptval.
  simpl.
  generalize (wtupdate tc st a v H1 H2 id).
  generalize (H1 id).
  intros.
  simpl.
  rename h into Q1111.
  rename h0 into Q1112.
  destruct vareq,(tc id).
  generalize (wtgetval_obligation_1 _ _).
  destruct (tc id).
  compute.
  dependent destruction (tc id).
  destruct (st id).
  dependent destruction (vareq id a).
  destruct vareq.
  destruct vareq.
  erewrite wtref'_update'.
  Unshelve.
  all: auto.
  2: {
  apply wtref'_update'.
  unfold update.
  simpl.
  intros.
  unfold wtref'.
  simpl.
  generalize (H3 id),(H1 id).
  destruct vareq; intros; simpl; destruct (tc id); subst; auto; simpl.
  simpl in H2.
  destruct v,t; inversion H2; subst; reflexivity.
  generalize (h t eq_refl).
  intros.
  destruct (st id),t; inversion h1; subst; reflexivity.
Qed.

Theorem strlen_partial_correctness_alt:
  forall st lr s ci c n q st' x m
         (MDL0: models armtypctx st)
         (LR0: st R_LR = Ⓓlr) (MEM0: st V_MEM32 = Ⓜm)
         (R0: st R_R0 = Ⓓs) (R1: st R_R1 = Ⓓci) (R2: st R_R2 = Ⓓn)
         (C: c = ci mod 2^8)
         (RET: memset_arm st lr = None)
         (XP0: exec_prog fh memset_arm 0 st q st' x),
    trueif_inv (memset_invset_alt s c n memset_arm x st').
  intros.
  eapply prove_invs.
  exact XP0.
  simpl.
  exists MDL0.
  assert (X := fun id => wtntref armtypctx st id MDL0).
  unfold wtutref,wtref in X.
  rewrite X in *; simpl in *.
  inversion R0; subst.
  inversion R1; subst.
  inversion R2; subst.
  tauto.
  intros.
  shelve_cases 32 PRE. Unshelve.
  destruct PRE.
  intuition.
  Local Ltac step := time arm_step.
  repeat step.
  econstructor.
  econstructor.
  unfold wtref.
  repeat split.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  erewrite wtref'_update.
  simpl.
  erewrite (wtntref armtypctx) in Hsv.
  unfold wtutref in Hsv.
  simpl in Hsv.
  inversion Hsv.
  rewrite H0.
  simpl.
  reflexivity.
  5: { destruct PRE. destruct H. intuition. repeat step.
       all: try discriminate.
       do 2 econstructor.
       intuition.
       unfold wtref.
       erewrite wtref'_update.
       erewrite wtref'_update.
       simpl.
       rewrite
       erewrite wtref'_update.
       erewrite wtref'_update.
       erewrite wtref'_update.
       erewrite wtref'_update.
       erewrite wtref'_update.
       erewrite wtref'_update.
       simpl.
  simpl.
  rewrite H0.
  simpl.
  unfold wtref'.
  simpl.
  generalize (eq_refl (s1 R_R0)).
  Search wtref.
  simpl.
  rewrite Hsv.
  destruct e.
  destruct (s1 R_R0).
  rewrite Hsv.
  red.
  simpl 1.
  simpl 1.
  simpl .
  red.
  simpl.

Theorem strlen_partial_correctness:
  forall st lr s ci c n q st' x m
         (MDL0: models armtypctx st)
         (LR0: st R_LR = Ⓓlr) (MEM0: st V_MEM32 = Ⓜm)
         (R0: st R_R0 = Ⓓs) (R1: st R_R1 = Ⓓci) (R2: st R_R2 = Ⓓn)
         (C: c = ci mod 2^8)
         (RET: memset_arm st lr = None)
         (XP0: exec_prog fh memset_arm 0 st q st' x),
    trueif_inv (memset_invset s c n memset_arm x st').
  intros.
  eapply prove_invs.
  exact XP0.
  simpl.
  eauto 7.
  intros.
  assert (Q : s < 2^32).
  unfold models in MDL0.
  edestruct (MDL0 R_R0); try reflexivity.
  inversion R0; subst; auto.
  inversion R0; subst; auto.
  assert (Q0 : s mod 2^32 = s).
  apply N.mod_small; auto.
  assert (Q1 : s ⊕ 0 = s).
  rewrite N.add_0_r.
  assumption.
  shelve_cases 32 PRE. Unshelve.

  Local Ltac step := time arm_step.
  step. step. step.
  destruct PRE.
  destruct H.
  intuition.
  rewrite H0,H,H1,H2,H4.
  exists x1.
  exists n.
  exists s.
  exists 0.
  exists x0.
  intuition.
  unfold memfilled.
  intros.
  destruct i; discriminate.
  destruct PRE.
  destruct H.
  intuition.
  exists x1,n,s,0,x0.
  intuition.
  rewrite H.
  reflexivity.
  unfold memfilled.
  intros.
  destruct i; discriminate.

  destruct PRE.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  intuition.
  repeat (step + discriminate).
  rewrite <- H5.
  unfold memset_bytedup.
  split; try reflexivity.
  (* admitting bitwise arithmetic *)
  split; try reflexivity.
  do 5 econstructor.
  intuition.
  eassumption.
  rewrite H5.
  (* assert (mod_lor : forall  *)
  (* replace ((x0 mod 2^8 << 8) mod 2^32) with (x0 mod 2^8 << 8). *)
  (* replace ((x0 mod 2^8) .| (x0 mod 2^8 << 8)) with  *)
  (* admitting bitwise arithmetic *)
  admit.
  assumption.
  do 5 econstructor.
  intuition.
  rewrite H4.
  symmetry.
  apply xplus_assoc.
  rewrite H6.
  rewrite N.add_mod_idemp_r, N.add_mod_idemp_l; try discriminate.
  rewrite <- N.add_assoc.
  rewrite N.sub_1_r.
  rewrite N.add_1_l.
  rewrite N.succ_pred.
  rewrite (N.add_comm (2^32)).
  rewrite N.add_assoc.
  rewrite mod_add_r; try discriminate.
  reflexivity.
  destruct x1; discriminate.

  apply memfilled_mod.
  apply memfilled_split.
  rewrite <- H5.
  unfold memfilled.
  unfold memfilled in H8.
  rewrite setmem_1.
  unfold update.
  intros.
  destruct iseq; auto.
  unfold memfilled.
  unfold memfilled in H8.
  intros.
  destruct i; try (destruct p; discriminate).
  rewrite N.add_0_r.
  rewrite <- H4.
  rewrite setmem_1.
  unfold update.
  destruct (iseq_refl x2). (* WTF involving N vs addr *)
  rewrite <- H5.
  simpl in H9.
  simpl.
  rewrite H9.
  reflexivity.

  intuition.
  repeat match goal with [ H : exists x : _, _ |- _ ] => destruct H end.
  intuition.
  repeat (discriminate + step). (* OOM *)
  intuition.
  rewrite H3 in H.
  exact H.
  rewrite <- H3.
  assumption.
  do 5 econstructor.
  intuition.
  rewrite H6.
  repeat rewrite <- xplus_assoc.
  reflexivity.
  Search setmem.
  rewrite H6.
  assert (xplusinv : forall b c,
             b < 2^32 -> c < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c).
  intros.
  rewrite N.add_mod_idemp_r; try discriminate.
  rewrite N.add_comm.
  rewrite (N.add_comm (2^32)).
  rewrite N.sub_add.
  rewrite mod_add_r; try discriminate.
  apply N.mod_small; auto.
  eapply N.le_trans.
  apply N.lt_le_incl.
  eassumption.
  rewrite N.add_comm.
  apply N.le_add_r.
  repeat rewrite <- xplus_assoc.
  assert (8 < 2^8); try reflexivity.
  repeat rewrite xplusinv;
    try reflexivity; try apply N.mod_upper_bound; try discriminate.
  rewrite xplus_assoc.
  rewrite <- H6.
  assumption.
  (* not sure this can be proven, may need to carry around type in invariants *)
  admit.
  Print setmem.
  Print setmem_big.
  Print setmem.
  Locate "[".
  Print memfilled.
  assert (memfilled_bytedup : forall m s c,
             c < 2 ^ 8 -> memfilled (m [Ⓓs := memset_bytedup c]) s c 4).
  intros.
  unfold memfilled.
  intros.
  simpl.
  unfold setmem_little,Mb,ARMArch.mem_bits.
  assert (bytedup_spec : forall c,
             c < 2^8 ->
             memset_bytedup c mod 2^8 = c /\
             memset_bytedup c >> 8 mod 2^8 = c /\
             memset_bytedup c >> 16 mod 2^8 = c /\
             memset_bytedup c >> 24 mod 2^8 = c).
  intros.
  unfold memset_bytedup.
  Check N.mod_small.
  repeat rewrite (N.mod_small _ (2^32)).
  Search ">>" N.lor.
  repeat rewrite N.shiftl_lor + rewrite N.shiftr_lor.
  replace 24 with (8 + 16).
  replace 16 with (8 + 8).
  repeat rewrite <- N.shiftl_shiftl + rewrite <- N.shiftr_shiftr.
  Search "<<" ">>".
  Search ">>".
  Search "<<" ">>".
  Search ">>".
  repeat rewrite N.shiftr_shiftl_r,N.shiftr_0_r; auto using N.le_refl.
  replace (c1 >> 8) with 0.
  simpl.
  Search N.modulo N.lor.
  Search N.modulo N.mul.
  Locate "<<".
  Print N.shiftl.
  Print Pos.shiftl.
  assert (orlmod : forall a b w, (a .| b) mod 2^w = (a mod 2^w) .| (b mod 2^w)).
  intros.
  generalize dependent b.
  generalize dependent a.
  Search "ind" "<".
  Search "strong" N.
  Search "wf" N.
  Search "well".
  Check well_founded.
  Check N.lt_wf.
  induction w using (well_founded_induction N.lt_wf_0).
  Search "peano".
  destruct w using N.peano_rec.
  simpl.
  intros.
  repeat rewrite N.mod_1_r.
  reflexivity.
  clear IHw.
  destruct w using N.peano_rec.
  (* destruct a,b; auto. *)
  (* simpl. *)
  (* rewrite N.lor_comm. *)
  (* reflexivity. *)
  intros.
  simpl.
  repeat rewrite <- N.bit0_mod.
  destruct a as [|[| |]],b as [|[| |]]; compute; reflexivity.
  clear IHw.
  intros.
  rewrite <- N.add_1_l.
  rewrite N.pow_add_r.
  repeat rewrite N.mod_mul_r; try apply N.pow_nonzero; try discriminate.
  Search ".|" "/".
  Search ".|" ">>".
  Locate ">>".
  Print N.shiftr.
  Search N.modulo 2%N.
  Search "/" ">>".
  repeat rewrite <- N.shiftr_div_pow2.
  Search ">>" ".|".
  rewrite N.shiftr_lor.
  rewrite H13.
  rewrite H13.
  Search ".|" "+".
  repeat rewrite (N.mul_comm (2^_)).
  Search "<<" "*".
  repeat rewrite <- N.shiftl_mul_pow2.
  Search "+" ".|".
  Search "recomp".
  Search N.modulo ">>".
  Search ".|" "+".
  assert (L : forall a b w, a mod 2^w .& (b << w) = 0).
  intros.
  generalize dependent b0.
  generalize dependent a0.
  induction w0 using N.peano_rec.
  Search (_ mod 1).
  intros.
  rewrite N.mod_1_r.
  reflexivity.
  intros.
  destruct a0; auto.
  destruct p; simpl.
  Search N.modulo 2.
  repeat rewrite <- lor_plus.
  repeat rewrite N.shiftr_div_pow2.
  Search "/" "mod"
  repeat rewrite <- N.div2_div.
  Search ".&" ".|".
  Search N.modulo 2.
  repeat rewrite <- N.bit0_mod.
  Search N.mul 2.
  simpl (2^1).
  rewrite <- N.double_spec.
  destruct p,p0; simpl N.testbit.
  Search ".|" "+".
  do 2 destruct N.testbit.
  destruct N.testbit.
  rewrite <- N.double_spec.
  Search N.succ N.lt.
  2: { destruct w as [_ |[ | | ]]; try reflexivity. }
  destruct a,b; auto.
  simpl.
  rewrite N.lor_comm.
  simpl.
  reflexivity.
  Search N.modulo (_ mod (_ * _)).
  Search "^" N.succ.
  rewrite N.pow_succ_r'.
  Check N.mod_mul_r.
  Search "^" 0%N.
  repeat rewrite N.mod_mul_r; try apply N.pow_nonzero; try discriminate.
  replace 2 with (2^1); auto.
  Search "/" 2.
  repeat rewrite <- N.div2_div.
  Search "mod" 2.
  repeat rewrite <- N.bit0_mod.
  destruct p,p0; simpl N.div2; try fold (N.pos p .| N.pos p0).
  rewrite IHw.
  Search N.lor N.add.
  rewrite
  rewrite IHw.
  rewrite IHw.
  Search N "ind".
  destruct p,p0; simpl; auto.
  Search N.modulo N.mul.
  generalize dependent p0.
  generalize dependent p.
  destruct p,p0; simpl; auto.
  rewrite N.pow_succ_r'.
  simpl.
  repeat rewrite N.shiftr_shiftl_l; auto using N.le_refl.
  repeat rewrite N.shiftl_shiftl.
  Search "<<" ">>".
  Search "<<" N.lor.
  replace (c1 .| ((c1 << 8) mod 2^32)) with (
  destruct i.
  simpl.
  intros.
  repeat rewrite setmem_1.
  destruct (N.eq_decidable a1 a2); subst.
  Search N eq.
  compute.
  apply memfilled_mod.
  apply memfilled_split.
  unfold memfilled.
  repeat rewrite <- xplus_assoc.
  apply memfilled_split.
  repeat rewrite (N.add_comm x2).
  unfold memfilled.
  intros.
  subst.
  simpl (_ ⊕ 4).
  Search "setmem".
  apply N.
  f_equal.
  Search N.modulo 0%N N.sub.

  destruct PRE.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  intuition.
  repeat (discriminate + step); try rewrite H0,H,H1,H2,H3.
  rewrite H.
  do 5 econstructor.
  intuition.
  Locate "⊖".
  (* group operations? *)
  rewrite H4.
  assert (xplus_assoc : forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c).
  admit.
  repeat rewrite <- (xplus_assoc s).
  reflexivity.
  rewrite H6.
  admit.
  repeat rewrite <- H5 in *.
  replace (x3 ⊕ 1 ⊕ 1 ⊕ 1 ⊕ 1) with (x3 ⊕ 4).
  apply memfilled_mod.
  apply memfilled_split.
  repeat apply memfilled_update.
  assumption.
  unfold memfilled.
  intros.
  Check N.add_mod_idemp_l.
  rewrite <- (N.add_mod_idemp_l _ i).
  rewrite <- H4.
  (* the "hard" part of the proof of the final loop *)
  repeat rewrite setmem_1.
  (* i : N
     H7 : i < 4
     ============================
     (x4 [x2 := c] [x2 ⊕ 1 := c] [x2 ⊕ 1 ⊕ 1 := c] [x2 ⊕ 1 ⊕ 1 ⊕ 1 := c]) (x2 ⊕ i) = c
   *)
  admit.
  discriminate.
  admit.
  repeat rewrite (N.add_comm (2^32)).
  (* exits *)
  all: admit.
  Unshelve.
  all: admit.
Abort.

(* Pain points:
   - "mod 2^32" gets attached to everything
   - conditional instructions duplicate program proofs
   - "s [Ⓑv := a] v" should be a, but isn't easily turned into a
   - subtraction adds 2^32 (for modular arithmetic)
   - Ⓓ, Ⓜ frequently require existentials to extract
   - (related to the previous) Ⓓ, Ⓜ are secretly dynamic types
   - It's easy to construct "impossible states" (i.e. VaN 32 2^64)
 *)