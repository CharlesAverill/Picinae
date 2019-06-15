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

Definition memset_post_alt s c n (_:exit) (st:store) :=
  exists m, st V_MEM32 = Ⓜm /\ st R_R0 = Ⓓs /\ memfilled m s c n.

Definition memset_invs_alt (s:addr) (c:N) n (a:addr) (st:store) :=
  let r1 := vnum (st R_R1) in
  let r2 := vnum (st R_R2) in
  let r3 := vnum (st R_R3) in
  let m := vmem (st V_MEM32) in
  let common_inv := s ⊕ n = r3 ⊕ r2 /\ memfilled m s c (r3 ⊕ (2^32 - s)) in
  match a with
  | 0 => Some (vnum (st R_R0) = s /\ r2 = n /\ r1 mod (2^8) = c)
  (* | 0 => Some (exists m ci, *)
  (*                 st V_MEM32 = Ⓜm *)
  (*                 /\ st R_R0 = Ⓓs *)
  (*                 /\ st R_R1 = Ⓓci *)
  (*                 /\ st R_R2 = Ⓓn *)
  (*                 /\ c = ci mod (2^8)) *)
  (* | 4 => Some (st R_R2 = Ⓓn /\ common_inv) *)
  | 12 => Some (r1 mod (2^8) = c /\ common_inv)
  | 44 => Some (st R_R12 = st R_R1
                /\ r1 = memset_bytedup c
                /\ r3 mod (2^2) = 0
                /\ common_inv)
  | 84 => Some (vnum (st R_R1) mod (2^8) = c /\ common_inv)
  | 120 => Some (memset_post_alt s c n (Exit 120) st)
  | _ => None
  end.

Definition memset_invset_alt s c n :=
  invs (memset_invs_alt s c n) (memset_post_alt s c n).

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

Lemma memfilled_split' :
  forall m s c n1 n2,
    memfilled m s c n1
    -> memfilled m (s ⊕ n1) c n2
    -> memfilled m s c (n1 + n2).
  intros.
  unfold memfilled in *.
  intros.
  destruct (N.lt_ge_cases i n1); auto.
  rewrite <- (H0 (i - n1)).
  (* rewrite (N.add_comm n0). *)
  rewrite N.add_mod_idemp_l.
  rewrite <- N.add_assoc.
  rewrite (N.add_comm n1).
  rewrite N.sub_add; auto.
  discriminate.
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

Search 0%N N.modulo.

Search N.add 0%N.
Theorem xplusid' : forall n, n ⊕ 0 = n mod 2^32.
  intro n.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplusinv' : forall b c, b < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c mod 2^32.
  intros.
  rewrite (N.add_comm (2^32)).
  rewrite N.add_comm.
  destruct b.
  rewrite N.add_0_r.
  rewrite N.sub_0_r.
  rewrite mod_add_r; try discriminate.
  apply mod_same.
  discriminate.
  assert (N.pos p <= 2^32); auto using N.lt_le_incl.
  rewrite <- N.add_sub_assoc; auto.
  rewrite <- xplus_assoc.
  rewrite N.sub_add; auto.
  rewrite N.mod_same; try discriminate.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplusinv : forall b c, b < 2^32 -> c < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c.
  intros.
  rewrite xplusinv'; auto.
  apply N.mod_small.
  assumption.
Qed.

Theorem set_dword : forall m a v,
    m [Ⓓa := v]
    = m [Ⓑa := v mod 2^8]
        [Ⓑa+1 := v >> 8 mod 2^8]
        [Ⓑa+2 := v >> 16 mod 2^8]
        [Ⓑa+3 := v >> 24].
  intros.
  repeat rewrite setmem_1.
  simpl setmem.
  unfold setmem,setmem_little,Mb,ARMArch.mem_bits.
  repeat rewrite <- N.add_1_r.
  repeat rewrite <- N.add_assoc.
  simpl (1+_).
  repeat f_equal.
Qed.

Theorem set_dword_aligned : forall m a v,
    a < 2^32
    -> a mod 2^2 = 0
    -> m [Ⓓa := v]
       = m [Ⓑa := v mod 2^8]
           [Ⓑa⊕1 := v >> 8 mod 2^8]
           [Ⓑa⊕2 := v >> 16 mod 2^8]
           [Ⓑa⊕3 := v >> 24].
  intros.
  rewrite <- mod2_eq in H0.
  assert (a⊕1=a+1/\a⊕2=a+2/\a⊕3=a+3).
  repeat rewrite <- mod2_eq.
  destruct a; auto.
  destruct p; inversion H0; destruct p; inversion H0.
  simpl.
  fold (mod2 (N.pos p) 30).
  rewrite mod2_eq.
  rewrite N.mod_small.
  repeat split; reflexivity.
  Search (_*_<_*_).
  rewrite (N.mul_lt_mono_pos_l 4); auto.
  reflexivity.
  intuition.
  rewrite H2,H1,H4.
  apply set_dword.
Qed.

(* Theorem bin_rect : forall (P : N -> Type), *)
(*     P 0 -> (forall p, P (N.pos p) -> P (N.pos p~0) -> (forall p, P (N.pos p) -> P (N.pos p~1)) *)
(*     -> forall a, P a. *)
(*   induction a; auto. *)
(*   induction p; auto. *)
(*   specialize (X1 (N.pos p) IHp). *)
(*   rewrite <- N.double_spec in *. *)
(*   rewrite N.add_1_r in *. *)
(*   assumption. *)
(*   specialize (X0 (N.pos p) IHp). *)
(*   assumption. *)
(*   apply (X1 0). *)
(*   assumption. *)
(* Qed. *)

(* Search "recompose". *)

(* Search (_ mod (2^_)). *)

Theorem andshiftlzero' : forall a b w,
    (a mod 2^w) .& (b << w) = 0.
  destruct a,b,w; try rewrite N.mod_1_r;
    try rewrite N.shiftl_0_l,N.land_0_r; auto.
  rewrite <- mod2_eq.
  simpl.
  generalize dependent p.
  generalize dependent p0.
  induction p1 using Pos.peano_ind; simpl; auto.
  destruct p; reflexivity.
  destruct p; simpl; try rewrite Pos.pred_succ; rewrite Pos.iter_succ; auto;
    destruct (Pos.succ p1); auto; specialize (IHp1 p0 p);
      destruct posmod2; auto; simpl in *; rewrite IHp1; reflexivity.
Qed.

Theorem andshiftlzero : forall a b w,
    a < 2^w -> a .& (b << w) = 0.
  intros a b w.
  rewrite <- N.shiftl_1_l.
  destruct a,b,w; simpl; auto.
  intros.
  destruct p; discriminate.
  unfold N.lt.
  simpl.
  (* fold (Pos.lt p (Pos.iter xO 1%positive p1)). *)
  generalize dependent p0.
  generalize dependent p.
  induction p1 using Pos.peano_ind; simpl; auto.
  intros.
  destruct p; simpl; auto.
  destruct p; inversion H.
  destruct p; inversion H.
  intros a b.
  repeat rewrite Pos.iter_succ.
  intros.
  destruct a; simpl; auto; rewrite IHp1; auto.
  (* generalize dependent H. *)
  generalize dependent (Pos.iter xO 1%positive p1).
  intros.
  clear IHp1.
  fold (N.compare (N.pos a) (N.pos p)).
  fold (N.lt (N.pos a) (N.pos p)).
  rewrite N.mul_lt_mono_pos_l.
  repeat rewrite <- N.double_spec.
  simpl.
  eapply N.lt_trans.
  apply N.lt_succ_diag_r.
  simpl.
  auto.
  reflexivity.
Qed.

Theorem bytedup_spec : forall c,
    c < 2^8
    -> memset_bytedup c mod 2^8 = c
    /\ memset_bytedup c >> 8 mod 2^8 = c
    /\ memset_bytedup c >> 16 mod 2^8 = c
    /\ memset_bytedup c >> 24 = c.
  unfold memset_bytedup.
  all: replace 32 with (24+8); replace 24 with (16+8);
    replace 16 with (8+8); auto.
  intros.
  assert (Q : c + (c << 8) < 2^(8+8)).
  rewrite N.shiftl_mul_pow2.
  eapply N.lt_le_trans.
  apply N.add_lt_mono_r; eassumption.
  rewrite <- Nmult_Sn_m.
  rewrite N.pow_add_r.
  apply N.mul_le_mono_pos_r; try reflexivity.
  rewrite N.le_succ_l.
  apply H.
  replace ((c << 8) mod 2^(8+8+8+8)) with (c<<8).
  2: { symmetry. apply N.mod_small. eapply N.le_lt_trans. apply N.le_add_r.
       rewrite N.add_comm. eapply N.lt_trans; try eassumption. reflexivity. }
  replace ((c .| (c<<8) << (8+8)) mod 2^(8+8+8+8)) with (c .| (c<<8) << 8 << 8).
  2: { symmetry. rewrite N.shiftl_shiftl. apply N.mod_small.
       repeat rewrite N.shiftl_mul_pow2 in *. repeat rewrite N.pow_add_r.
       rewrite <- N.mul_assoc. apply N.mul_lt_mono_pos_r; try reflexivity.
       repeat rewrite <- N.pow_add_r. rewrite lor_plus; auto.
       rewrite <- N.shiftl_mul_pow2. apply andshiftlzero. assumption. }
  repeat (rewrite N.shiftl_lor + rewrite N.shiftr_lor
          + rewrite <- N.shiftl_shiftl + rewrite <- N.shiftr_shiftr
          + rewrite N.add_assoc + rewrite N.shiftr_shiftl_l,N.shiftl_0_r);
    try discriminate.
  replace (c >> 8) with 0; try rewrite shiftr_low_pow2; auto; try reflexivity.
  repeat rewrite N.shiftr_0_l.
  simpl.
  repeat rewrite <- N.shiftl_lor.
  simpl in Q.
  repeat rewrite lor_plus; auto using andshiftlzero.
  repeat rewrite N.shiftl_mul_pow2.
  repeat rewrite N.mod_add; try discriminate.
  repeat rewrite N.mod_small; try assumption.
  repeat split; reflexivity.
  rewrite N.shiftl_shiftl.
  apply andshiftlzero.
  assumption.
Qed.

Theorem memset_preserves_lr :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_LR = s R_LR.
  intros.
  eapply noassign_prog_same; try eassumption.
  prove_noassign.
Qed.

Theorem memfilled_succ : forall m s c n,
    memfilled m s c n -> memfilled (update m (s ⊕ n) c) s c (N.succ n).
  intros.
  unfold memfilled,update in *.
  intros.
  destruct iseq; auto.
  rewrite N.lt_succ_r in H0.
  rewrite N.le_lteq in H0.
  destruct H0; subst; auto.
  destruct n0.
  reflexivity.
Qed.

Theorem memset_welltyped: welltyped_prog armtypctx memset_arm.
Proof.
  Picinae_typecheck.
Qed.

Theorem memfilled_zero : forall m s c, memfilled m s c 0.
  unfold memfilled.
  destruct i; discriminate.
Qed.

Theorem tc_extract : forall tc reg st (H : models tc st),
    match tc reg with
    | Some (NumT w) => vnum (st reg) < 2^w
    | Some (MemT w) => welltyped_memory (vmem (st reg))
    | None => True
    end.
  unfold models.
  intros.
  specialize (H reg).
  destruct tc; auto.
  specialize (H _ eq_refl).
  inversion H; auto.
Qed.

Theorem memset_partial_correctness_alt:
  forall st lr s ci c n q st' x m
         (MDL0: models armtypctx st)
         (LR0: st R_LR = Ⓓlr) (MEM0: st V_MEM32 = Ⓜm)
         (R0: st R_R0 = Ⓓs) (R1: st R_R1 = Ⓓci) (R2: st R_R2 = Ⓓn)
         (C: c = ci mod 2^8)
         (RET: memset_arm st lr = None)
         (XP0: exec_prog fh memset_arm 0 st q st' x),
    trueif_inv (memset_invset_alt s c n memset_arm x st').
  intros.
  Search welltyped_prog.
  eapply prove_invs; [exact XP0|simpl;rewrite R0,R1,R2,C;tauto|].
  intros.
  assert (WTM : models armtypctx s1).
  1: { eapply preservation_exec_prog; try eassumption. apply memset_welltyped. }
  shelve_cases 32 PRE. Unshelve.
  all: intuition.
  Local Ltac step := time arm_step.
  do 3 step.
  subst.
  Check xplusinv.
  rewrite Hsv,Hsv0.
  intuition.
  Search (_+_-_).
  rewrite N.add_comm.
  Search (_-_+_).
  rewrite N.sub_add.
  apply memfilled_zero.
  Print hastyp_val.
  rewrite <- Hsv.
  apply N.lt_le_incl.
  apply (tc_extract armtypctx R_R0).
  assumption.
  rewrite H2.
  rewrite Hsv,Hsv0 in *.
  subst.
  intuition.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite N.add_sub.
  apply memfilled_zero.
  apply N.lt_le_incl.
  rewrite <- Hsv.
  apply (tc_extract armtypctx R_R0 _ WTM).

  4: { assert (PLR : s1 R_LR = st R_LR).
       eapply memset_preserves_lr. eassumption.
       step.
       apply NIHere.
       rewrite <- store_upd_eq; try assumption.
       unfold true_inv,invs.
       rewrite PLR,LR0 in Hsv.
       inversion Hsv; subst.
       replace (memset_arm s1 n0) with (@None (N*stmt)). (* ??? *)
       auto.
       }

  repeat (discriminate + step).
  subst.
  rewrite Hsv1 in H.
  simpl vnum in H.
  rewrite H.
  repeat split; try reflexivity.
  apply N.eqb_eq.
  assumption.
  rewrite Hsv,Hsv2 in H1.
  assumption.
  rewrite Hsv,Hsv0 in *.
  assumption.
  rewrite Hsv,Hsv0,Hsv1,Hsv2 in *.
  rewrite setmem_1.
  intuition.
  rewrite (N.add_comm (2^32)).
  simpl.
  rewrite (N.add_comm _ (2^32)).
  rewrite <- xplus_assoc.
  rewrite xplusinv.
  assumption.
  reflexivity.
  fold (vnum (Ⓓ n3)).
  rewrite <- Hsv2.
  apply (tc_extract armtypctx R_R2).
  assumption.
  Search "xplus".
  simpl vnum.
  rewrite (N.add_comm n0).
  rewrite <- xplus_assoc.
  Search memfilled.
  apply memfilled_mod.
  Search (1+_) N.succ.
  simpl vnum in H.
  rewrite H.
  rewrite N.add_comm.
  apply memfilled_split.
  Search memfilled.
  apply memfilled_update.
  assumption.
  rewrite N.add_comm.
  unfold memfilled.
  destruct i.
  rewrite N.add_0_r.
  rewrite <- xplus_assoc.
  rewrite N.sub_add.
  rewrite N.add_0_r.
  simpl.
  pose (tc_extract armtypctx R_R3 s1 WTM).
  simpl in y.
  rewrite N.mod_small; auto.
  Search update.
  intros.
  apply update_updated.
  rewrite Hsv in y.
  assumption.
  pose (tc_extract armtypctx R_R0 st MDL0).
  apply N.lt_le_incl.
  rewrite R0 in y.
  assumption.
  intros.
  destruct p; discriminate.

  repeat (discriminate + step).
  1-5: rewrite Hsv,Hsv0,Hsv1,Hsv2,Hsv3 in *.
  Search mod2.
  assert (X0 : forall n, (n ⊕ 4) mod 2^2 = n mod 2^2).
  Search (_ mod (_*_)).
  replace (2^32) with ((2^2) * (2^30)); try reflexivity.
  intros.
  rewrite N.mod_mul_r; try discriminate.
  rewrite <- N.add_mod_idemp_r; try discriminate.
  rewrite mod_mul_l; try discriminate.
  rewrite N.add_0_r.
  rewrite mod_same; try discriminate.
  repeat rewrite <- mod2_eq.
  destruct n5; try reflexivity.
  destruct p; try reflexivity; destruct p; reflexivity.
  assert (X1 : forall n, (n ⊕ 8) mod 2^2 = n mod 2^2).
  intros.
  rewrite (xplus_assoc _ 4 4).
  repeat rewrite X0.
  reflexivity.
  intuition.
  simpl.
  repeat rewrite X1.
  assumption.
  repeat rewrite (N.add_comm (2^32)).
  simpl.
  repeat rewrite (N.add_comm _ (2^32)).
  fold (2^32).
  repeat rewrite <- xplus_assoc.
  repeat rewrite xplusinv; try reflexivity;
    try apply N.mod_upper_bound; try discriminate; try assumption.
  pose (tc_extract armtypctx R_R2 _ WTM).
  rewrite Hsv in y.
  assumption.
  destruct (bytedup_spec (ci mod (2^8))).
  apply N.mod_upper_bound.
  discriminate.
  intuition.
  simpl (2^8) in *.
  unfold vnum,vmem in *.
  inversion H.
  subst.
  pose (tc_extract _ R_R3 _ WTM).
  rewrite Hsv0 in y.
  simpl in y.
  repeat rewrite set_dword_aligned; try apply N.mod_upper_bound; try discriminate;
    repeat rewrite X0; repeat rewrite X1; try assumption.
  simpl (2^8) in *.
  repeat rewrite H3.
  repeat rewrite H5.
  repeat rewrite H6.
  repeat rewrite H8.
  rewrite (N.add_comm _ (2^32-s)).
  repeat rewrite <- xplus_assoc.
  rewrite (xplus_assoc (_-_)).
  repeat rewrite setmem_1.
  apply memfilled_mod.
  apply memfilled_split'.
  repeat apply memfilled_update.
  rewrite N.add_comm.
  assumption.
  replace (s ⊕ (2 ^ 32 - s ⊕ n2)) with n2.
  repeat apply memfilled_succ.
  replace n2 with (n2 ⊕ 0) at 1.
  apply memfilled_succ.
  apply memfilled_zero.
  rewrite N.add_0_r.
  apply N.mod_small.
  assumption.
  rewrite xplus_assoc.
  rewrite (N.add_comm s).
  rewrite N.sub_add.
  rewrite N.add_0_l.
  symmetry.
  apply N.mod_small.
  assumption.
  pose (tc_extract _ R_R0 _ MDL0).
  rewrite R0 in y0.
  apply N.lt_le_incl.
  assumption.

  1-4: admit.

  repeat (discriminate + step).
  all: unfold vnum,vmem,memset_post_alt in *; rewrite Hsv,Hsv0,Hsv1,Hsv2 in *.
  intuition.
  repeat rewrite <- xplus_assoc.
  repeat rewrite xplusinv; try reflexivity;
    try apply N.mod_upper_bound; try discriminate.
  assumption.
  pose (tc_extract _ R_R2 _ WTM).
  rewrite Hsv in y.
  assumption.
  rewrite (N.add_comm _ (2^32 - s)).
  repeat rewrite xplus_assoc.
  repeat rewrite <- (xplus_assoc (_⊕n2)).
  rewrite (N.add_comm (2^32 - s)).
  apply memfilled_mod.
  rewrite H.
  apply memfilled_split'.
  repeat apply memfilled_update.
  assumption.
  replace n2 with (n2 ⊕ 0) at 1.
  replace (s ⊕ (n2 ⊕ (2 ^ 32 - s))) with n2.
  repeat rewrite <- xplus_assoc.
  repeat apply memfilled_succ.
  apply memfilled_zero.
  rewrite N.add_comm.
  rewrite <- xplus_assoc.
  rewrite N.sub_add.
  rewrite N.add_0_r.
  symmetry.
  apply N.mod_small.
  3: rewrite N.add_0_r; apply N.mod_small.
  1,3: pose (X := tc_extract _ R_R3 _ WTM); rewrite Hsv0 in X; assumption.
  apply N.lt_le_incl.
  pose (tc_extract _ R_R0 _ MDL0).
  rewrite R0 in y.
  assumption.
  all: econstructor; intuition; repeat rewrite update_frame; try discriminate.
  all: try (erewrite memset_ret; eassumption).
  all: repeat rewrite setmem_1; try rewrite H.
  all: replace n with ((n2 ⊕ (2 ^ 32 - s)) ⊕ n0).
  all: try (apply memfilled_mod; apply memfilled_split;
            [ repeat apply memfilled_update; assumption| ]).
  all: try replace (s + (n2 ⊕ (2 ^ 32 - s))) with n2.
  1: replace n0 with 3.
  6: replace n0 with 2.
  11: replace n0 with 1.
  16: replace n0 with 0.
  1,6,11: repeat rewrite <- xplus_assoc;
    replace n2 with (n2 ⊕ 0) at 1; repeat apply memfilled_succ.
  all: try apply memfilled_zero.
  all: admit.
Abort.

Definition xcomp n := 2^32 - (n mod (2^32)).
Definition xminus n m := n ⊕ (xcomp m).

Theorem xminus_zero : forall n, xminus n n = 0.
  unfold xminus,xcomp.
  intros.
  rewrite <- N.add_mod_idemp_l; try discriminate.
  rewrite N.add_comm.
  rewrite N.sub_add; auto.
  apply N.lt_le_incl.
  apply N.mod_upper_bound.
  discriminate.
Qed.
  rewrite N.add_sub_swap.
  rewrite N.add_comm.
  N.sub N.add.

  repeat apply memfilled_succ.
  all: destruct n0; try discriminate.
  all: do 2 try destruct p; try discriminate.
  all: repeat (destruct p; try discriminate).
  4: { assumption.
  Theorem memfilled_succ' : forall m s c n,
    memfilled m s c n -> memfilled (update m (s ⊕ n) c) s c (N.succ n).
  apply memfilled_succ.
  all: pose 
  Search update.
  replace (N.add_comm 
  all: unfold vnum,vmem,memset_post_alt.

Theorem memset_partial_correctness:
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
  repeat rewrite <- xplus_assoc.
  assert (8 < 2^8); try reflexivity.
  do 3 try rewrite xplusinv;
    try reflexivity; try apply N.mod_upper_bound; try discriminate.
  rewrite xplusinv'; try reflexivity.
  rewrite xplus_assoc.
  rewrite <- H6.
  rewrite N.add_mod_idemp_r; try assumption.
  discriminate.
  repeat rewrite <- xplus_assoc.
  simpl N.add.
  repeat rewrite N.mod_same.
  Search N.modulo N.add.
  repeat rewrite N.add_mod_idemp_r; try discriminate.
  Locate "[".
  Import ARMNotations.
  Locate "[".
  Check getmem_1.
  Locate "[Ⓑ".
  assert (set_dword : forall m a v,
             m [Ⓓa := v]
             = m [Ⓑa := v mod 2^8]
                 [Ⓑa+1 := v >> 8 mod 2^8]
                 [Ⓑa+2 := v >> 16 mod 2^8]
                 [Ⓑa+3 := v >> 24]).
  intros.
  repeat rewrite setmem_1.
  simpl setmem.
  unfold setmem,setmem_little,Mb,ARMArch.mem_bits.
  Search N.succ N.add.
  repeat rewrite <- N.add_1_r.
  repeat rewrite <- N.add_assoc.
  simpl (1+_).
  repeat f_equal.
  repeat rewrite set_dword; repeat rewrite setmem_1.
  rewrite <- H1.
  rewrite H3.
  simpl vnum.
  (* These two lemmas are false, I need to replace them with alignment lemmas *)
  assert (BAD : forall a b, a + b = (a + b) mod 2^32).
  admit.
  assert (BAD2 : forall a b c, (a ⊕ b) + c = (a + b + c) mod 2^32).
  intros.
  rewrite BAD.
  apply N.add_mod_idemp_l.
  discriminate.
  repeat rewrite BAD2.
  repeat rewrite <- N.add_assoc.
  simpl N.add.
  rewrite (BAD x2 1).
  rewrite (BAD x2 2).
  rewrite (BAD x2 3).
  clear BAD.
  clear BAD2.
  assert (bytedup_spec : forall c,
             c < 2^8 ->
             memset_bytedup c mod 2^8 = c /\
             memset_bytedup c >> 8 mod 2^8 = c /\
             memset_bytedup c >> 16 mod 2^8 = c /\
             memset_bytedup c >> 24 = c).
  admit.
  rewrite H in H3.
  inversion H3.
  destruct (bytedup_spec c).
  rewrite H7.
  apply N.mod_upper_bound.
  discriminate.
  destruct H12.
  destruct H13.
  rewrite H9,H12,H13,H14.
  apply memfilled_mod.
  apply memfilled_split.
  Search memfilled.
  repeat apply memfilled_update.
  assumption.
  Search memfilled.
  rewrite H6.
  repeat rewrite N.add_mod_idemp_l; try discriminate.
  assert (memfilled_succ : forall m s c n,
             memfilled m s c n -> memfilled (update m (s ⊕ n) c) s c (N.succ n)).
  intros.
  unfold memfilled.
  unfold memfilled in H15.
  Search N.lt N.succ.
  Search N.lt "dec".
  intros.
  unfold update.
  destruct iseq; auto.
  rewrite N.lt_succ_r in H16.
  rewrite N.le_lteq in H16.
  destruct H16; auto.
  rewrite H16 in n2.
  destruct n2.
  reflexivity.
  rewrite <- (N.add_0_r (s+x3)) at 1.
  repeat apply memfilled_succ.
  unfold memfilled.
  destruct i; discriminate.
  1-3: admit.
  do 5 econstructor.
  intuition.
  exact H6.
  rewrite H8.
  repeat f_equal.
  Search N.leb.
  destruct (N.leb_spec 8 x1); try discriminate.
  destruct x1; auto.
  compute in H9.
  do 4 (destruct p; auto); discriminate.
  assumption.
  assert (RLR_pres : s1 R_LR = st R_LR).
  eapply noassign_prog_same; try apply XP.
  prove_noassign.
  destruct PRE.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  intuition.
  repeat (discriminate + step).
  intuition.
  repeat rewrite setmem_1.
  do 5 econstructor.
  intuition.
  rewrite H4.
  repeat rewrite <- xplus_assoc.
  simpl (1+_).
  rewrite (N.add_mod_idemp_r x3); try discriminate.
  rewrite N.add_mod_idemp_r; try discriminate.
  reflexivity.
  repeat rewrite <- xplus_assoc.
  do 3 try rewrite xplusinv;
    try reflexivity; try apply N.mod_upper_bound; try discriminate.
  rewrite xplusinv'; try reflexivity.
  rewrite N.add_mod_idemp_r; try discriminate.
  assumption.
  assert (memfilled_succ : forall m s c n,
             memfilled m s c n -> memfilled (update m (s ⊕ n) c) s c (N.succ n)).
  admit.
  rewrite <- H5.
  apply memfilled_split.
  repeat apply memfilled_update.
  assumption.
  rewrite H4.
  repeat rewrite <- xplus_assoc.
  simpl (1⊕_).
  repeat rewrite (N.add_mod_idemp_r x3); try discriminate.
  repeat rewrite N.add_mod_idemp_r; try discriminate.
  rewrite <- (N.add_0_r x3) at 1.
  repeat rewrite N.add_assoc.
  repeat apply memfilled_succ.
  unfold memfilled.
  destruct i; discriminate.
  all: rewrite RLR_pres; rewrite LR0; simpl (vnum (Ⓓ _)).
  Print nextinv.
  Print invs.
  apply NIHere.
  red.
  red.
  red.
  destruct lr.
  discriminate.
  destruct p.
  3: { red. econstructor. intuition. repeat rewrite setmem_1.
       assert (3 <= x1).
       destruct x1; try discriminate.
       compute.
       destruct p; try discriminate; destruct p; try discriminate.
       Search N.lt N.le.
       rewrite N.lt_eq_cases in H7.
       destruct H7.
       Search N.add N.sub.
       Search N.leb.
       destruct (N.leb_spec 1 x1); try discriminate.
       destruct (N.leb_spec 1 (2 ^ 32 + x1 ⊖ 1)); try discriminate.
       destruct (N.leb_spec 1 (2 ^ 32 + (2 ^ 32 + x1 ⊖ 1) ⊖ 1)); try discriminate.
       destruct (N.leb_spec 1 (2 ^ 32 + (2 ^ 32 + (2 ^ 32 + x1 ⊖ 1) ⊖ 1) ⊖ 1));
         try discriminate.
       Search "xplus".
       Search N.add N.sub.
       repeat rewrite <- (N.add_sub_assoc (2^32)) in H12; try assumption.
       Search N.leb.
       destruct (N.leb_spec 1 x1).
       do 3 rewrite <- (N.add_sub_assoc (2^32)) in BC6.
       Search x1
       destruct p; auto.
       compute.
       destruct (N.leb_spec 1 x1) in BC6.
       assert (x1 = 3).
       destruct x1; try discriminate.
       f_equal.
       destruct p; try discriminate.
       f_equal.
       destruct p; auto; try discriminate.
       destruct x1.
       assert 
       discriminate.
       destruct p; try discriminate.
       destruct p; try discriminate.
       destruct p; try discriminate.
  simpl in BC6.
  red.
  discriminate.
  econstructor.
  econstructor.
  discriminate.
  split.
  Search update.
  do 3 (rewrite update_frame; try discriminate).
  discriminate.
  discriminate.
  intuition.
  unfold update.
  simpl (iseq).
  unfold vareq.
  destruct ARMArch.Var.eq_dec.
  inversion e.
  destruct
  unfold ARMArch.Var.eq_dec.
  red.
  red.
  simpl.
  red.
  rewrite RLR_pres.
  red.
  unfold true_inv.
  simpl.
  Print nextinv.
  apply NIHere.
  Print true_inv.
  red.
  red.
  red.
  red.
  red.
  unfold 
  repeat rewrite xplus_assoc.
  rewrite <- N.add_assoc at 1.
  repeat apply memfilled_succ.
  rewrite xplusinv.
  Set Printing All.
  rewrite mod_same.
  repeat rewrite setmem_1.
  auto.
  assert (memfilled_bytedup : forall m s c,
             m [Ⓓs := memset_bytedup c] s c 4 =
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