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

Definition xcomp n := ((2^32 - (n mod (2^32))) mod (2^32)).
Definition xminus n m := n ⊕ (xcomp m).

Theorem xminus_zero n : xminus n n = 0.
  unfold xminus,xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite <- N.add_mod_idemp_l by discriminate.
  rewrite N.add_comm.
  rewrite N.sub_add by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  reflexivity.
Qed.

Theorem xminus_alt' n m : m < 2^32 -> 2 ^ 32 + n ⊖ m = n mod (2^32) ⊕ (xcomp m).
  intro H.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc; auto using N.lt_le_incl.
  unfold xcomp.
  rewrite (N.mod_small m) by assumption.
  rewrite N.add_mod_idemp_l by discriminate.
  rewrite N.add_mod_idemp_r by discriminate.
  reflexivity.
Qed.

Theorem xminus_alt n m : n < 2^32 -> m < 2^32 -> 2 ^ 32 + n ⊖ m = n ⊕ (xcomp m).
  intros H1 H2.
  rewrite xminus_alt' by assumption.
  rewrite (N.mod_small n) by assumption.
  reflexivity.
Qed.

Theorem mod_n_n (n d:N) : d ≠ 0 -> (n mod d) mod d = n mod d.
  intro H.
  apply N.mod_small.
  apply N.mod_upper_bound.
  exact H.
Qed.

Theorem xcomp_mod n : xcomp n mod (2^32) = xcomp n.
  unfold xcomp.
  apply mod_n_n.
  discriminate.
Qed.

Theorem xcomp_mod_in n : xcomp (n mod (2^32)) = xcomp n.
  unfold xcomp.
  rewrite mod_n_n by discriminate.
  reflexivity.
Qed.

Theorem xplus_minus n m : m < n -> (n-m) mod (2^32) = xminus n m.
  intros.
  assert (Q : m / (2^32) <= n / (2^32)).
  apply N.div_le_mono; try discriminate.
  apply N.lt_le_incl.
  assumption.
  Search N.add N.sub N.le.
  unfold xminus,xcomp.
  Search N.add N.sub.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc by
      (apply N.lt_le_incl; eapply N.le_lt_trans; try exact H;
       apply N.mod_le; discriminate).
  rewrite mod_add_l by discriminate.
  rewrite (N.div_mod m (2^32)) at 1 by discriminate.
  rewrite N.sub_add_distr.
  rewrite (N.div_mod n (2^32)) by discriminate.
  rewrite N.add_sub_swap by (apply N.mul_le_mono_l; exact Q).
  rewrite <- N.mul_sub_distr_l.
  rewrite N.lt_eq_cases in Q.
  destruct Q as [Q|Q]; [|rewrite Q].
  rewrite <- N.add_0_l in Q at 1.
  rewrite N.lt_add_lt_sub_r in Q.
  destruct (n / 2^32); try discriminate.
  destruct (_ - m/_); try discriminate.
  rewrite <- (N.succ_pos_pred p0).
  rewrite <- (N.succ_pos_pred p).
  repeat rewrite N.mul_succ_r.
  repeat rewrite <- N.add_assoc.
  repeat rewrite (N.add_comm (2^32)).
  repeat rewrite <- (N.add_sub_assoc (_*_)) by
    (eapply N.le_trans; [apply N.lt_le_incl,N.mod_upper_bound; discriminate|
                         rewrite N.add_comm; apply N.le_add_r]).
  repeat rewrite mod_add_mul_ll by discriminate.
  reflexivity.
  rewrite N.sub_diag.
  rewrite N.add_0_l.
  rewrite <- N.add_sub_assoc; [symmetry; apply mod_add_mul_ll; discriminate|].
  rewrite (N.div_mod' n (2^32)) in H.
  rewrite (N.div_mod' m (2^32)) in H.
  rewrite Q in H.
  apply N.lt_le_incl.
  eapply N.add_lt_mono_l.
  exact H.
Qed.

Theorem xcomp_plus_dist' n m : xcomp n ⊕ xcomp m = xcomp (n+m).
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_mod_idemp_l by discriminate.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite N.add_comm.
  rewrite N.add_sub_assoc by
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate).
  rewrite <- N.sub_add_distr.
  Search N.add N.lt.
  rewrite xplus_minus by
      (apply N.add_lt_mono; apply N.mod_upper_bound; discriminate).
  unfold xminus.
  rewrite <- N.add_mod_idemp_l at 1 by discriminate.
  rewrite N.add_0_l.
  unfold xcomp.
  rewrite N.add_mod_idemp_r by discriminate.
  rewrite N.add_mod_idemp_l by discriminate.
  apply mod_n_n.
  discriminate.
Qed.

Theorem xcomp_plus_dist n m : xcomp n ⊕ xcomp m = xcomp (n⊕m).
  rewrite xcomp_plus_dist'.
  unfold xcomp.
  rewrite mod_n_n by discriminate.
  reflexivity.
Qed.

Theorem xplus_id_l' n : n ⊕ 0 = n mod 2^32.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Theorem xplus_id_l n : n < 2^32 -> n ⊕ 0 = n.
  rewrite N.add_0_r.
  apply N.mod_small.
Qed.

Theorem xplus_id_r' n : 0 ⊕ n = n mod 2^32.
  reflexivity.
Qed.

Theorem xplus_id_r n : n < 2^32 -> 0 ⊕ n = n.
  apply N.mod_small.
Qed.

Theorem xplus_comm n m : n ⊕ m = m ⊕ n.
  rewrite N.add_comm.
  reflexivity.
Qed.

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
  let common_inv := s ⊕ n = r3 ⊕ r2 /\ memfilled m s c (xcomp s ⊕ r3) in
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
  | 120 => Some (memfilled m s c n)
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
  apply mod_n_n.
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

Theorem memfilled_one' m s c : memfilled (update m (s mod (2^32)) c) s c 1.
  unfold memfilled.
  intros i H.
  destruct i; try (rewrite N.add_0_r; apply update_updated).
  destruct p; inversion H.
Qed.

Theorem memfilled_one m s c : s < 2^32 -> memfilled (update m s c) s c 1.
  intros.
  erewrite <- (N.mod_small s (2^32)) at 1 by exact H.
  apply memfilled_one'.
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
  Check tc_extract.
  assert (TCX := fun r => tc_extract _ r _ WTM).
  assert (TCXR0 := tc_extract _ R_R0 _ MDL0).
  assert (TCXR1 := TCX R_R1).
  assert (TCXR2 := TCX R_R2).
  assert (TCXR3 := TCX R_R3).
  simpl in *.
  rewrite R0 in TCXR0.
  subst.
  shelve_cases 32 PRE. Unshelve.
  all: intuition. (* extract precondition hypotheses *)
  subst.
  Local Ltac step := time arm_step.
  do 3 step.
  1-2: rewrite H2.
  1-2: unfold vnum,vmem in *; rewrite Hsv,Hsv0 in *; intuition.
  1-2: rewrite N.add_comm; fold (xminus n n); rewrite (xminus_zero n).
  1-2: apply memfilled_zero.

  4: { assert (PLR : s1 R_LR = st R_LR).
       eapply memset_preserves_lr. eassumption.
       step.
       apply NIHere.
       rewrite <- store_upd_eq; try assumption.
       unfold true_inv,invs.
       rewrite PLR,LR0 in Hsv.
       inversion Hsv; subst.
       replace (memset_arm s1 n0) with (@None (N*stmt)). (* ??? *)
       unfold memset_post_alt.
       exists (vmem (s1 (V_MEM32))).
       erewrite memset_ret by eassumption.
       intuition.
       specialize (WTM V_MEM32 _ eq_refl).
       inversion WTM.
       reflexivity. }

  repeat (discriminate + step).
  1-2: unfold vnum,vmem in *.
  1-2: rewrite Hsv,Hsv0,Hsv1,Hsv2,H in *.
  intuition.
  apply N.eqb_eq.
  assumption.
  intuition.
  rewrite <- xplus_assoc.
  rewrite xplusinv; [assumption|reflexivity|assumption].
  rewrite xplus_assoc.
  Set Nested Proofs Allowed.
  Theorem memfilled_xcomp m s c skip n :
    memfilled m s c (xcomp s ⊕ skip)
    -> memfilled m skip c n
    -> memfilled m s c (xcomp s ⊕ skip ⊕ n).
    intros H H0.
    apply memfilled_mod.
    apply memfilled_split'; [exact H|].
    rewrite xplus_assoc.
    fold (xminus s s).
    rewrite xminus_zero.
    rewrite N.add_0_l.
    unfold memfilled in *.
    intro.
    rewrite N.add_mod_idemp_l by discriminate.
    apply H0.
  Qed.
  apply memfilled_xcomp; [apply memfilled_update; assumption|].
  apply memfilled_one.
  assumption.

  destruct (bytedup_spec (ci mod N.pos (2 ^ 8)));
    [apply N.mod_upper_bound; discriminate|].
  intuition.
  repeat (discriminate + step).
  1-5: unfold vnum,vmem in *.
  1-5: rewrite Hsv,Hsv0,Hsv1,Hsv2,Hsv3 in *.
  1-5: inversion H; subst.
  1-5: repeat rewrite <- xplus_assoc.
  repeat rewrite xplusinv by (reflexivity + apply N.mod_upper_bound; discriminate).
  intuition.
  Theorem minus_n_mod_n n m : 0 < m -> m < n -> (n - m) mod m = n mod m.
    intros H0 H1.
    rewrite (N.div_mod' n m) at 1.
    assert (Q : m <= m * (n / m)).
    Search "/" "<=".
    rewrite <- N.mul_1_r at 1.
    Search (_*_ <= _*_).
    apply N.mul_le_mono_pos_l; [exact H0|].
    Search (_ <= _/_).
    destruct m; inversion H0.
    apply N.div_le_lower_bound; [discriminate|].
    rewrite N.mul_1_r.
    apply N.lt_le_incl.
    exact H1.
    rewrite N.add_sub_swap by exact Q.
    Search N.mul N.pred.
    rewrite <- N.mul_pred_r.
    Search "*" "mod".
    destruct m; inversion H0.
    rewrite mod_add_mul_ll by discriminate.
    apply mod_n_n.
    discriminate.
  Qed.
  simpl (8 ⊕ _).
  repeat rewrite <- mod2_eq.
  rewrite <- mod2_eq in H0.
  destruct n2; auto.
  destruct p; try destruct p; inversion H0.
  simpl.
  destruct posmod2; reflexivity.
  rewrite xminus_alt by assumption + reflexivity.
  rewrite (xplus_comm 8).
  rewrite <- xplus_assoc.
  rewrite (xplus_comm _ 8).
  fold (xminus 8 8).
  rewrite xminus_zero.
  rewrite N.add_0_r.
  rewrite (N.mod_small n0); assumption.
  2-4: repeat rewrite xminus_alt by assumption + reflexivity.
  2-5: rewrite minus_n_mod_n by
      reflexivity + (eapply N.lt_le_trans; [|apply N.le_add_r]; reflexivity).
  2-5:
    repeat
      match goal with
        [ _ : context [ ?x <=? ?y ] |- _] => destruct (N.leb_spec x y)
      end; try discriminate.
  2-4: intuition; [shelve|].
  5: intuition; shelve.
  (* 2-4: repeat rewrite xminus_alt. *)
  (* 2-4: rewrite minus_n_mod_n. *)
  (* 2-4: repeat rewrite xplusinv. *)
  (* 2: { intuition. *)
  (* 2-4: intuition. *)
  (* 2-4: intuition; [admit|]. *)
  (* 5: intuition; admit. *)
  1-4: rewrite (xplus_assoc (xcomp s)).
  1-4: repeat rewrite set_dword_aligned by
      (apply N.mod_upper_bound; discriminate) +
      (rewrite dblmod_r by discriminate;
       rewrite <- N.add_mod_idemp_r by discriminate;
       rewrite N.add_0_r;
       assumption) + assumption.
  1-4: repeat rewrite setmem_1.
  1-4: rewrite H3,H6,H5,H8.
  Search memfilled.
  1-4: apply memfilled_xcomp; [repeat apply memfilled_update; assumption|].
  1-4: repeat rewrite <- xplus_assoc.
  1-4: repeat apply memfilled_succ.
  1-4: apply memfilled_one; assumption.

  assert (Q : (xcomp s ⊕ vnum (s1 R_R3) ⊕ vnum (s1 R_R2)) = n).
  rewrite <- xplus_assoc. rewrite <- H1. rewrite xplus_assoc.
  rewrite (xplus_comm _ s). fold (xminus s s). rewrite xminus_zero.
  rewrite N.add_0_l. apply N.mod_small. pose (Q := tc_extract _ R_R2 _ MDL0).
  rewrite R2 in Q. exact Q.
  subst.
  repeat (discriminate + step).
  all: unfold vnum,vmem,memset_post_alt in *; rewrite Hsv,Hsv0,Hsv1,Hsv2 in *.
  intuition.
  repeat rewrite <- xplus_assoc.
  rewrite xplus_assoc.
  fold (xminus s s).
  rewrite xminus_zero.
  rewrite N.add_0_l.
  rewrite mod_n_n by discriminate.
  repeat rewrite xplusinv; try reflexivity;
    try apply N.mod_upper_bound; try discriminate; assumption.
  repeat rewrite (xplus_assoc (xcomp s)).
  repeat rewrite <- (xplus_assoc (xcomp s ⊕ n0)).
  1-4: rewrite H.
  1-5: apply memfilled_xcomp; [repeat apply memfilled_update; assumption|].
  1-5: repeat rewrite <- xplus_assoc.
  repeat apply memfilled_succ.
  apply memfilled_one.
  assumption.
  all: repeat
         match goal with
           [ _ : context [ ?x <=? ?y ] |- _] => destruct (N.leb_spec x y)
         end; try discriminate.
  all: rewrite N.lt_1_r in *.
  4: subst; apply memfilled_zero.
  3: replace n with 1; [apply memfilled_one; assumption|].
  2: replace n with 2; [apply memfilled_succ,memfilled_one; assumption|].
  1: replace n with 3;
    [apply memfilled_succ,memfilled_succ,memfilled_one; assumption|].
  all: rewrite (xminus_alt n) in H0 by assumption + reflexivity.
  all: repeat rewrite xminus_alt in H0 by
      (apply N.mod_upper_bound; discriminate) + reflexivity.
  Theorem xcomp_comp n : n < 2^32 -> xcomp (xcomp n) = n.
    intro H.
    rewrite <- (xplus_id_l n) at 2 by assumption.
    rewrite <- (xminus_zero (xcomp n)).
    unfold xminus.
    rewrite xplus_assoc.
    fold (xminus n n).
    rewrite xminus_zero.
    rewrite xplus_id_r by (apply N.mod_upper_bound; discriminate).
    reflexivity.
  Qed.

  Theorem xeq_xplus_r n m p :
    n < 2^32 -> p < 2^32 -> n ⊕ m = p <-> n = p ⊕ xcomp m.
    intros.
    split; intros; subst; rewrite <- xplus_assoc; [|rewrite (N.add_comm _ m)];
      fold (xminus m m); rewrite xminus_zero; rewrite xplus_id_l by assumption;
        reflexivity.
  Qed.

  Theorem xeq_xplus_l n m p :
    m < 2^32 -> p < 2^32 -> n ⊕ m = p <-> m = xcomp n ⊕ p.
    intros.
    rewrite xplus_comm.
    rewrite xeq_xplus_r by assumption.
    rewrite xplus_comm.
    reflexivity.
  Qed.

  Theorem xeq_xcomp_r n m p :
    n < 2^32 -> p < 2^32 -> n ⊕ xcomp m = p <-> n = p ⊕ m.
    intros.
    rewrite xeq_xplus_r by assumption.
    Search xcomp N.modulo.
    rewrite <- (xcomp_mod_in m).
    rewrite xcomp_comp by (apply N.mod_upper_bound; discriminate).
    rewrite N.add_mod_idemp_r by discriminate.
    reflexivity.
  Qed.

  Theorem xeq_xcomp_l n m p :
    m < 2^32 -> p < 2^32 -> xcomp n ⊕ m = p <-> m = n ⊕ p.
    intros.
    rewrite xplus_comm.
    rewrite xeq_xcomp_r by assumption.
    rewrite xplus_comm.
    reflexivity.
  Qed.

  (* all: repeat match goal with H : _=0 |- _ => symmetry in H end. *)
  all: repeat rewrite xeq_xcomp_r in * by
      (reflexivity + assumption + apply N.mod_upper_bound; discriminate).
  all: subst.
  all: reflexivity.
  Unshelve.

  all: rewrite H2.
  all: do 2 f_equal.
  all: repeat rewrite xminus_alt in * by
      (reflexivity + assumption + apply N.mod_upper_bound; discriminate).
  Search "xplus".
  Search "xplus".
  Theorem xplus_minus' n m : m <= n → n ⊖ m = xminus n m.
    intro H.
    rewrite N.lt_eq_cases in H.
    destruct H; [apply xplus_minus; assumption|].
    subst.
    rewrite xminus_zero.
    rewrite N.sub_diag.
    reflexivity.
  Qed.

  Theorem xplus_minus'' n m :
    n < 2^32 -> m <= n → n - m = n ⊕ xcomp m.
    intros H0 H1.
    unfold xcomp.
    rewrite N.add_mod_idemp_r by discriminate.
    rewrite N.add_sub_assoc by
        (apply N.lt_le_incl,N.mod_upper_bound; discriminate).
    rewrite N.add_comm.
    assert (H2 : m < 2^32) by (eapply N.le_lt_trans; eassumption).
    rewrite (N.mod_small m) by (eapply N.le_lt_trans; eassumption).
    rewrite <- N.add_sub_assoc by assumption.
    rewrite mod_add_l by discriminate.
    symmetry.
    apply N.mod_small.
    eapply N.le_lt_trans ; [|exact H0].
    apply N.le_sub_l.
  Qed.

  Theorem xlt_minus n m p :
    n < 2^32 -> n ⊕ xcomp m < p -> n < p + m.
    intros H1 H2.
    destruct (N.lt_ge_cases n m) as [H3|H3].
    eapply N.lt_le_trans; [exact H3|].
    rewrite N.add_comm.
    apply N.le_add_r.
    rewrite <- xplus_minus'' in H2 by assumption.
    Search N.add N.sub N.lt.
    apply N.lt_sub_lt_add_r.
    assumption.
  Qed.

  all: repeat (apply xlt_minus in H1;
               (assumption + reflexivity +
                (try apply N.mod_upper_bound; try discriminate))).
  all: replace (2^32) with (2^29 * 2^3) by reflexivity.
  Search N.add N.modulo N.mul.
  all: rewrite mod_add_mul_lr by discriminate.
  all: replace (2^29 * 2^3) with (2^32) by reflexivity.
  Search "xplus".
  Search N.succ N.lt.
  (* Theorem xge_minus n m p : *)
  (*   p < 2^32 -> n <= m ⊕ xcomp p -> n + p <= m. *)
  (*   intros H1 H2. *)
  (*   destruct (N.lt_ge_cases m p) as [H3|H3]. *)
  (*   eapply N.lt_le_trans; [exact H3|]. *)
  (*   rewrite N.add_comm. *)
  (*   apply N.le_add_r. *)
  (*   rewrite <- xplus_minus'' in H2 by assumption. *)
  (*   Search N.add N.sub N.lt. *)
  (*   apply N.lt_sub_lt_add_r. *)
  (*   assumption. *)
  (* Qed. *)

  Check N.lt_le_pred.
  Search xcomp.
  match goal with
    [H1 : ?x <= ?y |- _] => idtac
  end.
  Check xplus_minus''.
  all: fold (2^32) in *.
  (* rewrite <- (xplus_minus'' n0 8 TCXR2 H10) in H9. *)
  Check xplus_minus''.
  match goal with
    [H1 : ?m <= ?n, H2 : ?n < 2^32, H3 : _ <= ?n ⊕ xcomp ?m |- _] =>
    idtac n m H1 H2 H3
  end.
  Theorem sub_eq_r n m p : n <= m -> p <= m - n <-> p + n <= m.
    intro H0.
    rewrite N.add_le_mono_r.
    rewrite N.sub_add by exact H0.
    reflexivity.
  Qed.

  Theorem xminus_eq_r n m p :
    n < 2^32 -> m <= n -> p <= n ⊕ xcomp m <-> p + m <= n.
    intros H0 H1.
    rewrite <- xplus_minus'' by assumption.
    apply sub_eq_r.
    assumption.
  Qed.

  (* rewrite (xminus_eq_r n0 8 8 TCXR2 H10) in H9. *)
  all: repeat rewrite <- xplus_assoc in *.
  Search xcomp.
  all: repeat rewrite xcomp_plus_dist' in *.
  match goal with
    [H1 : ?m <= ?n, H2 : ?n < 2^32, H3 : ?p <= ?n ⊕ xcomp ?m |- _] =>
    idtac n m p H2 H1 H3
  end.
  all: repeat match goal with
                [H1 : ?m <= ?n, H2 : ?n < 2^32 |- _] =>
                rewrite (xminus_eq_r n m) in * by exact H2 + exact H1
              end.

  all: repeat match goal with H : _ < 2^32 |- _ => clear H end.
  all: simpl (_<_) in *.
  all: simpl (_<=_) in *.
  all: repeat
         match goal with
           H : _ < N.pos _ |- _ =>
           apply N.lt_le_pred in H; rewrite N.le_lteq in H; destruct H;
             [simpl in H|rewrite H; reflexivity]
         end.
  4: edestruct N.nlt_0_r; eassumption.
  all: rewrite N.le_ngt in *.
  all: tauto.
Qed.

(* Pain points:
   - "mod 2^32" gets attached to everything
   - conditional instructions duplicate program proofs
   - "s [Ⓑv := a] v" should be a, but isn't easily turned into a
   - subtraction adds 2^32 (for modular arithmetic)
   - Ⓓ, Ⓜ frequently require existentials to extract
   - (related to the previous) Ⓓ, Ⓜ are secretly dynamic types
   - It's easy to construct "impossible states" (i.e. VaN 32 2^64)
 *)