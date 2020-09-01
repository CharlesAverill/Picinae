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

(* CATEGORY: basic modular arithmetic *)
Definition xcomp n := ((2^32 - (n mod (2^32))) mod (2^32)).
Notation "⊖ x" := (xcomp x) (at level 20).
Notation "x _⊖_ y" := (x ⊕ ⊖y) (at level 50, left associativity).

Theorem xminus_zero n : n _⊖_ n = 0.
  unfold xcomp. (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite <- N.add_mod_idemp_l by discriminate. (* C:binarith *)
  rewrite N.add_comm. (* C:binarith *)
  rewrite N.sub_add by (* C:binarith *)
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate). (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xminus_alt' n m : m < 2^32 -> 2 ^ 32 + n ⊖ m = n mod (2^32) _⊖_ m.
  intro H. (* C:regular *)
  rewrite N.add_comm. (* C:binarith *)
  rewrite <- N.add_sub_assoc; auto using N.lt_le_incl. (* C:binarith *)
  unfold xcomp. (* C:binarith *)
  rewrite (N.mod_small m) by assumption. (* C:binarith *)
  rewrite N.add_mod_idemp_l by discriminate. (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xminus_alt n m : n < 2^32 -> m < 2^32 -> 2 ^ 32 + n ⊖ m = n _⊖_ m.
  intros H1 H2. (* C:regular *)
  rewrite xminus_alt' by assumption. (* C:binalg *)
  rewrite (N.mod_small n) by assumption. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem mod_n_n (n d:N) : d ≠ 0 -> (n mod d) mod d = n mod d.
  intro H. (* C:regular *)
  apply N.mod_small. (* C:binarith *)
  apply N.mod_upper_bound. (* C:binarith *)
  exact H. (* C:regular *)
Qed.

Theorem xcomp_mod n : ⊖n mod (2^32) = ⊖n.
  unfold xcomp. (* C:binarith *)
  apply mod_n_n. (* C:binarith *)
  discriminate. (* C:regular *)
Qed.

Theorem xcomp_mod_in n : ⊖(n mod (2^32)) = ⊖n.
  unfold xcomp. (* C:binarith *)
  rewrite mod_n_n by discriminate. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplus_minus n m : m < n -> (n-m) mod (2^32) = n _⊖_ m.
  intros. (* C:regular *)
  assert (Q : m / (2^32) <= n / (2^32)). (* C:regular *)
  apply N.div_le_mono; try discriminate. (* C:regular *)
  apply N.lt_le_incl. (* C:regular *)
  assumption. (* C:regular *)
  unfold xcomp. (* C:regular *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite N.add_sub_assoc by (* C:binarith *)
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite N.add_comm. (* C:regular *)
  rewrite <- N.add_sub_assoc by (* C:binarith *)
      (apply N.lt_le_incl; eapply N.le_lt_trans; try exact H; (* C:binarith *)
       apply N.mod_le; discriminate). (* C:binarith *)
  rewrite mod_add_l by discriminate. (* C:binarith *)
  rewrite (N.div_mod m (2^32)) at 1 by discriminate. (* C:binarith *)
  rewrite N.sub_add_distr. (* C:binarith *)
  rewrite (N.div_mod n (2^32)) by discriminate. (* C:binarith *)
  rewrite N.add_sub_swap by (apply N.mul_le_mono_l; exact Q). (* C:binarith *)
  rewrite <- N.mul_sub_distr_l. (* C:binarith *)
  rewrite N.lt_eq_cases in Q. (* C:binarith *)
  destruct Q as [Q|Q]; [|rewrite Q]. (* C:binarith *)
  rewrite <- N.add_0_l in Q at 1. (* C:binarith *)
  rewrite N.lt_add_lt_sub_r in Q. (* C:binarith *)
  destruct (n / 2^32); try discriminate. (* C:binarith *)
  destruct (_ - m/_); try discriminate. (* C:binarith *)
  rewrite <- (N.succ_pos_pred p0). (* C:binarith *)
  rewrite <- (N.succ_pos_pred p). (* C:binarith *)
  repeat rewrite N.mul_succ_r. (* C:binarith *)
  repeat rewrite <- N.add_assoc. (* C:binarith *)
  repeat rewrite (N.add_comm (2^32)). (* C:binarith *)
  repeat rewrite <- (N.add_sub_assoc (_*_)) by  (* C:binarith *)
    (eapply N.le_trans; [apply N.lt_le_incl,N.mod_upper_bound; discriminate| (* C:binarith *)
                         rewrite N.add_comm; apply N.le_add_r]). (* C:binarith *)
  repeat rewrite mod_add_mul_ll by discriminate. (* C:binarith *)
  reflexivity. (* C:binarith *)
  rewrite N.sub_diag. (* C:binarith *)
  rewrite N.add_0_l. (* C:binarith *)
  rewrite <- N.add_sub_assoc; [symmetry; apply mod_add_mul_ll; discriminate|]. (* C:binarith *)
  rewrite (N.div_mod' n (2^32)) in H. (* C:binarith *)
  rewrite (N.div_mod' m (2^32)) in H. (* C:binarith *)
  rewrite Q in H. (* C:binarith *)
  apply N.lt_le_incl. (* C:binarith *)
  eapply N.add_lt_mono_l. (* C:binarith *)
  exact H. (* C:binarith *)
Qed.

Theorem xcomp_plus_dist' n m : ⊖n ⊕ ⊖m = ⊖(n+m).
  unfold xcomp. (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite N.add_mod_idemp_l by discriminate. (* C:binarith *)
  rewrite N.add_sub_assoc by (* C:binarith *)
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite N.add_comm. (* C:binarith *)
  rewrite N.add_sub_assoc by (* C:binarith *)
      (apply N.lt_le_incl; apply N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite <- N.sub_add_distr. (* C:binarith *)
  rewrite xplus_minus by (* C:binarith *)
      (apply N.add_lt_mono; apply N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite <- N.add_mod_idemp_l at 1 by discriminate. (* C:binarith *)
  rewrite N.add_0_l. (* C:binarith *)
  unfold xcomp. (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite N.add_mod_idemp_l by discriminate. (* C:binarith *)
  apply mod_n_n. (* C:binarith *)
  discriminate. (* C:binarith *)
Qed.

Theorem xcomp_plus_dist n m : ⊖n ⊕ ⊖m = ⊖(n⊕m).
  rewrite xcomp_plus_dist'. (* C:regular *)
  unfold xcomp. (* C:regular *)
  rewrite mod_n_n by discriminate. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplus_id_l' n : n ⊕ 0 = n mod 2^32.
  rewrite N.add_0_r. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplus_id_l n : n < 2^32 -> n ⊕ 0 = n.
  rewrite N.add_0_r. (* C:regular *)
  apply N.mod_small. (* C:binarith *)
Qed.

Theorem xplus_id_r' n : 0 ⊕ n = n mod 2^32.
  reflexivity. (* C:regular *)
Qed.

Theorem xplus_id_r n : n < 2^32 -> 0 ⊕ n = n.
  apply N.mod_small. (* C:regular *)
Qed.

Theorem xplus_comm n m : n ⊕ m = m ⊕ n.
  rewrite N.add_comm. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Lemma xplus_assoc : forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c.
  simpl. (* C:regular *)
  intros. (* C:regular *)
  rewrite N.add_mod_idemp_r, N.add_mod_idemp_l, N.add_assoc; (* C:binarith *)
    reflexivity + discriminate. (* C:binarith *)
Qed.

Theorem mod_greater (n d1 d2:N) :
  d1 ≠ 0 -> d1 <= d2 -> (n mod d1) mod d2 = n mod d1.
  intros. (* C:regular *)
  apply N.mod_small. (* C:binarith *)
  eapply N.lt_le_trans; eauto. (* C:regular *)
  apply N.mod_upper_bound. (* C:binarith *)
  exact H. (* C:regular *)
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
  destruct n as [|n],w as [|w]; auto using N.mod_1_r. (* C:binarith *)
  unfold mod2. (* C:binarith *)
  generalize dependent n. (* C:binarith *)
  induction w using Pos.peano_ind. (* C:binarith *)
  intros. (* C:binarith *)
  rewrite <- N.bit0_mod. (* C:binarith *)
  simpl. (* C:binarith *)
  destruct n; reflexivity. (* C:binarith *)
  intros. (* C:binarith *)
  rewrite npossucc. (* C:binarith *)
  rewrite N.pow_succ_r; try discriminate. (* C:binarith *)
  rewrite N.mod_mul_r; try discriminate. (* C:binarith *)
  simpl. (* C:binarith *)
  rewrite <- N.div2_div. (* C:binarith *)
  rewrite <- N.bit0_mod. (* C:binarith *)
  destruct n; simpl; try rewrite Pos.pred_succ; try rewrite IHw; simpl; auto;
    destruct (_ mod _),w; simpl; reflexivity. (* C:binarith *)
Qed.

Theorem xplusid' : forall n, n ⊕ 0 = n mod 2^32.
  intro n. (* C:regular *)
  rewrite N.add_0_r. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplusinv' : forall b c, b < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c mod 2^32.
  intros. (* C:regular *)
  rewrite (N.add_comm (2^32)). (* C:binarith *)
  rewrite N.add_comm. (* C:binarith *)
  destruct b. (* C:binarith *)
  rewrite N.add_0_r. (* C:binarith *)
  rewrite N.sub_0_r. (* C:binarith *)
  rewrite mod_add_r; try discriminate. (* C:binarith *)
  apply mod_n_n. (* C:binarith *)
  discriminate. (* C:binarith *)
  assert (N.pos p <= 2^32); auto using N.lt_le_incl. (* C:binarith *)
  rewrite <- N.add_sub_assoc; auto. (* C:binarith *)
  rewrite <- xplus_assoc. (* C:binarith *)
  rewrite N.sub_add; auto. (* C:binarith *)
  rewrite N.mod_same; try discriminate. (* C:binarith *)
  rewrite N.add_0_r. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplusinv : forall b c, b < 2^32 -> c < 2^32 -> b ⊕ (2^32 + c ⊖ b) = c.
  intros. (* C:regular *)
  rewrite xplusinv'; auto. (* C:binalg *)
  apply N.mod_small. (* C:binarith *)
  assumption. (* C:regular *)
Qed.

Theorem minus_n_mod_n n m : 0 < m -> m < n -> (n - m) mod m = n mod m.
  intros H0 H1. (* C:regular *)
  rewrite (N.div_mod' n m) at 1. (* C:regular *)
  assert (Q : m <= m * (n / m)). (* C:regular *)
  rewrite <- N.mul_1_r at 1. (* C:regular *)
  apply N.mul_le_mono_pos_l; [exact H0|]. (* C:regular *)
  destruct m; inversion H0. (* C:regular *)
  apply N.div_le_lower_bound; [discriminate|]. (* C:regular *)
  rewrite N.mul_1_r. (* C:regular *)
  apply N.lt_le_incl. (* C:regular *)
  exact H1. (* C:regular *)
  rewrite N.add_sub_swap by exact Q. (* C:binarith *)
  rewrite <- N.mul_pred_r. (* C:binarith *)
  destruct m; inversion H0. (* C:binarith *)
  rewrite mod_add_mul_ll by discriminate. (* C:binarith *)
  apply mod_n_n. (* C:binarith *)
  discriminate. (* C:binarith *)
Qed.

Theorem xcomp_comp n : n < 2^32 -> ⊖(⊖n) = n.
  intro H. (* C:regular *)
  rewrite <- (xplus_id_l n) at 2 by assumption. (* C:binalg *)
  rewrite <- (xminus_zero (⊖n)). (* C:binalg *)
  rewrite xplus_assoc. (* C:binalg *)
  fold (n _⊖_ n). (* C:binalg *)
  rewrite xminus_zero. (* C:binalg *)
  rewrite xplus_id_r by (apply N.mod_upper_bound; discriminate). (* C:binalg *)
  reflexivity. (* C:binalg *)
Qed.

(* CATEGORY: modular equations *)
Theorem xeq_xplus_r n m p :
  n < 2^32 -> p < 2^32 -> n ⊕ m = p <-> n = p _⊖_ m.
  intros. (* C:regular *)
  split; intros; subst; rewrite <- xplus_assoc; [|rewrite (N.add_comm _ m)]; (* C:binalg *)
    rewrite xminus_zero; rewrite xplus_id_l by assumption; (* C:binalg *)
      reflexivity. (* C:binalg *)
Qed.

Theorem xeq_xplus_l n m p :
  m < 2^32 -> p < 2^32 -> n ⊕ m = p <-> m = ⊖n ⊕ p.
  intros. (* C:regular *)
  rewrite xplus_comm. (* C:binalg *)
  rewrite xeq_xplus_r by assumption. (* C:binalg *)
  rewrite xplus_comm. (* C:binalg *)
  reflexivity. (* C:regular *)
Qed.

Theorem xeq_xcomp_r n m p :
  n < 2^32 -> p < 2^32 -> n _⊖_ m = p <-> n = p ⊕ m.
  intros. (* C:regular *)
  rewrite xeq_xplus_r by assumption. (* C:binalg *)
  rewrite <- (xcomp_mod_in m). (* C:binalg *)
  rewrite xcomp_comp by (apply N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binalg *)
  reflexivity. (* C:regular *)
Qed.

Theorem xeq_xcomp_l n m p :
  m < 2^32 -> p < 2^32 -> ⊖n ⊕ m = p <-> m = n ⊕ p.
  intros. (* C:regular *)
  rewrite xplus_comm. (* C:binalg *)
  rewrite xeq_xcomp_r by assumption. (* C:binalg *)
  rewrite xplus_comm. (* C:binalg *)
  reflexivity. (* C:regular *)
Qed.

(* more mordular arithmetic *)
Theorem xplus_minus' n m : m <= n → n ⊖ m = n _⊖_ m.
  intro H. (* C:regular *)
  rewrite N.lt_eq_cases in H. (* C:regular *)
  destruct H; [apply xplus_minus; assumption|]. (* C:binalg *)
  subst. (* C:regular *)
  rewrite xminus_zero. (* C:binalg *)
  rewrite N.sub_diag. (* C:binarith *)
  reflexivity. (* C:regular *)
Qed.

Theorem xplus_minus'' n m :
  n < 2^32 -> m <= n → n - m = n _⊖_ m.
  intros H0 H1. (* C:regular *)
  unfold xcomp. (* C:binarith *)
  rewrite N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite N.add_sub_assoc by (* C:binarith *)
      (apply N.lt_le_incl,N.mod_upper_bound; discriminate). (* C:binarith *)
  rewrite N.add_comm. (* C:binarith *)
  assert (H2 : m < 2^32) by (eapply N.le_lt_trans; eassumption). (* C:binarith *)
  rewrite (N.mod_small m) by (eapply N.le_lt_trans; eassumption). (* C:binarith *)
  rewrite <- N.add_sub_assoc by assumption. (* C:binarith *)
  rewrite mod_add_l by discriminate. (* C:binarith *)
  symmetry. (* C:binarith *)
  apply N.mod_small. (* C:binarith *)
  eapply N.le_lt_trans ; [|exact H0]. (* C:binarith *)
  apply N.le_sub_l. (* C:binarith *)
Qed.

Theorem xlt_minus n m p :
  n < 2^32 -> n _⊖_ m < p -> n < p + m.
  intros H1 H2. (* C:regular *)
  destruct (N.lt_ge_cases n m) as [H3|H3]. (* C:regular *)
  eapply N.lt_le_trans; [exact H3|]. (* C:regular *)
  rewrite N.add_comm. (* C:regular *)
  apply N.le_add_r. (* C:regular *)
  rewrite <- xplus_minus'' in H2 by assumption. (* C:binarith *)
  apply N.lt_sub_lt_add_r. (* C:regular *)
  assumption. (* C:regular *)
Qed.

Theorem sub_eq_r n m p : n <= m -> p <= m - n <-> p + n <= m.
  intro H0. (* C:regular *)
  rewrite N.add_le_mono_r. (* C:regular *)
  rewrite N.sub_add by exact H0. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Theorem xminus_eq_r n m p :
  n < 2^32 -> m <= n -> p <= n _⊖_ m <-> p + m <= n.
  intros H0 H1. (* C:regular *)
  rewrite <- xplus_minus'' by assumption. (* C:binarith *)
  apply sub_eq_r. (* C:regular *)
  assumption. (* C:regular *)
Qed.

Theorem andshiftlzero' : forall a b w,
    (a mod 2^w) .& (b << w) = 0.
  destruct a,b,w; try rewrite N.mod_1_r; (* C:binarith *)
    try rewrite N.shiftl_0_l,N.land_0_r; auto. (* C:binarith *)
  rewrite <- mod2_eq. (* C:binarith *)
  simpl. (* C:binarith *)
  generalize dependent p. (* C:binarith *)
  generalize dependent p0. (* C:binarith *)
  induction p1 using Pos.peano_ind; simpl; auto. (* C:binarith *)
  destruct p; reflexivity. (* C:binarith *)
  destruct p; simpl; try rewrite Pos.pred_succ; rewrite Pos.iter_succ; auto; (* C:binarith *)
    destruct (Pos.succ p1); auto; specialize (IHp1 p0 p); (* C:binarith *)
      destruct posmod2; auto; simpl in *; rewrite IHp1; reflexivity. (* C:binarith *)
Qed.

Theorem andshiftlzero : forall a b w,
    a < 2^w -> a .& (b << w) = 0.
  intros a b w. (* C:regular *)
  rewrite <- N.shiftl_1_l. (* C:binarith *)
  destruct a,b,w; simpl; auto. (* C:binarith *)
  intros. (* C:binarith *)
  destruct p; discriminate. (* C:binarith *)
  unfold N.lt. (* C:binarith *)
  simpl. (* C:binarith *)
  generalize dependent p0. (* C:binarith *)
  generalize dependent p. (* C:binarith *)
  induction p1 using Pos.peano_ind; simpl; auto. (* C:binarith *)
  intros. (* C:binarith *)
  destruct p; simpl; auto. (* C:binarith *)
  destruct p; inversion H. (* C:binarith *)
  destruct p; inversion H. (* C:binarith *)
  intros a b. (* C:binarith *)
  repeat rewrite Pos.iter_succ. (* C:binarith *)
  intros. (* C:binarith *)
  destruct a; simpl; auto; rewrite IHp1; auto. (* C:binarith *)
  generalize dependent (Pos.iter xO 1%positive p1). (* C:binarith *)
  intros. (* C:binarith *)
  clear IHp1. (* C:binarith *)
  fold (N.compare (N.pos a) (N.pos p)). (* C:binarith *)
  fold (N.lt (N.pos a) (N.pos p)). (* C:binarith *)
  rewrite N.mul_lt_mono_pos_l. (* C:binarith *)
  repeat rewrite <- N.double_spec. (* C:binarith *)
  simpl. (* C:binarith *)
  eapply N.lt_trans. (* C:binarith *)
  apply N.lt_succ_diag_r. (* C:binarith *)
  simpl. (* C:binarith *)
  auto. (* C:binarith *)
  reflexivity. (* C:binarith *)
Qed.

(* CATEGORY: memory lemmas *)
Theorem set_dword : forall m a v,
    m [Ⓓa := v]
    = m [Ⓑa := v mod 2^8]
        [Ⓑa+1 := v >> 8 mod 2^8]
        [Ⓑa+2 := v >> 16 mod 2^8]
        [Ⓑa+3 := v >> 24].
  intros. (* C:regular *)
  repeat rewrite setmem_1. (* C:memory *)
  simpl setmem. (* C:memory *)
  unfold setmem,setmem_little,Mb,ARMArch.mem_bits. (* C:memory *)
  repeat rewrite <- N.add_1_r. (* C:regular *)
  repeat rewrite <- N.add_assoc. (* C:regular *)
  simpl (1+_). (* C:regular *)
  repeat f_equal. (* C:regular *)
Qed.

Theorem set_dword_aligned : forall m a v,
    a < 2^32
    -> a mod 2^2 = 0
    -> m [Ⓓa := v]
       = m [Ⓑa := v mod 2^8]
           [Ⓑa⊕1 := v >> 8 mod 2^8]
           [Ⓑa⊕2 := v >> 16 mod 2^8]
           [Ⓑa⊕3 := v >> 24].
  intros. (* C:regular *)
  rewrite <- mod2_eq in H0. (* C:binarith *)
  assert (a⊕1=a+1/\a⊕2=a+2/\a⊕3=a+3). (* C:binarith *)
  repeat rewrite <- mod2_eq. (* C:binarith *)
  destruct a; auto. (* C:binarith *)
  destruct p; inversion H0; destruct p; inversion H0. (* C:binarith *)
  simpl. (* C:binarith *)
  fold (mod2 (N.pos p) 30). (* C:binarith *)
  rewrite mod2_eq. (* C:binarith *)
  rewrite N.mod_small. (* C:binarith *)
  repeat split; reflexivity. (* C:binarith *)
  rewrite (N.mul_lt_mono_pos_l 4); auto. (* C:binarith *)
  reflexivity. (* C:binarith *)
  intuition. (* C:binarith *)
  rewrite H2,H1,H4. (* C:binarith *)
  apply set_dword. (* C:binarith *)
Qed.

(* CATEGORY: calling convention *)
Theorem tc_extract : forall tc reg st (H : models tc st),
    match tc reg with
    | Some (NumT w) => vnum (st reg) < 2^w
    | Some (MemT w) => welltyped_memory (vmem (st reg))
    | None => True
    end.
  unfold models. (* C:regular *)
  intros. (* C:regular *)
  specialize (H reg). (* C:regular *)
  destruct tc; auto. (* C:regular *)
  specialize (H _ eq_refl). (* C:regular *)
  inversion H; auto. (* C:regular *)
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
  intros. (* C:regular *)
  rewrite H. (* C:regular *)
  rewrite H0. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Definition arm_vreg_preserves prog :=
  forall s n s' x,
    exec_prog fh prog 0 s n s' x
    -> List.map s' armcc_vreg = List.map s armcc_vreg.

Theorem memset_preserves_vreg : arm_vreg_preserves memset_arm.
  unfold arm_vreg_preserves. (* C:picinae *)
  intros. (* C:picinae *)
  compute. (* C:picinae *)
  repeat apply cons_eq; (* C:picinae *)
    try reflexivity; (* C:picinae *)
    (eapply noassign_prog_same; [|eassumption]; prove_noassign). (* C:picinae *)
Qed.

Theorem memset_preserves_rsp :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_SP = s R_SP.
  intros. (* C:picinae *)
  eapply noassign_prog_same; [|eassumption]. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.

(* CATEGORY: memset specification and invariants *)
Theorem memset_ret :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_R0 = s R_R0.
  intros. (* C:picinae *)
  eapply noassign_prog_same; [|eassumption]. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.

Definition memfilled (m:addr->N) (s:addr) (c:N) n :=
  forall i, i < n -> m (s⊕i) = c.

Definition memset_bytedup c :=
  (c .| ((c << 8) mod 2 ^ 32)
     .| ((c .| ((c << 8) mod 2 ^ 32) << 16) mod 2 ^ 32)).

Definition memset_post s c n (_:exit) (st:store) :=
  exists m, st V_MEM32 = Ⓜm /\ st R_R0 = Ⓓs /\ memfilled m s c n.

Definition memset_invs (s:addr) (c:N) n (a:addr) (st:store) :=
  let r1 := vnum (st R_R1) in
  let r2 := vnum (st R_R2) in
  let r3 := vnum (st R_R3) in
  let m := vmem (st V_MEM32) in
  let common_inv := s ⊕ n = r3 ⊕ r2 /\ memfilled m s c (⊖s ⊕ r3) in
  match a with
  | 0 => Some (vnum (st R_R0) = s /\ r2 = n /\ r1 mod (2^8) = c)
  | 12 => Some (r1 mod (2^8) = c /\ common_inv)
  | 44 => Some (st R_R12 = st R_R1
                /\ r1 = memset_bytedup c
                /\ r3 mod (2^2) = 0
                /\ common_inv)
  | 84 => Some (vnum (st R_R1) mod (2^8) = c /\ common_inv)
  | 120 => Some (memfilled m s c n)
  | _ => None
  end.

Definition memset_invset s c n :=
  invs (memset_invs s c n) (memset_post s c n).

(* CATEGORY: memfilled lemmas *)

Lemma memfilled_split :
  forall m s c n1 n2,
    memfilled m s c n1
    -> memfilled m (s + n1) c n2
    -> memfilled m s c (n1 + n2).
  intros. (* C:regular *)
  unfold memfilled in *. (* C:regular *)
  intros. (* C:regular *)
  destruct (N.lt_ge_cases i n1); auto. (* C:regular *)
  rewrite <- (H0 (i - n1)). (* C:regular *)
  rewrite <- N.add_assoc. (* C:regular *)
  rewrite (N.add_comm n1). (* C:regular *)
  rewrite N.sub_add; auto. (* C:regular *)
  eapply N.le_lt_add_lt. (* C:regular *)
  apply N.le_refl. (* C:regular *)
  rewrite N.sub_add; auto. (* C:regular *)
  rewrite N.add_comm. (* C:regular *)
  assumption. (* C:regular *)
Qed.

Lemma memfilled_split' :
  forall m s c n1 n2,
    memfilled m s c n1
    -> memfilled m (s ⊕ n1) c n2
    -> memfilled m s c (n1 + n2).
  intros. (* C:regular *)
  unfold memfilled in *. (* C:regular *)
  intros. (* C:regular *)
  destruct (N.lt_ge_cases i n1); auto. (* C:regular *)
  rewrite <- (H0 (i - n1)). (* C:regular *)
  rewrite N.add_mod_idemp_l. (* C:binarith *)
  rewrite <- N.add_assoc. (* C:regular *)
  rewrite (N.add_comm n1). (* C:regular *)
  rewrite N.sub_add; auto. (* C:regular *)
  discriminate. (* C:regular *)
  eapply N.le_lt_add_lt. (* C:regular *)
  apply N.le_refl. (* C:regular *)
  rewrite N.sub_add; auto. (* C:regular *)
  rewrite N.add_comm. (* C:regular *)
  assumption. (* C:regular *)
Qed.

Lemma memfilled_mod :
  forall m s c n,
    memfilled m s c n
    -> memfilled m s c (n mod (2^32)).
  unfold memfilled. (* C:regular *)
  intros. (* C:regular *)
  apply H. (* C:regular *)
  destruct (N.lt_ge_cases n (2^32)). (* C:regular *)
  rewrite N.mod_small in H0; auto. (* C:regular *)
  eapply N.lt_trans; try eassumption. (* C:regular *)
  eapply N.lt_le_trans; try eassumption. (* C:regular *)
  apply N.mod_upper_bound; auto. (* C:regular *)
  discriminate. (* C:regular *)
Qed.

Lemma memfilled_update :
  forall m s c n a,
    memfilled m s c n
    -> memfilled (m[Ⓑ a := c]) s c n.
  rewrite setmem_1. (* C:regular *)
  unfold update,memfilled. (* C:regular *)
  intros. (* C:regular *)
  destruct (_ == _); auto. (* C:regular *)
Qed.

(* CATEGORY: bytedup proof (filling a word with a char) *)

Theorem bytedup_spec : forall c,
    c < 2^8
    -> memset_bytedup c mod 2^8 = c
    /\ memset_bytedup c >> 8 mod 2^8 = c
    /\ memset_bytedup c >> 16 mod 2^8 = c
    /\ memset_bytedup c >> 24 = c.
  unfold memset_bytedup. (* C:binarith *)
  all: replace 32 with (24+8); replace 24 with (16+8); (* C:binarith *)
    replace 16 with (8+8); auto. (* C:binarith *)
  intros. (* C:binarith *)
  assert (Q : c + (c << 8) < 2^(8+8)). (* C:binarith *)
  rewrite N.shiftl_mul_pow2. (* C:binarith *)
  eapply N.lt_le_trans. (* C:binarith *)
  apply N.add_lt_mono_r; eassumption. (* C:binarith *)
  rewrite <- Nmult_Sn_m. (* C:binarith *)
  rewrite N.pow_add_r. (* C:binarith *)
  apply N.mul_le_mono_pos_r; try reflexivity. (* C:binarith *)
  rewrite N.le_succ_l. (* C:binarith *)
  apply H. (* C:binarith *)
  replace ((c << 8) mod 2^(8+8+8+8)) with (c<<8). (* C:binarith *)
  2: { symmetry. apply N.mod_small. eapply N.le_lt_trans. apply N.le_add_r. (* C:binarith *)
       rewrite N.add_comm. eapply N.lt_trans; try eassumption. reflexivity. } (* C:binarith *)
  replace ((c .| (c<<8) << (8+8)) mod 2^(8+8+8+8)) with (c .| (c<<8) << 8 << 8). (* C:binarith *)
  2: { symmetry. rewrite N.shiftl_shiftl. apply N.mod_small. (* C:binarith *)
       repeat rewrite N.shiftl_mul_pow2 in *. repeat rewrite N.pow_add_r. (* C:binarith *)
       rewrite <- N.mul_assoc. apply N.mul_lt_mono_pos_r; try reflexivity. (* C:binarith *)
       repeat rewrite <- N.pow_add_r. rewrite lor_plus; auto. (* C:binarith *)
       rewrite <- N.shiftl_mul_pow2. apply andshiftlzero. assumption. } (* C:binarith *)
  repeat (rewrite N.shiftl_lor + rewrite N.shiftr_lor (* C:binarith *)
          + rewrite <- N.shiftl_shiftl + rewrite <- N.shiftr_shiftr (* C:binarith *)
          + rewrite N.add_assoc + rewrite N.shiftr_shiftl_l,N.shiftl_0_r); (* C:binarith *)
    try discriminate. (* C:binarith *)
  replace (c >> 8) with 0; try rewrite shiftr_low_pow2; auto; try reflexivity. (* C:binarith *)
  repeat rewrite N.shiftr_0_l. (* C:binarith *)
  simpl. (* C:binarith *)
  repeat rewrite <- N.shiftl_lor. (* C:binarith *)
  simpl in Q. (* C:binarith *)
  repeat rewrite lor_plus; auto using andshiftlzero. (* C:binarith *)
  repeat rewrite N.shiftl_mul_pow2. (* C:binarith *)
  repeat rewrite N.mod_add; try discriminate. (* C:binarith *)
  repeat rewrite N.mod_small; try assumption. (* C:binarith *)
  repeat split; reflexivity. (* C:binarith *)
  rewrite N.shiftl_shiftl. (* C:binarith *)
  apply andshiftlzero. (* C:binarith *)
  assumption. (* C:binarith *)
Qed.

(* CATEGORY: more memset lemmas *)

Theorem memset_preserves_lr :
  forall s n s' x,
    exec_prog fh memset_arm 0 s n s' x -> s' R_LR = s R_LR.
  intros. (* C:regular *)
  eapply noassign_prog_same; try eassumption. (* C:picinae *)
  prove_noassign. (* C:picinae *)
Qed.

Theorem memfilled_succ : forall m s c n,
    memfilled m s c n -> memfilled (update m (s ⊕ n) c) s c (N.succ n).
  intros. (* C:regular *)
  unfold memfilled,update in *. (* C:memory *)
  intros. (* C:memory *)
  destruct iseq; auto. (* C:memory *)
  rewrite N.lt_succ_r in H0. (* C:regular *)
  rewrite N.le_lteq in H0. (* C:regular *)
  destruct H0; subst; auto. (* C:regular *)
  destruct n0. (* C:regular *)
  reflexivity. (* C:regular *)
Qed.

Theorem memset_welltyped: welltyped_prog armtypctx memset_arm.
Proof.
  Picinae_typecheck. (* C:picinae *)
Qed.

Theorem memfilled_zero : forall m s c, memfilled m s c 0.
  unfold memfilled. (* C:regular *)
  destruct i; discriminate. (* C:regular *)
Qed.

Theorem memfilled_one' m s c : memfilled (update m (s mod (2^32)) c) s c 1.
  unfold memfilled. (* C:regular *)
  intros i H. (* C:regular *)
  destruct i; try (rewrite N.add_0_r; apply update_updated). (* C:regular *)
  destruct p; inversion H. (* C:regular *)
Qed.

Theorem memfilled_one m s c : s < 2^32 -> memfilled (update m s c) s c 1.
  intros. (* C:regular *)
  erewrite <- (N.mod_small s (2^32)) at 1 by exact H. (* C:regular *)
  apply memfilled_one'. (* C:regular *)
Qed.

Theorem memfilled_xcomp m s c skip n :
  memfilled m s c (⊖s ⊕ skip)
  -> memfilled m skip c n
  -> memfilled m s c (⊖s ⊕ skip ⊕ n).
  intros H H0. (* C:regular *)
  apply memfilled_mod. (* C:regular *)
  apply memfilled_split'; [exact H|]. (* C:regular *)
  rewrite xplus_assoc. (* C:binalg *)
  rewrite xminus_zero. (* C:binalg *)
  rewrite N.add_0_l. (* C:binarith *)
  unfold memfilled in *. (* C:regular *)
  intro. (* C:regular *)
  rewrite N.add_mod_idemp_l by discriminate. (* C:binarith *)
  apply H0. (* C:regular *)
Qed.

(* CATEGORY: memset proof *)
Theorem memset_partial_correctness:
  forall st lr s ci c n q st' x m
         (MDL0: models armtypctx st)
         (LR0: st R_LR = Ⓓlr) (MEM0: st V_MEM32 = Ⓜm)
         (R0: st R_R0 = Ⓓs) (R1: st R_R1 = Ⓓci) (R2: st R_R2 = Ⓓn)
         (C: c = ci mod 2^8)
         (RET: memset_arm st lr = None)
         (XP0: exec_prog fh memset_arm 0 st q st' x),
    trueif_inv (memset_invset s c n memset_arm x st').
  (* most of the proof here is setting up to either: *)
  (* 1: solve "obvious" portions of the proof *)
  (* 2: apply memfilled lemmas *)
  (* CATEGORY: PICINAE SETUP *)
  intros. (* C:regular *)
  eapply prove_invs; [exact XP0|simpl;rewrite R0,R1,R2,C;tauto|]. (* C:picinae *)
  intros. (* C:picinae *)
  assert (WTM : models armtypctx s1). (* C:picinae *)
  1: { eapply preservation_exec_prog; try eassumption. apply memset_welltyped. } (* C:picinae *)
  assert (TCX := fun r => tc_extract _ r _ WTM). (* C:picinae *)
  assert (TCXR0 := tc_extract _ R_R0 _ MDL0). (* C:picinae *)
  assert (TCXR1 := TCX R_R1). (* C:picinae *)
  assert (TCXR2 := TCX R_R2). (* C:picinae *)
  assert (TCXR3 := TCX R_R3). (* C:picinae *)
  simpl in *. (* C:picinae *)
  rewrite R0 in TCXR0. (* C:picinae *)
  subst. (* C:picinae *)
  assert (PLR : s1 R_LR = Ⓓlr).
  erewrite memset_preserves_lr; eassumption.
  shelve_cases 32 PRE. Unshelve. (* C:picinae *)

  all: intuition. (* C:picinae *) (* extract precondition hypotheses *)
  Local Ltac step := time arm_step. (* C:picinae *)

  (* Proving postcondition from final invariant *)
  5: { step.
       unfold memset_post.
       repeat rewrite update_frame by discriminate.
       specialize (WTM V_MEM32 _ eq_refl).
       inversion WTM; subst.
       rewrite <- H0 in *.
       eexists; intuition; eauto.
       erewrite memset_ret; eauto.
  } (* C:picinae *)

  (* CATEGORY: proof of function setup *)
  (* proof of function setup *)
  subst. (* C:picinae *)
  do 3 step. (* C:picinae *)
  1-2: rewrite H2. (* C:picinae *)
  1-2: unfold vnum,vmem in *; rewrite Hsv,Hsv0 in *; intuition. (* C:picinae *)
  1-2: rewrite N.add_comm; fold (n _⊖_ n); rewrite (xminus_zero n). (* C:binalg *)
  1-2: apply memfilled_zero. (* C:regular *)

  (* CATEGORY: proof of first loop *)
  (* proof of first loop *)
  repeat (discriminate + step). (* C:picinae *)
  1-2: unfold vnum,vmem in *. (* C:picinae *)
  1-2: rewrite Hsv,Hsv0,Hsv1,Hsv2,H in *. (* C:picinae *)
  intuition. (* C:picinae *)
  apply N.eqb_eq. (* C:picinae *)
  assumption. (* C:regular *)
  intuition. (* C:picinae *)
  rewrite <- xplus_assoc. (* C:binalg *)
  rewrite xplusinv; [assumption|reflexivity|assumption]. (* C:binalg *)
  rewrite xplus_assoc. (* C:binalg *)
  apply memfilled_xcomp; [apply memfilled_update; assumption|]. (* C:regular *)
  apply memfilled_one. (* C:regular *)
  assumption. (* C:picinae *)

  (* CATEGORY: proof of second loop (part 1) *)
  (* proof of second loop *)
  destruct (bytedup_spec (ci mod N.pos (2 ^ 8))); (* C:ARM *)
    [apply N.mod_upper_bound; discriminate|]. (* C:ARM *)
  intuition. (* C:binalg *)
  repeat (discriminate + step). (* C:picinae *)
  1-5: unfold vnum,vmem in *. (* C:picinae *)
  1-5: rewrite Hsv,Hsv0,Hsv1,Hsv2,Hsv3 in *. (* C:picinae *)
  1-5: inversion H; subst. (* C:picinae *)
  1-5: repeat rewrite <- xplus_assoc. (* C:binalg *)
  repeat rewrite xplusinv by (reflexivity + apply N.mod_upper_bound; discriminate). (* C:binalg *)
  intuition. (* C:regular *)
  simpl (8 ⊕ _). (* C:binarith *)
  rewrite dblmod_r by discriminate. (* C:binarith *)
  rewrite (N.mod_small 32) by reflexivity. (* C:binarith *)
  rewrite <- N.add_mod_idemp_r by discriminate. (* C:binarith *)
  rewrite N.add_comm. (* C:binarith *)
  simpl. (* C:binarith *)
  assumption. (* C:binarith *)
  rewrite xminus_alt by assumption + reflexivity. (* C:binalg *)
  rewrite (xplus_comm 8). (* C:binalg *)
  rewrite <- xplus_assoc. (* C:binalg *)
  rewrite (xplus_comm _ 8). (* C:binalg *)
  rewrite xminus_zero. (* C:binalg *)
  rewrite N.add_0_r. (* C:binarith *)
  rewrite (N.mod_small n0); assumption. (* C:binarith *)
  2-4: repeat rewrite xminus_alt by assumption + reflexivity. (* C:binalg *)
  2-5: rewrite minus_n_mod_n by (* C:binalg *)
      reflexivity + (eapply N.lt_le_trans; [|apply N.le_add_r]; reflexivity). (* C:binalg *)
  2-5: (* C:binarith *)
    repeat (* C:binarith *)
      match goal with (* C:binarith *)
        [ _ : context [ ?x <=? ?y ] |- _] => destruct (N.leb_spec x y) (* C:binarith *)
      end; try discriminate. (* C:binarith *)
  (* some things are tricky to prove, shelve them to prove them later *)
  2-4: intuition; [shelve|]. (* C:binarith *)
  5: intuition; shelve. (* C:binarith *)
  1-4: rewrite (xplus_assoc (⊖s)). (* C:binalg *)
  (* note that the memory access needs to be aligned to words *)
  (* this is the reason why the invariants contain alignment statements *)
  (* this tactic does everything necessary to show alignment for offsets *)
  (* this yields a proof effectively solvable with the memfilled goals *)
  1-4: repeat rewrite set_dword_aligned by (* C:memory *)
      (apply N.mod_upper_bound; discriminate) + (* C:binarith *)
      (rewrite dblmod_r by discriminate; (* C:binarith *)
       rewrite <- N.add_mod_idemp_r by discriminate; (* C:binarith *)
       rewrite N.add_0_r; (* C:binarith *)
       assumption) + assumption. (* C:binarith *)
  1-4: repeat rewrite setmem_1. (* C:memory *)
  1-4: rewrite H3,H6,H5,H8. (* C:binarith *) (* eliminate memset_bytedup *)
  1-4: apply memfilled_xcomp; [repeat apply memfilled_update; assumption|]. (* C:regular *)
  1-4: repeat rewrite <- xplus_assoc. (* C:binalg *)
  1-4: repeat apply memfilled_succ. (* C:regular *)
  1-4: apply memfilled_one; assumption. (* C:regular *)

  (* CATEGORY: proof of last loop *)
  (* prove the last loop *)
  (* n ends up being too opaque to use for most of the memfilled proofs *)
  (* replace it before starting to simplify things *)
  assert (Q : (⊖s ⊕ vnum (s1 R_R3) ⊕ vnum (s1 R_R2)) = n). (* C:binalg *)
  rewrite <- xplus_assoc. rewrite <- H1. rewrite xplus_assoc. (* C:binalg *)
  rewrite (xplus_comm _ s). rewrite xminus_zero. (* C:binalg *)
  rewrite N.add_0_l. apply N.mod_small. pose (Q := tc_extract _ R_R2 _ MDL0). (* C:binarith *)
  rewrite R2 in Q. exact Q. (* C:binarith *)
  subst. (* C:binalg *)
  repeat (discriminate + step). (* C:picinae *)
  all: unfold vnum,vmem,memset_post in *; rewrite Hsv,Hsv0,Hsv1,Hsv2 in *. (* C:picinae *)
  (* only the first subgoal contains things outside of memfilled *)
  (* use intuition to break it up, solve the non-memfilled subgoal *)
  intuition. (* C:regular *)
  repeat rewrite <- xplus_assoc. (* C:binalg *)
  rewrite xplus_assoc. (* C:binalg *)
  rewrite xminus_zero. (* C:binalg *)
  rewrite N.add_0_l. (* C:binarith *)
  rewrite mod_n_n by discriminate. (* C:binarith *)
  repeat rewrite xplusinv; try reflexivity; (* C:binarith *)
    try apply N.mod_upper_bound; try discriminate; assumption. (* C:binarith *)
  repeat rewrite (xplus_assoc (⊖s)). (* C:binalg *)
  repeat rewrite <- (xplus_assoc (⊖s ⊕ n0)). (* C:binalg *)
  1-4: rewrite H. (* C:binalg *)
  1-5: apply memfilled_xcomp; [repeat apply memfilled_update; assumption|]. (* C:regular *)
  1-5: repeat rewrite <- xplus_assoc. (* C:binalg *)
  repeat apply memfilled_succ. (* C:regular *)
  apply memfilled_one. (* C:regular *)
  assumption. (* C:regular *)
  all: repeat (* C:regular *)
         match goal with (* C:regular *)
           [ _ : context [ ?x <=? ?y ] |- _] => destruct (N.leb_spec x y) (* C:regular *)
         end; try discriminate. (* C:regular *)
  (* the next 3 tactics get the value of n *)
  all: rewrite N.lt_1_r in *. (* C:regular *)
  1-3: match goal with (* C:binarith *)
         H : (2^32 + _ ⊖ 1) = 0 |- _ => (* C:binarith *)
         repeat (* C:binarith *)
           (rewrite xminus_alt in H by (* C:binarith *)
               (assumption + reflexivity + (apply N.mod_upper_bound; discriminate)); (* C:binarith *)
            rewrite xeq_xplus_r in H by (* C:binarith *)
                (assumption + reflexivity + (apply N.mod_upper_bound; discriminate))); (* C:binarith *)
           compute in H (* C:binarith *)
       end. (* C:binarith *)
  all: subst. (* C:regular *)
  4: apply memfilled_zero. (* C:regular *)
  all: repeat apply memfilled_succ; apply memfilled_one; assumption. (* C:regular *)

  (* CATEGORY: proof of second loop (part 2) *)
  (* the tricky goals from the second loop *)
  (* basically, this is showing that s ⊕ n = r3 ⊕ r2 *)
  Unshelve. (* C:regular *)
  all: rewrite H2. (* C:regular *)
  all: do 2 f_equal. (* C:regular *)
  all: repeat rewrite xminus_alt in * by (* C:binarith *)
      (reflexivity + assumption + apply N.mod_upper_bound; discriminate). (* C:binarith *)
  all: repeat (apply xlt_minus in H1; (* C:binalg *)
               (assumption + reflexivity +  (* C:binalg *)
                (try apply N.mod_upper_bound; try discriminate))). (* C:binarith *)
  (* an upper bound on r2 is known at this point *)
  (* it's possible to complete the proof by brute force here *)
  (* now we need to prove a lower bound *)
  (* before doing that, get rid of a pointless 2 ^ 32 *)
  all: replace (2^32) with (2^29 * 2^3) by reflexivity. (* C:binarith *)
  all: rewrite mod_add_mul_lr by discriminate. (* C:binarith *)
  all: replace (2^29 * 2^3) with (2^32) by reflexivity. (* C:binarith *)

  all: fold (2^32) in *. (* C:binarith *)
  all: repeat rewrite <- xplus_assoc in *. (* C:binalg *)
  all: repeat rewrite xcomp_plus_dist' in *. (* C:binalg *)
  all: repeat match goal with (* C:binalg *)
                [H1 : ?m <= ?n, H2 : ?n < 2^32 |- _] => (* C:binalg *)
                rewrite (xminus_eq_r n m) in * by exact H2 + exact H1 (* C:binalg *)
              end. (* C:binalg *)

  (* upper and lower bounds on n0 are now known *)
  (* simplify the proof context so we have it all directly *)
  all: repeat match goal with H : _ < 2^32 |- _ => clear H end. (* C:regular *)
  all: simpl (_<_) in *. (* C:regular *)
  all: simpl (_<=_) in *. (* C:regular *)
  (* brute force all possible values of n (at most 8) *)
  all: repeat (* C:regular *)
         match goal with (* C:regular *)
           H : _ < N.pos _ |- _ => (* C:regular *)
           apply N.lt_le_pred in H; rewrite N.le_lteq in H; destruct H; (* C:regular *)
             [simpl in H|rewrite H; reflexivity] (* C:regular *)
         end. (* C:regular *)
  (* all statements now contain a contradiction *)
  (* discriminate doesn't solve this, however *)
  (* demonstrate the contradiction manually *)
  4: edestruct N.nlt_0_r; eassumption. (* C:regular *)
  all: rewrite N.le_ngt in *. (* C:regular *)
  all: tauto. (* C:regular *)
Qed.
(* CATEGORY: END *)

(* Pain points:
   - "mod 2^32" gets attached to everything
     => solution: use xplus/xminus as much as possible
        staying inside the group operations of modular arithmetic
        keeps things working
   - conditional instructions duplicate program proofs
     => solution: use repeat (discriminate + step)
   - "s [Ⓑv := a] v" should be a, but isn't easily turned into a
     => solution: rewrite setmem_1,update_updated
   - subtraction adds 2^32 (for modular arithmetic)
     => solution: use (a _⊖_ b) := a ⊕ ⊖b where ⊖ denotes modular inverse
   - Ⓓ, Ⓜ frequently require existentials to extract
     => solution: use vnum/vmem
   - (related to the previous) Ⓓ, Ⓜ are secretly dynamic types
     => solution: use vnum/vmem, which is secretly a type cast
   - It's easy to construct "impossible states" (i.e. VaN 32 2^64)
     => solution: prove that the program is well-typed to extract types
 *)
