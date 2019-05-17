Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
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

Definition memset_bytedup b :=
  let c := b mod (2 ^ 8)
  in c .| c<<8 .| c<<16 .| c<<24.

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
  rewrite N.add_0_r.
  (* admitting s=s mod _ *)
  admit.
  unfold memfilled.
  intros.
  destruct i; inversion H3.
  destruct PRE.
  destruct H.
  intuition.
  rewrite H,H0,H1,H2.
  exists x1,n,s,0,x0.
  intuition.
  (* admitting s=s mod _ *)
  admit.
  unfold memfilled.
  intros.
  destruct i; inversion H3.

  destruct PRE.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  intuition.
  step. step. step. step.
  inversion BC1.
  inversion BC0.
  step.
  inversion BC1.
  step.
  step.
  step.
  step.
  intuition.
  unfold memset_bytedup.
  Search N.modulo.
  repeat rewrite (N.mod_small _ (2^32)).
  rewrite H5.
  repeat rewrite mod_same.
  (* admitting bitwise arithmetic *)
  admit.
  compute.
  intros.
  inversion H7.
  (* admitting more arithmetic *)
  admit.
  admit.
  rewrite H.
  econstructor.
  exists x1,x2,x3.
  econstructor.
  intuition.
  (* arith *)
  admit.
  repeat step.
  do 3 econstructor.
  exists (x3 ⊕ 1).
  econstructor.
  intuition.
  rewrite H4.
  Search N.add N.modulo.
  repeat rewrite N.add_mod_idemp_r.
  repeat rewrite N.add_mod_idemp_l.
  rewrite N.add_assoc.
  reflexivity.
  compute.
  intros.
  inversion H7.
  compute.
  intros.
  inversion H7.
  rewrite H6.
  Locate "⊖".
  Print N.sub.
  repeat econstructor; auto.
  rewrite H4.
  Search N.modulo N.add.
  repeat rewrite N.add_mod_idemp_l.
  repeat rewrite N.add_mod_idemp_r.
  Search N.add eq.
  Search (_ + _ = _ + _).
  Locate "Ⓓ".
  Search (VaN _ _ = VaN _ _).
  assert (valinj : forall a b, a=b -> Ⓓa = Ⓓb).
  intros.
  rewrite H7.
  reflexivity.
  apply valinj.
  Search N.modulo N.add.
  repeat rewrite <- N.add_assoc.
  rewrite N.add_1_l.
  rewrite N.sub_1_r.
  Search N.succ N.pred.
  rewrite N.succ_pred.
  Search N.add N.modulo.
  repeat rewrite N.add_assoc.
  simpl.
  repeat rewrite (N.add_comm _ (N.pos (2^32))).
  Search N.modulo N.add.
  repeat rewrite <- N.add_assoc.
  rewrite mod_add_l.
  repeat rewrite N.add_mod_idemp_l.
  rewrite N.add_assoc.
  reflexivity.
  Locate "≠".
  compute. intros. inversion H7.
  compute. intros. inversion H7.
  rewrite N.add_comm.
  destruct x1.
  compute. intros. inversion H7.
  red.
  intros.
  inversion H7.
  compute. intros. inversion H7.
  compute. intros. inversion H7.
  compute. intros. inversion H7.
  unfold memfilled in H8.
  unfold memfilled.
  intros.
  (* dealing with store operations *)
  destruct (N.eq_decidable i x3); subst.
  rewrite <- H5.
  (* this should be trivial, but isn't *)
  admit.
  destruct (N.lt_decidable i x3); subst.
  rewrite <- (H8 i); auto.
  (* again, should be trivial, isn't *)
  admit.
  (* arithmetic *)
  admit.
  (* duplicate goals from conditionals *)
  admit.
  admit.
  admit.

  (* main loop *)
  admit.

  (* end loop *)
  admit.
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