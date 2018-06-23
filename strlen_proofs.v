(* Example proofs using CoqBAP for Intel x86 Architecture
 *
 * Copyright (c) 2018 Kevin W. Hamlen
 * Computer Science Department
 * The University of Texas at Dallas
 *
 * Any use, commercial or otherwise, requires the express permission of
 * the author.
 *
 * To run this module, first load the BapSyntax, BapInterp, BapStatics,
 * Bap_i386, and strlen_i386 modules, and compile each (in that order)
 * using menu option Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Bap_i386.
Require Import strlen_i386.

Import BAPx86.
Import X86Notations.
Open Scope N.


(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the BAP_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strlen_welltyped: welltyped_prog x86typctx strlen_i386.
Proof.
  BAP_typecheck.
Qed.

(* Example #2: Memory safety
   Strlen contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem strlen_preserves_memory:
  forall RW s m n s' x,
  exec_prog RW strlen_i386 0 s m n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply prog_noassign_inv; [|exact H].
  intro a. destruct a as [|a]. discriminate 1.
  repeat first [ exact I | destruct a as [a|a|] | simpl; (repeat split); discriminate 1 ].
Qed.



(* Injections on certain data types occur frequently in proofs.  Some versions of Coq check
   injection-heavy proofs very slowly (at Qed).  This slow-down can be avoided by sequestering
   the most prevalent injections into lemmas, which we do here. *)
Lemma inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                     Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Create a case distinction between unfinished and not-unfinished program states.
   "Unfinished" programs are those whose starting states were not provided a sufficiently
   high recursion limit to fully evaluate one or more IL blocks.  A real CPU has no such
   recursion limit, so we don't usually care about such states.  Proof goals therefore
   tend to have the form "if not unfinished, then <some correctness property>". *)
Lemma fin_dec: forall x, {x = Some Unfinished} + {x <> Some Unfinished}.
Proof.
  intro. destruct x; [destruct e|]; first [ left;reflexivity | right;discriminate 1].
Qed.


(* Example #3: Architectural calling convention compliance
   Strlen does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strlen_preserves_ebx:
  forall RW s m n s' x,
  exec_prog RW strlen_i386 0 s m n s' x -> s' R_EBX = s R_EBX.
Proof.
  intros. eapply prog_noassign_inv; [|exact H].
  intro a. destruct a as [|a]. discriminate 1.
  repeat first [ exact I | destruct a as [a|a|] | simpl; (repeat split); discriminate 1 ].
Qed.

Definition strlen_esp_inv (esp:N) (mem:addr->N) (x:exit) (s':store) :=
  match x with Exit a =>
    if N.eq_dec a (getmem LittleE 4 mem esp) then True
    else s' R_ESP = Some (VaN esp 32)
  | _ => True
  end.

Lemma strlen_stmt_esp:
  forall y u s' mem x a' (PRE: y = Some (VaN u 32)) (XS: s' R_ESP = y),
  strlen_esp_inv u mem (match x with Some e => e | None => Exit a' end) s'.
Proof.
  intros. rewrite <- XS in PRE. unfold strlen_esp_inv.
  destruct x; [ destruct e; try exact I | ].
  all: destruct (N.eq_dec _ _); first [ exact I | exact PRE ].
Qed.

Theorem strlen_preserves_esp:
  forall RW s esp mem m n s' x
         (ESP0: s R_ESP = Some (VaN esp 32)) (MEM0: s V_MEM32 = Some (VaM mem 32))
         (RET: strlen_i386 (getmem LittleE 4 mem esp) = None)
         (XP: exec_prog RW strlen_i386 0 s m n s' x),
  strlen_esp_inv esp mem x s'.
Proof.
  intros. pattern x,s',n.
  eapply prog_inv_reachable. exact XP.
  unfold strlen_esp_inv. destruct (N.eq_dec _ _). exact I. assumption.

  intros.
  unfold strlen_esp_inv in PRE. destruct (N.eq_dec a1 _) as [EQ|NE] in PRE.
    rewrite <- EQ, IL in RET. discriminate RET.
  apply strlen_preserves_memory in XP0. rewrite <- XP0 in MEM0.
  clear s n s' x ESP0 RET XP NE LT XP0 XP'.
  destruct a1 as [|a]; repeat first [ discriminate IL | destruct a as [a|a|] ].
  all: apply inj_prog_stmt in IL; destruct IL; subst sz q; simpl.

  all: try (
    apply (noassign_inv R_ESP) in XS;
    [ apply (strlen_stmt_esp (s1 R_ESP)); assumption
    | simpl; repeat split; discriminate 1 ]
  ).

  destruct (fin_dec x1) as [FIN|FIN]. subst x1. exact I.
  stock_store in XS. simpl_stmt in XS; [|assumption]. destruct XS. subst x1.
  unfold strlen_esp_inv. destruct (N.eq_dec _ _).
    exact I.
    contradict n. reflexivity.
Qed.



(* Example #4: Partial correctness
   At termination, strlen returns (in EAX) a value k that satisfies the following:
   (1) p <= k,
   (2) no memory byte at addresses in the interval [p, p+k) is nil, and
   (3) the byte at address p+k is nil,
   where p is the address stored at [ESP+4] on entry. *)

Definition ones (b n:N) := N.iter n (fun x => x * 2^b + 1) 0.

Lemma land_lohi_0:
  forall x y n, x < 2^n -> N.land x (N.shiftl y n) = 0.
Proof.
  intros. apply N.bits_inj_0. intro m. rewrite N.land_spec. destruct (N.lt_ge_cases m n).
    rewrite N.shiftl_spec_low. apply Bool.andb_false_r. assumption.
    erewrite bound_hibits_zero. reflexivity. exact H. assumption.
Qed.

Remark N_neq0_gt0: forall n, n<>0 <-> n>0.
Proof.
  split; intro.
    destruct n. contradict H. reflexivity. reflexivity.
    destruct n. discriminate H. discriminate 1.
Qed.

Remark le_div:
  forall a b c, a<=b -> a/c <= b/c.
Proof.
  intros.
  destruct c. destruct a; destruct b; reflexivity.
  intro H2. apply H, N.lt_gt. eapply N.lt_le_trans.
  rewrite (N.div_mod' b (N.pos p)) at 1.
  apply N.add_lt_mono_l. eapply (N.lt_lt_add_r _ _ (a mod N.pos p)). apply N.mod_lt. discriminate 1.
  rewrite N.add_assoc, <- N.mul_succ_r. rewrite (N.div_mod' a (N.pos p)) at 2.
  apply N.add_le_mono_r, N.mul_le_mono_l, N.le_succ_l, N.gt_lt, H2.
Qed.

Lemma unroll_Niter:
  forall {A:Type} f n (x:A), N.iter (N.succ n) f x = f (N.iter n f x).
Proof.
  intros. do 2 rewrite N2Nat.inj_iter. rewrite N2Nat.inj_succ. reflexivity.
Qed.

Lemma ones_succ:
  forall n w, ones n (N.succ w) = (ones n w) * 2^n + 1.
Proof.
  intros. unfold ones at 1. rewrite unroll_Niter. reflexivity.
Qed.

Lemma ones_succ_top:
  forall w n, ones w (N.succ n) = ones w n + 2^(w*n).
Proof.
  intros. induction n using N.peano_ind.
    rewrite N.mul_0_r. reflexivity.
    rewrite ones_succ, ones_succ, N.mul_succ_r, N.pow_add_r, <- N.add_assoc,
            (N.add_comm 1), N.add_assoc, <- N.mul_add_distr_r, <- IHn, ones_succ.
    reflexivity.
Qed.

Lemma ones_split:
  forall w i j, ones w (i+j) = (ones w i) + (ones w j) * 2^(w*i).
Proof.
  intros. revert i. induction j using N.peano_ind; intro.
    rewrite N.mul_0_l, N.add_0_r, N.add_0_r. reflexivity.
    rewrite ones_succ, <- N.add_succ_comm, N.mul_add_distr_r, <- N.mul_assoc,
            <- N.pow_add_r, (N.add_comm w), <- N.mul_succ_r, (N.add_comm _ (1*_)), N.add_assoc,
            N.mul_1_l, <- ones_succ_top.
    apply IHj.
Qed.

Lemma split_digit: forall m n p, 0 < m -> m*n <= p -> p - n = p - m*n + (m-1)*n.
Proof.
  intros. rewrite N.mul_sub_distr_r. rewrite N.add_sub_assoc.
    rewrite N.sub_add by assumption. rewrite N.mul_1_l. reflexivity.
    apply N.mul_le_mono_nonneg_r. apply N.le_0_l. apply N.lt_pred_le. assumption.
Qed.

Lemma ones_bound:
  forall p x, ones (N.pos p) x < 2^(N.pos p * x).
Proof.
  intros. induction x using N.peano_ind.
    apply N_lt_0_pow2.
    rewrite ones_succ_top, N.mul_succ_r, N.pow_add_r. eapply N.lt_le_trans.
      eapply N.add_lt_le_mono. exact IHx. reflexivity.
      rewrite <- (N.mul_1_l (2^_)) at -3. rewrite <- N.mul_add_distr_r, N.mul_comm. apply N.mul_le_mono_nonneg_l.
        apply N.le_0_l.
        change (1+1) with (2^1). apply N.pow_le_mono_r. discriminate 1. destruct p; discriminate 1.
Qed.

Lemma add_sub_mod_le: forall x y z, z <= y -> (x + (y-z)) mod y < x -> z <= x.
Proof.
  intros. destruct (N.le_gt_cases y (x+(y-z))).
    apply (N.add_le_mono_r _ _ (y-z)). rewrite N.add_sub_assoc, N.add_comm, N.add_sub. assumption. assumption.
    rewrite N.mod_small in H0 by assumption. apply (N.lt_le_trans _ _ (x+(y-z))) in H0.
      contradict H0. apply N.lt_irrefl.
      apply N.le_add_r.
Qed.

Lemma le_add_sub_mod:
  forall x y z, 0 < z -> x <= (x + (2^y-z)) mod 2^y -> x < z.
Proof.
  intros. apply N.nle_gt. intro H1. apply H0. apply N.lt_gt.
  rewrite N.add_sub_assoc by (
    etransitivity; [exact H1|]; etransitivity; [exact H0|]; eapply N.lt_le_incl, N.mod_upper_bound, N.pow_nonzero; discriminate 1).
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc by exact H1.
  rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate 1).
  rewrite N.mod_small by (
    eapply N.le_lt_trans; [apply N.le_sub_l|]; eapply N.le_lt_trans; [exact H0|]; apply N.mod_upper_bound, N.pow_nonzero; discriminate 1).
  apply N.sub_lt; assumption.
Qed.

Lemma sub_lnot: forall x w, x < 2^w ->
  (2^w + (2^w - x) mod 2^w - 1) mod 2^w = N.lnot x w.
Proof.
  intros.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc by apply (N.le_succ_l 0), N_lt_0_pow2.
  rewrite <- (N.mod_small (_-1) (2^w)) by (apply N.sub_lt; [ apply (N.le_succ_l 0), N_lt_0_pow2 | apply N.lt_0_1 ]).
  rewrite <- N.add_mod by (apply N.pow_nonzero; discriminate 1).
  rewrite <- (N.succ_pred (2^w)) at 1 by (apply N.pow_nonzero; discriminate 1).
  rewrite <- N.add_1_l.
  rewrite <- (N.add_sub_assoc 1) by apply N.lt_le_pred, H.
  rewrite (N.add_comm 1), <- (N.add_assoc _ 1).
  rewrite N.add_sub_assoc, (N.add_comm 1) by apply (N.le_succ_l 0), N_lt_0_pow2.
  rewrite N.add_sub.
  rewrite N.add_mod, N.mod_same, N.add_0_r, N.mod_mod by (apply N.pow_nonzero; discriminate 1).
  rewrite N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply N.lt_pred_l, N.pow_nonzero; discriminate 1 ]).
  rewrite <- N.ones_equiv.
  symmetry. destruct x. rewrite N.sub_0_r. apply N.lnot_0_l.
  apply N.lnot_sub_low. apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

Lemma bytes_pos_lobound:
  forall mem i a (WTM: welltyped_memory mem)
         (H: forall j, j < i -> mem (a + j) > 0),
  ones Mb i <= getmem LittleE i mem a.
Proof.
  intros mem i a WTM. revert a. induction i using N.peano_ind; intros.
    reflexivity.
    rewrite ones_succ, getmem_succ, lor_plus.
      rewrite N.add_comm. apply N.add_le_mono.
        apply N.lt_pred_le, N.gt_lt. rewrite <- (N.add_0_r a). apply H. apply N.lt_0_succ.
        rewrite N.shiftl_mul_pow2. apply N.mul_le_mono_nonneg_r.
          apply N.le_0_l.
          apply IHi. intros. rewrite N.add_succ_comm. apply H. apply -> N.succ_lt_mono. assumption.
      apply land_lohi_0, WTM.
Qed.

Lemma below_ones:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: getmem LittleE w mem a < ones Mb w),
  exists i, i < w /\ mem (a+i) = 0.
Proof.
  intros mem w a WTM. revert a. induction w using N.peano_ind; intros.
    contradict GM. apply N.nlt_0_r.
    rewrite ones_succ, getmem_succ in GM. destruct (mem a) eqn:M0.
      exists 0. split. apply N.lt_0_succ. rewrite N.add_0_r. exact M0.
      destruct (IHw (N.succ a)) as [i [LOI MI]].

        apply (N.mul_lt_mono_pos_r (2^Mb)). reflexivity.
        rewrite <- N.shiftl_mul_pow2.
        apply (N.le_lt_add_lt 1 (N.pos p)). destruct p; discriminate 1.
        rewrite N.add_comm, <- lor_plus. exact GM.
        apply N.bits_inj_0. intro n. rewrite N.land_spec. destruct (N.lt_ge_cases n Mb) as [LO|HI].
          rewrite N.shiftl_spec_low. apply Bool.andb_false_r. exact LO.
          rewrite bound_hibits_zero with (w:=Mb). reflexivity. rewrite <- M0. apply WTM. exact HI.

        exists (N.succ i). split.
          revert LOI. apply N.succ_lt_mono.
          rewrite <- N.add_succ_comm. exact MI.
Qed.

Lemma sub1parity:
  forall b x, x > 0 ->
  (x mod 2^b =? 0) = xorb (N.testbit x b) (N.testbit (x-1) b).
Proof.
  intros b x.
  do 2 rewrite N.testbit_odd, N.shiftr_div_pow2.
  rewrite (N.div_mod' x (2^b)) at -2.
  assert (XLO: x mod 2^b < 2^b). apply N.mod_lt, N.pow_nonzero. discriminate 1.
  destruct (x mod 2^b).

  rewrite N.add_0_r, N.mul_comm.
  intro H. apply N.gt_lt in H.
  rewrite N.div_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite <- (N.sub_add (2^b) (_*_)).
  rewrite <- N.add_sub_assoc by apply N.lt_pred_le, N_lt_0_pow2.
  rewrite <- (N.mul_1_l (2^b)) at 4. rewrite <- N.mul_sub_distr_r.
  rewrite N.div_add_l by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (_-_)) by (apply N.sub_lt; [ apply N.lt_pred_le, N_lt_0_pow2 | reflexivity ]).
  rewrite N.add_0_r.
  rewrite N.odd_sub by (eapply N.lt_pred_le, N.mul_lt_mono_pos_r; [ apply N_lt_0_pow2 | exact H ]).
  rewrite N.odd_1. destruct (N.odd (_/_)); reflexivity.

    rewrite <- (N.mul_1_l (2^b)) at 1. apply N.mul_le_mono_pos_r. apply N_lt_0_pow2.
    apply N.lt_pred_le, (N.mul_lt_mono_pos_r (2^b)). apply N_lt_0_pow2. exact H.

  intro.
  rewrite <- N.add_sub_assoc by (destruct p; discriminate 1).
  rewrite N.mul_comm. do 2 rewrite N.div_add_l by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (N.pos _)) by exact XLO.
  rewrite (N.div_small (_-_)) by (eapply N.le_lt_trans; [ apply N.le_sub_l | exact XLO ]).
  rewrite Bool.xorb_nilpotent. reflexivity.
Qed.

Lemma sub11parity:
  forall b x y, y*2^b < x ->
  (x mod 2^b =? 0) = xorb (N.odd y) (xorb (N.testbit x b) (N.testbit (x-(y*2^b + 1)) b)).
Proof.
  intros. rewrite N.sub_add_distr.
  rewrite <- (N.sub_add (y*2^b) x) at -3 by apply N.lt_le_incl, H.
  rewrite N.testbit_odd, N.shiftr_div_pow2.
  rewrite N.mod_add, N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.add_comm _ y), N.odd_add, Bool.xorb_assoc_reverse, <- N.shiftr_div_pow2, <- N.testbit_odd.
  rewrite <- sub1parity by apply N.lt_gt, N.lt_add_lt_sub_r, H.
  rewrite <- Bool.xorb_assoc_reverse, Bool.xorb_nilpotent.
  symmetry. apply Bool.xorb_false_l.
Qed.

Lemma sub_parity:
  forall b w x y z, y*2^b < x/2^w ->
                    z <= x mod 2^w ->
  (x/2^w mod 2^b =? 0) = xorb (N.odd y) (xorb (N.testbit x (b+w)) (N.testbit (x-(z + (y*2^b + 1)*2^w)) (b+w))).
Proof.
  intros.
  do 2 rewrite <- N.div_pow2_bits.
  rewrite (N.div_mod' x (2^w)) at 3.
  rewrite N.sub_add_distr.
  rewrite <- N.add_sub_assoc by assumption.
  rewrite N.mul_comm, N.add_comm.
  rewrite <- N.add_sub_assoc.
  rewrite <- N.mul_sub_distr_r.
  rewrite N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (_-_)) by (eapply N.le_lt_trans; [apply N.le_sub_l | apply N.mod_lt, N.pow_nonzero; discriminate 1]).
  rewrite N.add_0_l.
  apply sub11parity. assumption.

  apply N.mul_le_mono_pos_r. apply N_lt_0_pow2.
  rewrite N.add_1_r. apply N.le_succ_l. assumption.
Qed.

Lemma extract_bit:
  forall b w xw x y z, y*2^b < x/2^w ->
                       z <= x mod 2^w ->
                       b+w < xw ->
                       N.odd y = true ->
  (x/2^w mod 2^b =? 0) =
  N.testbit (N.lxor (N.lnot x xw) (x - (z + (y*2^b + 1)*2^w))) (b+w).
Proof.
  intros.
  rewrite (sub_parity b w x y z); try assumption.
  rewrite N.lxor_spec, <- Bool.xorb_assoc.
  rewrite N.lnot_spec_low by assumption.
  rewrite H2. reflexivity.
Qed.

Lemma testbit_ones_true:
  forall w n b, b<>0 -> n < w -> N.testbit (ones b w) (b*n) = true.
Proof.
  intros w n b H0 H.

  destruct b as [|b']. contradict H0. reflexivity. clear H0.

  rewrite <- (N.sub_add n w) by apply N.lt_le_incl, H.
  destruct (w-n) eqn:H1. contradict H. apply N.nlt_ge, N.sub_0_le. assumption.
  rewrite <- (N.succ_pred (N.pos p)) by discriminate 1.
  rewrite N.add_comm, ones_split, ones_succ.
  rewrite <- lor_plus by (rewrite <- N.shiftl_mul_pow2; apply land_lohi_0, ones_bound).
  rewrite N.lor_spec.
  erewrite bound_hibits_zero; [| apply ones_bound | reflexivity].
  rewrite N.mul_pow2_bits_high by reflexivity.
  rewrite N.sub_diag.
  rewrite <- lor_plus by (rewrite N.land_comm, <- N.shiftl_mul_pow2; change 1 with (2^0); apply land_lohi_0, N.pow_lt_mono_r; reflexivity).
  rewrite N.lor_spec.
  rewrite N.mul_pow2_bits_low by reflexivity.
  reflexivity.
Qed.

Lemma testbit_onesm1_true:
  forall w n b, b<>0 -> n<>0 -> n<w -> N.testbit (ones b w - 1) (b*n) = true.
Proof.
  intros.
  destruct w. contradict H1. apply N.nlt_0_r.
  rewrite <- (N.succ_pred (N.pos p)) by discriminate 1.
  rewrite ones_succ, N.add_sub. rewrite <- (N.mul_1_r b) at 2.
  destruct n. contradict H0. reflexivity.
  rewrite N.mul_pow2_bits_high by (apply N.mul_le_mono_nonneg_l; [ apply N.le_0_l | destruct p0; discriminate 1]).
  rewrite <- N.mul_sub_distr_l, N.sub_1_r. apply testbit_ones_true. assumption.
  apply -> N.pred_lt_mono. assumption. discriminate 1.
Qed.

Theorem noborrow_nonil:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: ones Mb w <= getmem LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE w mem a) (Mb*w))
                              (getmem LittleE w mem a - ones Mb w))
                      (ones Mb w - 1) = 0)
         i (IW: i < w),
  mem (a + i) > 0.
Proof.
  intros until i. intro IW.
  assert (JW:=N.le_refl w). revert JW i IW. generalize w at -2 as i. induction i using N.peano_ind; intros IW j JI.
  contradict JI. apply N.nlt_0_r.
  specialize (IHi (N.le_trans _ _ _ (N.le_succ_diag_r i) IW)).
  apply N.lt_succ_r, N.lt_eq_cases in JI. destruct JI as [JI|JI].
  apply (IHi _ JI). subst j.
  apply N.le_lteq in IW. destruct IW as [IW|IW].

  assert (H:=N.add_sub w i). rewrite N.add_comm in H. revert H.
  rewrite <- N.add_sub_assoc by (apply N.lt_le_incl, N.lt_succ_l; exact IW).
  generalize (w-i) as j. intros. subst w.
  destruct j as [|j]. contradict IW. rewrite N.add_0_r. apply N.nlt_succ_diag_l.
  rewrite <- (N.succ_pos_pred j) in *. destruct (Pos.pred_N j) as [|j'].
  contradict IW. rewrite N.add_1_r. apply N.lt_irrefl.
  clear j IW. rename j' into j.

  apply N_neq0_gt0, N.eqb_neq.
  rewrite ones_split in TST at 1. rewrite ones_succ in TST.
  apply (f_equal (fun x => N.testbit x (Mb + Mb*i))) in TST.
  rewrite N.bits_0, N.land_spec in TST.
  rewrite <- extract_bit in TST.
  rewrite <- TST.
  rewrite getmem_split, <- N.shiftr_div_pow2, N.shiftr_lor.
  rewrite N.shiftr_shiftl_l by reflexivity.
  rewrite N.sub_diag, N.shiftl_0_r, N.shiftr_div_pow2.
  rewrite N.div_small by apply getmem_bound, WTM.
  rewrite N.lor_0_l, getmem_succ, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.lor_0_r.
  rewrite N.mod_small by apply WTM.
  rewrite <- (N.mul_1_r Mb) at 2. rewrite <- N.mul_add_distr_l. rewrite testbit_onesm1_true.
    rewrite Bool.andb_true_r. reflexivity.
    discriminate 1.
    rewrite N.add_1_l. apply N.succ_0_discr.
    rewrite N.add_comm, <- (N.add_0_r (_+_)), <- N.add_1_l, N.add_assoc. apply N.add_lt_mono_l. reflexivity.

  rewrite ones_split, getmem_split in GM.
  rewrite lor_plus in GM by apply land_lohi_0, getmem_bound, WTM.
  rewrite N.shiftl_mul_pow2 in GM.
  apply (N.div_le_mono _ _ (2^(Mb*i))) in GM; [|apply N.pow_nonzero; discriminate 1].
  do 2 rewrite N.div_add in GM by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in GM by apply ones_bound.
  rewrite N.div_small in GM by apply getmem_bound, WTM.
  apply N.le_succ_l. rewrite <- N.add_1_r, <- ones_succ, getmem_split.
  rewrite lor_plus by apply land_lohi_0, getmem_bound, WTM.
  rewrite N.shiftl_mul_pow2.
  rewrite N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small by apply getmem_bound, WTM.
  exact GM.

  rewrite getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.mod_small by apply getmem_bound, WTM.
  rewrite N.lor_0_r. apply bytes_pos_lobound. exact WTM. exact IHi.

  rewrite N.add_comm, N.mul_add_distr_l. apply N.add_lt_mono_l.
  rewrite N.mul_succ_r. rewrite <- (N.add_0_l Mb) at 1. apply N.add_lt_mono_r.
  apply N.mul_pos_pos; reflexivity.

  rewrite <- N.bit0_odd, <- (N.mul_0_r Mb). apply testbit_ones_true.
    discriminate 1.
    reflexivity.

  subst w. clear TST IHi. revert a GM. induction i using N.peano_ind; intros.
    apply N.lt_gt. eapply N.lt_le_trans. apply N.lt_0_1. rewrite N.add_0_r. etransitivity.
      exact GM.
      rewrite getmem_succ, N.lor_0_r. reflexivity.

    rewrite <- N.add_succ_comm. apply IHi.
    rewrite getmem_succ, ones_succ in GM.
    apply (N.div_le_mono _ _ (2^Mb)) in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_add_l in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_small, N.add_0_r in GM; [|reflexivity].
    etransitivity. exact GM.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor, N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r, shiftr_low_pow2, N.lor_0_l.
      reflexivity. apply WTM. reflexivity.
Qed.

Lemma lsd_pos:
  forall b x, b<>0 -> x > 0 -> exists n, x/2^(b*n) mod 2^b > 0.
Proof.
  intros b x B0 X0. exists (N.log2 x / b).
  apply N.lt_gt. apply N.gt_lt in X0. destruct (N.log2_spec x X0) as [LO HI].
  rewrite N.mod_small.
    eapply N.lt_le_trans.
      apply N.lt_0_1.
      erewrite <- N.div_same.
        apply le_div. etransitivity.
          apply N.pow_le_mono_r. discriminate 1. apply N.mul_div_le; assumption.
          assumption.
        apply N.pow_nonzero. discriminate 1.
    eapply N.mul_lt_mono_pos_l. apply N_lt_0_pow2. eapply N.le_lt_trans.
      apply N.mul_div_le, N.pow_nonzero. discriminate 1.
      rewrite <- N.pow_add_r, <- N.mul_succ_r. eapply N.lt_le_trans.
        exact HI.
        apply N.pow_le_mono_r. discriminate 1. apply N.le_succ_l, N.mul_succ_div_gt. exact B0.
Qed.

Theorem borrow_nil:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: ones Mb w <= getmem LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE w mem a) (Mb*w))
                              (getmem LittleE w mem a - ones Mb w))
                      (ones Mb w - 1) > 0),
  exists i, i < w /\ mem (a + i) = 0.
Proof.
  intros.
  destruct w as [|w]. contradict TST. rewrite N.land_0_r. discriminate 1.
  rewrite <- (N.succ_pos_pred w) in *.
  apply (lsd_pos Mb) in TST; [|discriminate 1]. destruct TST as [j TST].

  rewrite <- N.shiftr_div_pow2, N.shiftr_land, <- N.land_ones, <- N.land_assoc in TST.

  destruct j as [|j].
  rewrite N.mul_0_r, (N.shiftr_0_r (_-_)), ones_succ, N.add_sub, <- N.shiftl_mul_pow2, (N.land_comm _ (N.ones _)) in TST.
  rewrite land_lohi_0 in TST by reflexivity.
  rewrite N.land_0_r in TST. discriminate TST.

  rewrite ones_succ in TST at 2.
  rewrite N.add_sub, <- N.shiftl_mul_pow2 in TST.
  rewrite N.shiftr_shiftl_r in TST by (rewrite <- (N.mul_1_r Mb) at 1; apply N.mul_le_mono_l; destruct j; discriminate 1).
  rewrite <- N.mul_pred_r in TST.
  destruct (N.le_gt_cases (N.pos j) (Pos.pred_N w)) as [JW|JW]; [|
    rewrite (shiftr_low_pow2 (ones _ _)) in TST by (eapply N.lt_le_trans; [ apply ones_bound | apply N.pow_le_mono_r ; [ discriminate 1 | apply N.mul_le_mono_l, N.lt_le_pred, JW] ]);
    rewrite N.land_0_l, N.land_0_r in TST; discriminate TST ].
  rewrite <- (N.sub_add (N.pos j) (Pos.pred_N w)) in TST at 5 by exact JW.
  rewrite N.add_comm, ones_split, (N.shiftr_div_pow2 (_+_)) in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 2 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb), N.pow_add_r, N.mul_assoc in TST.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite (ones_succ_top _ (N.pred _)) in TST.
  rewrite <- (N.mul_1_l (2^(_*N.pred _))) in TST at 1.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in TST by apply ones_bound.
  rewrite N.land_ones in TST.
  rewrite N.mod_add in TST by (apply N.pow_nonzero; discriminate 1).
  change (_ mod _) with (N.ones 1) in TST.
  rewrite N.land_ones, <- (N.div_1_r (N.shiftr _ _)) in TST.
  change 1 with (2^0) in TST at 1.
  rewrite <- N.testbit_spec', N.shiftr_spec', N.add_0_l in TST.
  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST at 4 by (
    etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
  rewrite N.add_comm, ones_split in TST.
  rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
  rewrite ones_succ in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb) in TST.

  destruct (N.le_gt_cases (ones Mb (N.pred (N.pos j))) (getmem LittleE (N.pred (N.pos j)) mem a)) as [LOJ|LOJ].

  rewrite <- extract_bit in TST.

  exists (N.pred (N.pos j)). split.

    apply N.lt_succ_r, N.le_le_pred. exact JW.

    rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST by (
      etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
    rewrite N.add_comm in TST.
    rewrite getmem_split in TST.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor in TST.
    rewrite shiftr_low_pow2 in TST by apply getmem_bound, WTM.
    rewrite N.shiftr_shiftl_l in TST by reflexivity.
    rewrite N.lor_0_l, N.sub_diag, N.shiftl_0_r in TST.
    rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
    rewrite getmem_succ in TST.
    rewrite lor_plus in TST by apply land_lohi_0, WTM.
    rewrite N.shiftl_mul_pow2 in TST.
    rewrite N.mod_add in TST by (apply N.pow_nonzero; discriminate 1).
    rewrite N.mod_small in TST by apply WTM.
    destruct (mem _). reflexivity. discriminate TST.

  apply N.le_succ_l. rewrite <- N.add_1_r, <- ones_succ.
  rewrite <- N.sub_succ_l by apply N.le_le_pred, JW.
  rewrite <- (N.add_0_l (ones _ _)).
  rewrite <- (N.div_small (ones Mb (N.pred (N.pos j))) (2^(Mb * N.pred (N.pos j)))) by apply ones_bound.
  rewrite <- N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite <- ones_split.
  rewrite N.add_sub_assoc by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, N.add_sub.
  apply le_div. exact GM.

  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones.
  rewrite N.mod_small by apply getmem_bound, WTM.
  rewrite N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.lor_0_r. exact LOJ.

  rewrite N.mul_succ_r, N.add_comm.
  apply N.add_lt_mono_r, N.mul_lt_mono_pos_l. reflexivity.
  eapply N.lt_le_trans. apply N.lt_pred_l. discriminate 1. exact JW.

  rewrite <- (N.succ_pred (_-_)), ones_succ.
  change (2^Mb) with (2*2^N.pred Mb).
  rewrite N.mul_comm, <- N.mul_assoc, N.add_comm. apply N.odd_add_mul_2.
  intro H. apply JW, N.lt_gt. eapply N.le_lt_trans. apply N.sub_0_le. exact H. apply N.lt_pred_l. discriminate 1.

  destruct (below_ones _ _ _ WTM LOJ) as [k [KW MK]].
  exists k. split.
    eapply N.lt_le_trans.
      exact KW.
      apply N.le_le_pred, N.le_le_succ_r, JW.
    exact MK.
Qed.


(* Tactic: destN n until T hyp:H
   Keep destructing n:N until either n is a completed numeric constant (provided as an
   equality in hypothesis H) or tactic T solves the goal.  This yields a set of subgoals
   in which n equals the various constants admitted by T.  Typical usage:
     destN a until (discriminate IL) hyp:ADDR.
   where IL is an instruction lookup of the form (IL: program a = Some _). *)
Tactic Notation "destN" constr(n) "until" tactic(T) "eqn" ":" ident(H) :=
  let p := fresh n in
  destruct n as [|p] eqn:H;
  [ try solve [T]
  | repeat first [ solve[T] | destruct p as [p|p|] ] ].

(* Tactic: focus_addr H n
   Shelve all goals except the goal in which hypothesis H has the form (H: _ = n).
   This retrieves the subgoal for address n from a sea of arbitrarily ordered goals.
   Use vernacular command "Unshelve" to pull back all the shelved goals afterward. *)
Tactic Notation "focus_addr" hyp(H) constr(n) :=
  match type of H with _ = n => idtac | _ => shelve end.

Definition nilfree (m:addr->N) (p:addr) (k:N) :=
  p <= k /\ forall i, p <= i -> i < k -> m i > 0.

Definition strlen_inv_set (m:addr->N) (esp:N) (a:addr) (_:exit) (s:store) (_:nat) :=
  match a with
  | 0 => Some True
  | 38 => Some (∃ eax edx, s R_EAX = Ⓓeax /\ s R_EDX = Ⓓedx /\ nilfree m (m Ⓓ[esp+4]) eax /\ edx < 4)
  | 49 | 75 | 101 | 127 => Some (∃ eax, s R_EAX = Ⓓeax /\ nilfree m (m Ⓓ[esp+4]) eax /\ s R_EDX = Ⓓ0)
  | 153 => Some (∃ eax, s R_EAX = Ⓓeax /\ nilfree m (m Ⓓ[esp+4]) (eax-4) /\ 4 <= eax /\
                         s R_ECX = Ⓓ(2^32 + m Ⓓ[eax-4] ⊖ ones 8 4) /\
                         exists i, m Ⓓ[esp+4] <= i < eax /\ m i = 0)
  | 182 => Some (∃ eax, s R_EAX = Ⓓeax /\ nilfree m (m Ⓓ[esp+4]) eax /\ m eax = 0)
  | 186 => Some (∃ eax, s R_EAX = Ⓓeax /\ nilfree m (m Ⓓ[esp+4]) ((m Ⓓ[esp+4])+eax) /\ m ((m Ⓓ[esp+4])+eax) = 0)
  | _ => None
  end.

Definition strlen_postcond (mem:addr->N) (esp:N) (_:addr) (_:exit) (s:store) (_:nat) :=
  s R_ESP = Some (VaN (esp+4) 32) /\
  let p := getmem LittleE 4 mem (esp+4) in
  exists eax, s R_EAX = Some (VaN eax 32) /\
              mem (p + eax) = 0 /\
              forall i, i < eax -> mem (p+i) > 0.

Definition strlen_inv (mem:addr->N) (esp:N) :=
  x86_subroutine_inv strlen_i386 (strlen_inv_set mem esp) (strlen_postcond mem esp) (getmem LittleE 4 mem esp).

Theorem strlen_partial_correctness:
  forall RW s esp mem m n s' x
         (HI: ~ RW false mem 32 (2^32 - 1)%N)
         (MDL0: models x86typctx s)
         (ESPLO: esp + 8 <= 2^32)
         (ESP0: s R_ESP = Some (VaN esp 32)) (MEM0: s V_MEM32 = Some (VaM mem 32))
         (RET: strlen_i386 (getmem LittleE 4 mem esp) = None)
         (XP0: exec_prog RW strlen_i386 0 s m n s' x),
  match strlen_inv mem esp x s' n with Some P => P | None => True end.
Proof.
  intros.
  destruct x as [|a'|i]; try exact I.
  eapply prog_inv. exact XP0.
  unfold strlen_inv. destruct (getmem _ _ _ _). discriminate RET. exact I.
  intros.
  assert (MEM: s1 V_MEM32 = Some (VaM mem 32)).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  assert (ESP: strlen_esp_inv esp mem (Exit a1) s1).
    eapply strlen_preserves_esp. exact ESP0. exact MEM0. exact RET. exact XP.
  assert (MDL: models x86typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strlen_welltyped. exact XP.
  unfold strlen_esp_inv in ESP. unfold strlen_inv, x86_subroutine_inv in PRE.
  clear s MDL0 MEM0 ESP0 XP XP0.
  assert (WTM:=x86_wtm MDL MEM). simpl in WTM.

  destruct (N.eq_dec a1 _). subst a1. eapply NISStep. intros. rewrite IL in RET. discriminate RET. clear n0.
  destN a1 until (exfalso; exact PRE) eqn:ADDR.
  all:unfold strlen_inv_set in PRE.

  Local Ltac step := time x86_step.

  all: focus_addr ADDR 0. clear PRE.
  step. rewrite N.mod_small by (eapply N.lt_le_trans; [|exact ESPLO]; apply N.add_lt_mono_l; reflexivity).
  step.
  step.
  assert (NF0: nilfree mem (mem Ⓓ[esp+4]) (mem Ⓓ[esp+4])). split.
    reflexivity.
    intros i H1 H2. exfalso. apply H1, N.lt_gt, H2.
  step. eexists. split. reflexivity. split. exact NF0. apply Neqb_ok in BC. rewrite <- BC. reflexivity.
  step. clear BC BC0.
  step. assert (LM1: mem Ⓓ[esp+4] + 1 < 2^32).
    apply N.lt_nge. intro H. apply HI.
    replace (mem Ⓓ[esp+4]) with (2^32-1) in ACC. apply (ACC 0). reflexivity.
    apply N.le_antisymm.
      apply N.le_sub_le_add_r. exact H.
      rewrite <- N.pred_sub. apply N.lt_le_pred, getmem_bound, WTM.
  step. eexists. split. reflexivity. split. exact NF0. symmetry. apply Neqb_ok, BC.
  assert (NF1: nilfree mem (mem Ⓓ[esp+4]) (mem Ⓓ[esp+4]+1)). split.
    apply N.le_add_r.
    intros i H1 H2. replace i with (mem Ⓓ[esp+4]).
      apply N_neq0_gt0, N.neq_sym, N.eqb_neq, BC.
      apply N.le_antisymm. exact H1. apply N.lt_succ_r. rewrite <- N.add_1_r. exact H2.
  clear NF0 BC.
  step.
  step. assert (LM2: mem Ⓓ[ esp + 4] + 1 + 1 < 2^32).
    apply N.lt_nge. intro H. apply HI.
    replace (mem Ⓓ[esp+4]) with (2^32-1-1) in ACC. rewrite N.sub_add in ACC by discriminate 1. apply (ACC 0). reflexivity.
    apply N.add_sub_eq_r. apply N.le_antisymm.
      rewrite <- N.pred_sub. apply N.lt_le_pred. exact LM1.
      apply N.le_sub_le_add_r. exact H.
  step. eexists. split. reflexivity. split. exact NF1. symmetry. apply Neqb_ok. exact BC.
  assert (NF2: nilfree mem (mem Ⓓ[esp+4]) (mem Ⓓ[esp+4]+1+1)). split.
    rewrite <- N.add_assoc. apply N.le_add_r.
    intros i H1 H2. rewrite N.add_1_r in H2. apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      revert i H1 H2. exact (proj2 NF1).
      rewrite H2. apply N_neq0_gt0, N.neq_sym, N.eqb_neq, BC.
  clear NF1 BC.
  step. clear LM1.
  step. rewrite <- (N.land_ones _ 2), lxor_land, N.land_ones by reflexivity.
  step. eexists. split. reflexivity. split. exact NF2. apply Neqb_ok in BC. rewrite BC. reflexivity.
  eexists. eexists. do 2 (split; [reflexivity|]). split. exact NF2. apply N.mod_upper_bound. discriminate 1.
  eexists. eexists. do 2 (split; [reflexivity|]). split. exact NF0. apply N.mod_upper_bound. discriminate 1.

  Unshelve. all: focus_addr ADDR 38. destruct PRE as [eax [edx [EAX [EDX [NF EDX4]]]]].
  step. assert (LM3: eax + 1 < 2^32).
    apply N.lt_nge. intro H. apply HI.
    replace eax with (2^32-1) in ACC. apply (ACC 0). reflexivity.
    apply N.le_antisymm.
      apply N.le_sub_le_add_r. exact H.
      rewrite <- N.pred_sub. apply N.lt_le_pred. exact (x86_regsize MDL EAX).
  step. eexists. split. reflexivity. split. exact NF. symmetry. apply Neqb_ok. exact BC.
  step.
  step. eexists. split. reflexivity. split; [|reflexivity]. split.
    etransitivity. apply (proj1 NF). apply N.le_add_r.
    intros i H1 H2. rewrite N.add_1_r in H2. apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      revert i H1 H2. exact (proj2 NF).
      rewrite H2. apply N_neq0_gt0, N.neq_sym, N.eqb_neq, BC.

  Unshelve. all: match type of ADDR with _=49 => idtac | _=75 => idtac | _=101 => idtac | _=127 => idtac | _ => shelve end.
  all: unfold strlen_inv_set in PRE; destruct PRE as [eax [EAX [NF EDX0]]].
  all:step. all:assert (LM: eax + 4 < 2^32) by (apply N.lt_nge; intro H; apply HI;
    replace (2^32-1) with (eax+(N.pred(2^32) - eax));
    [ apply ACC, (N.add_lt_mono_r _ _ eax); rewrite N.sub_add by apply N.lt_le_pred, (x86_regsize MDL EAX); rewrite N.add_comm; eapply N.lt_le_trans; [|exact H]; reflexivity
    | rewrite N.add_sub_assoc by apply N.lt_le_pred, (x86_regsize MDL EAX); rewrite N.add_comm, N.add_sub; reflexivity ]).
  all:step.
  all:step.
  all:step. all:change 4278124287 with (2^32 - ones 8 4).
  all:step.
  all:step.
  2,4,6,8:apply N.ltb_ge, le_add_sub_mod in BC; [|reflexivity];
  eexists; split; [reflexivity|]; rewrite N.add_sub; split; [exact NF|]; repeat split;
  [ rewrite N.add_comm; apply N.le_add_r
  | rewrite N.add_sub_assoc, N.add_comm by discriminate 1; reflexivity
  | change 32 with (Mb*4) in BC; apply below_ones in BC; [|exact WTM]; destruct BC as [i [I4 NIL]]; exists (eax+i); repeat split;
    [ etransitivity; [ apply (proj1 NF) | apply N.le_add_r ]
    | apply N.add_lt_mono_l; exact I4
    | exact NIL ] ].
  all: apply N.ltb_lt, add_sub_mod_le in BC; [|discriminate 1].
  all: rewrite sub_lnot by apply getmem_bound, WTM.
  all:step.
    all:rewrite N.add_sub_assoc by discriminate 1.
    all:rewrite (N.add_comm _ (2^32)).
    all:rewrite <- N.add_sub_assoc by exact BC.
    all:rewrite N.add_mod, N.mod_same, N.add_0_l, N.mod_mod by (apply N.pow_nonzero; discriminate 1).
    all:rewrite (N.mod_small (_-_)) by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply getmem_bound, WTM ]).
  all:change 16843008 with (ones 8 4 - 1).
  all:step.
  all:step.
  1,3,5,7:apply Neqb_ok in BC0; symmetry in BC0; eexists; split; [reflexivity|]; repeat split;
  [ etransitivity; [ apply (proj1 NF) | apply N.le_add_r ]
  | intros; destruct (N.lt_ge_cases i eax);
    [ apply (proj2 NF); assumption
    | rewrite <- (N.add_sub i eax), N.add_comm, <- N.add_sub_assoc by assumption;
      (apply noborrow_nonil with (w:=4); try assumption);
      apply (N.add_lt_mono_l _ _ eax); rewrite N.add_sub_assoc, N.add_comm, N.add_sub; assumption ]
  | rewrite BC0; reflexivity ].
  all: eexists; split; [reflexivity|]; rewrite N.add_sub; split; [exact NF|]; repeat split;
  [ rewrite N.add_comm; apply N.le_add_r
  | rewrite <- N.add_sub_assoc by exact BC; rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate 1;
    rewrite N.mod_small; [reflexivity|]; eapply N.le_lt_trans; [apply N.le_sub_l | apply getmem_bound,WTM ]
  | change 32 with (Mb*4) in BC0; apply N.eqb_neq, N.neq_sym, N_neq0_gt0, borrow_nil in BC0; try assumption;
    destruct BC0 as [i [I4 NIL]]; exists (eax + i); repeat split;
    [ etransitivity; [ apply (proj1 NF) | apply N.le_add_r ]
    | apply N.add_lt_mono_l, I4
    | exact NIL ] ].

  Unshelve. all:focus_addr ADDR 153. destruct PRE as [eax [EAX [NF [EAX4 [ECX NIL]]]]].
  step.
    rewrite <- N.add_sub_assoc by exact EAX4.
    rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate 1.
    rewrite N.mod_small by (etransitivity; [ apply N.sub_lt; [exact EAX4|reflexivity] | apply (x86_regsize MDL EAX) ]).
  step.
    change 4278124287 with (2^32 - ones 8 4).
    rewrite N.add_comm. rewrite <- N.add_sub_assoc by discriminate 1.
    change (2^32-(2^32-ones 8 4)) with (ones 8 4).
    rewrite N.add_mod_idemp_l by discriminate 1.
    rewrite N.sub_add by (etransitivity; [|apply N.le_add_r]; discriminate 1).
    rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate 1.
    rewrite N.mod_small by apply getmem_bound, WTM.
  step. replace (mem Ⓓ[ eax - 4] mod 2 ^ 8) with (mem (eax-4)) by (
    change 4 with (N.succ 3); rewrite getmem_succ, <- N.land_ones; simpl;
    rewrite N.land_lor_distr_l, N.land_ones, N.land_ones, N.mod_small by apply WTM;
    rewrite N.shiftl_mul_pow2, N.mod_mul, N.lor_0_r by discriminate 1;
    reflexivity ).
  step. eexists. split. reflexivity. split. exact NF. symmetry. apply Neqb_ok. exact BC.
  apply N.eqb_neq, N.neq_sym, N_neq0_gt0 in BC.
  step.
    replace (eax - 4 ⊕ 1) with (eax-3) by (
      change 4 with (3+1);
      rewrite N.sub_add_distr, N.sub_add by (change 1 with (4-3); apply N.sub_le_mono_r, EAX4);
      symmetry; apply N.mod_small;
      eapply N.le_lt_trans; [ apply N.le_sub_l | apply (x86_regsize MDL EAX) ]).
  step. rewrite N.land_diag. replace (mem Ⓓ[eax-4] mod _ >> _) with (mem (eax-3)) by (
    change 4 with (N.succ (N.succ 2));
    rewrite getmem_succ, getmem_succ, <- N.land_ones, N.shiftr_land,
            N.shiftr_lor, N.shiftr_shiftl_l, N.shiftl_0_r by discriminate 1;
    change (N.ones _ >> _) with (N.ones 8);
    rewrite shiftr_low_pow2, N.lor_0_l, N.land_lor_distr_l, N.land_ones, N.mod_small by apply WTM;
    rewrite N.shiftl_mul_pow2, N.land_ones, N.mod_mul, N.lor_0_r by discriminate 1;
    rewrite N.sub_succ_r, N.succ_pred by (eapply N.sub_gt, N.lt_le_trans; [|exact EAX4]; reflexivity);
    reflexivity ).
  assert (NF3: nilfree mem (mem Ⓓ[esp+4]) (eax-3)). split.
    etransitivity. apply (proj1 NF). apply N.sub_le_mono_l. discriminate 1.
    intros i H1 H2. apply N.lt_le_pred in H2. rewrite <- N.sub_succ_r in H2. apply N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      apply (proj2 NF). exact H1. exact H2.
      rewrite H2. exact BC.
  clear NF BC.
  step. eexists. split. reflexivity. split. exact NF3. symmetry. apply Neqb_ok. exact BC.
  apply N.eqb_neq, N.neq_sym, N_neq0_gt0 in BC.
  assert (NF2: nilfree mem (mem Ⓓ[esp+4]) (eax-2)). split.
    etransitivity. apply (proj1 NF3). apply N.sub_le_mono_l. discriminate 1.
    intros i H1 H2. apply N.lt_le_pred in H2. rewrite <- N.sub_succ_r in H2. apply N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      apply (proj2 NF3). exact H1. exact H2.
      rewrite H2. exact BC.
  clear NF3 BC.
  step.
  step.
  step.
    replace (eax - 3 ⊕ 1) with (eax-2) by (
      change 3 with (2+1); rewrite N.sub_add_distr;
      rewrite N.sub_add by (apply N.le_add_le_sub_r; transitivity 4; [ discriminate 1 | exact EAX4 ]);
      symmetry; apply N.mod_small; eapply N.le_lt_trans; [ apply N.le_sub_l | apply (x86_regsize MDL EAX) ]).
    replace (mem Ⓓ[eax-4] >> 16 mod 2^8) with (mem (eax-2)) by (
      change 4 with (2+N.succ 1);
      rewrite getmem_split, N.shiftr_lor, shiftr_low_pow2, N.lor_0_l by apply getmem_bound, WTM;
      rewrite N.shiftr_shiftl_l, N.shiftl_0_r by discriminate 1;
      rewrite getmem_succ, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.mod_small by apply WTM;
      rewrite N.shiftl_mul_pow2, N.land_ones, N.mod_mul, N.lor_0_r by discriminate 1;
      change 4 with (2+2); rewrite N.sub_add_distr, N.sub_add by apply N.le_add_le_sub_r, EAX4;
      reflexivity).
  step. eexists. split. reflexivity. split. exact NF2. symmetry. apply Neqb_ok. exact BC.
  apply N.eqb_neq, N.neq_sym, N_neq0_gt0 in BC.
  assert (NF1: nilfree mem (mem Ⓓ[esp+4]) (eax-1)). split.
    etransitivity. apply (proj1 NF2). apply N.sub_le_mono_l. discriminate 1.
    intros i H1 H2. apply N.lt_le_pred in H2. rewrite <- N.sub_succ_r in H2. apply N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      apply (proj2 NF2). exact H1. exact H2.
      rewrite H2. exact BC.
  clear NF2 BC.
  step.
    replace (eax - 2 ⊕ 1) with (eax-1) by (
      change 2 with (1+1) at 1;
      rewrite N.sub_add_distr, N.sub_add by (apply N.le_add_le_sub_r; transitivity 4; [ discriminate 1 | exact EAX4 ]);
      symmetry; apply N.mod_small; eapply N.le_lt_trans; [ apply N.le_sub_l | apply (x86_regsize MDL EAX) ] ).
  eexists. split. reflexivity. split. exact NF1. destruct NIL as [i [[H1 H2] NIL]]. replace eax with (N.succ (eax-1)) in H2.
    apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2 as [H2|H2].
      contradict NIL. apply N_neq0_gt0. apply NF1. exact H1. exact H2.
      rewrite <- H2. exact NIL.
    rewrite N.sub_1_r. apply N.succ_pred. intro H. apply EAX4. rewrite H. reflexivity.

  Unshelve. all:focus_addr ADDR 182. destruct PRE as [eax [EAX [NF NIL]]].
  step.
    rewrite (N.mod_small (esp+4)) by (eapply N.lt_le_trans; [|exact ESPLO]; apply N.add_lt_mono_l; reflexivity).
    rewrite <- N.add_sub_assoc by exact (proj1 NF).
    rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by discriminate 1.
    rewrite (N.mod_small (eax-_)) by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply (x86_regsize MDL EAX) ]).
  eexists. split. reflexivity. rewrite N.add_sub_assoc, (N.add_comm _ eax), N.add_sub by exact (proj1 NF). split.
    exact NF.
    exact NIL.

  Unshelve. destruct PRE as [eax [EAX [NF NIL]]].
  step. split. simpl_stores. rewrite N.mod_small. reflexivity. eapply N.lt_le_trans; [|exact ESPLO]. apply N.add_lt_mono_l. reflexivity.
  eexists. simpl_stores. repeat split.
    exact EAX.
    exact NIL.
    intros i H. apply NF. apply N.le_add_r. apply N.add_lt_mono_l. exact H.
Qed.
