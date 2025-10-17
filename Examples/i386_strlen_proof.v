Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import i386_strlen.

Import X86Notations.
Open Scope N.

(* The x86 lifter models non-writable code. *)
Theorem strlen_nwc: forall s2 s1, strlen_i386 s1 = strlen_i386 s2.
Proof. reflexivity. Qed.

(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strlen_welltyped: welltyped_prog x86typctx strlen_i386.
Proof.
  Picinae_typecheck.
Qed.

(* Example #2: Memory safety
   Strlen contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem strlen_preserves_memory:
  forall_endstates strlen_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.



(* Example #3: Architectural calling convention compliance
   Strlen does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strlen_preserves_ebx:
  forall_endstates strlen_i386 (fun _ s _ s' => s R_EBX = s' R_EBX).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

Theorem strlen_preserves_readable:
  forall_endstates strlen_i386 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.


(* Proving that strlen preserves ESP is our first example of a property that
   requires stepwise symbolic interpretation of the program to verify.  We must
   first identify the instruction addresses that we wish to consider as subroutine
   exit points (usually the return instructions).  This is where post-conditions
   are placed, and where symbolic execution will stop during the proof. *)
Definition strlen_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 186 => true
  | _ => false
  end | _ => false end.

(* We next define a set of invariants, one for each program point.  In this simple
   case, all program points have the same invariant, so we return the same for all. *)
Definition esp_invs (esp:N) (t:trace) :=
  match t with (Addr _,s)::_ =>
    Some (s R_ESP = esp)
  | _ => None end.

(* Now we pose a theorem that asserts that this invariant-set is satisfied at
   all points in the subroutine.  The "satisfies_all" function asserts that
   anywhere an invariant exists (e.g., at the post-condition), it is true. *)
Theorem strlen_preserves_esp:
  forall s esp mem t s' x'
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x86typctx s)
         (ESP: s R_ESP = esp) (MEM: s V_MEM32 = mem),
  satisfies_all strlen_i386 (esp_invs esp) strlen_exit ((x',s')::t).
Proof.
  intros.

  (* Use the prove_inv inductive principle from Picinae_theory.v. *)
  apply prove_invs.

  (* We must first prove the pre-condition, which says that the invariant-set is
     satisfied on entry to the subroutine.  This is proved by assumption ESP. *)
  simpl. rewrite ENTRY. x86_step. exact ESP.

  (* Now we enter the inductive case, wherein Coq asks us to prove that the invariant-set
     is preserved by every (reachable) instruction in the program.  Before breaking the
     goal down into many cases (one for each instruction in this case), it is wise to
     simplify and/or remove anything in the context that is unnecessary. In order for
     symbolic interpretation to succeed, the context must reveal the values of all
     relevant variables in store s1 (which denotes the store on entry to each instruction
     for which the goal must be proved).  The only two variables in our invariant-set are
     ESP and MEM.  The value of ESP will be revealed by our pre-condition (PRE).  We can
     get the value of MEM using our previously proved strlen_preserves_memory theorem. *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlen_welltyped. intro MDL1.
  clear - PRE. rename t1 into t.

  (* We are now ready to break the goal down into one case for each invariant-point.
     The destruct_inv tactic finds all the invariants defined by the invariant-set
     in a precondition hypothesis (PRE).  Its first argument is the address bitwidth
     of the ISA (32 bits in this case). *)
  destruct_inv 32 PRE.

  (* Now we launch the symbolic interpreter on all goals in parallel.  (This can
     take a while to complete, so please be patient...!) *)
  all: x86_step.

  (* Note that we wind up with more goals that we started with, since some of the
     instructions branch, requiring us to prove the goal for each possible destination.
     Fortunately, since this is a pretty simple invariant-set, the symbolic state
     inferred for all the goals trivially satisfies the theorem.  We can solve
     all by assumption or reflexivity: *)
  all: try solve [ reflexivity | assumption ].

  (* At Qed, Coq re-checks the proof, including all those symbolic interpretation
     steps, so please be patient again... *)
Qed.


(* Example #4: Partial correctness
   Proving full partial correctness of strlen is challenging because strlen's
   binary implementation relies on some obscure properties of bit arithmetic
   to more efficiently find zeros in groups of bytes instead of one at a time.
   Our goal is to prove that at termination, strlen returns (in EAX) a value k
   that satisfies the following:
   (1) p <= k,
   (2) no memory byte at addresses in the interval [p, p+k) is nil, and
   (3) the byte at address p+k is nil,
   where p is the address stored at [ESP+4] on entry. *)

(* We define partial-correctness of strlen as returning an index in EAX
   such that all addresses in [p, p+EAX) are "nil-free" (non-zero), where
   p is the (original) value of the first stack argument. *)
Definition nilfree (m:memory) (p:addr) (k:N) :=
  forall i, i < k -> m Ⓑ[p+i] <> 0.

(* The invariant-set for this property is much more complex than our previous
   examples.  Addresses 38, 153, and 182 are meets in the control-flow graph,
   so we place invariants at those points to simplify the analysis.  Address 49
   is the start of an unrolled loop, where the loop body has been replicated at
   addresses 75, 101, and 127 for better performance.  We therefore put our
   loop invariant at all four addresses so that we can treat it like a rolled
   loop, and avoid duplications in the proof logic.  Address 186 is the
   return instruction at the end, so gets a special invariant. *)
Definition Ones (b n:N) := N.iter n (fun x => x * 2^b + 1) 0.
Definition strlen_invs (m:memory) (esp:N) (t:trace) :=
  let p := m Ⓓ[4+esp] in
  match t with (Addr a,s)::_ => match a with
  | 38 => Some (
        ∃ k, s R_EAX = (k⊕p) /\ nilfree m p k /\ s R_EDX < 4 /\ (k+p) mod 4 = 3
    )
  | 49 | 75 | 101 | 127 => Some (
        ∃ k, s R_EAX = (k⊕p) /\ nilfree m p k /\ s R_EDX = 0 /\ (k+p) mod 4 = 0
    )
  | 153 => Some (
        ∃ k, s R_EAX = (k⊕p) /\ nilfree m p (k-4) /\ 4 <= k /\
            s R_ECX = (m Ⓓ[(k-4)+p] ⊖ Ones 8 4) /\ (k+p) mod 4 = 0 /\
               ∃ i, i < 4 /\ m Ⓑ[(i+k-4)+p] = 0
    )
  | 182 => Some (∃ k, s R_EAX = (k⊕p) /\ nilfree m p k /\ m Ⓑ[k+p] = 0)
  | 186 => Some (∃ k, s R_EAX = k /\ nilfree m p k /\ m Ⓑ[k+p] = 0)
  | _ => None
  end | _ => None end.

(* Before attempting the main theorem, we prove many helper lemmas about bit arithmetic... *)

Lemma Nsub_distr:
  forall x y z, z <= y -> y <= x -> x - (y - z) = x - y + z.
Proof.
  intros.
  apply (N.add_cancel_r _ _ (y-z)).
  rewrite N.sub_add by (transitivity y; [ apply N.le_sub_l | assumption ]).
  rewrite N.add_sub_assoc by assumption.
  rewrite <- N.add_assoc, (N.add_comm z y), N.add_assoc, N.add_sub.
  symmetry. apply N.sub_add. assumption.
Qed.

Lemma land_lohi_0:
  forall x y n, x < 2^n -> N.land x (N.shiftl y n) = 0.
Proof.
  intros. apply N.bits_inj_0. intro m. rewrite N.land_spec. destruct (N.lt_ge_cases m n).
    rewrite N.shiftl_spec_low. apply Bool.andb_false_r. assumption.
    erewrite bound_hibits_zero. reflexivity. exact H. assumption.
Qed.

Lemma le_div:
  forall a b c, a <= b -> a/c <= b/c.
Proof.
  intros.
  destruct c. destruct a; destruct b; reflexivity.
  intro H2. apply H, N.lt_gt. eapply N.lt_le_trans.
  rewrite (N.div_mod' b (N.pos p)) at 1.
  apply N.add_lt_mono_l. eapply (N.lt_lt_add_r _ _ (a mod N.pos p)). apply N.mod_lt. discriminate 1.
  rewrite N.add_assoc, <- N.mul_succ_r. rewrite (N.div_mod' a (N.pos p)) at 2.
  apply N.add_le_mono_r, N.mul_le_mono_l, N.le_succ_l, N.gt_lt, H2.
Qed.

Lemma Ones_succ:
  forall n w, Ones n (N.succ w) = (Ones n w) * 2^n + 1.
Proof.
  intros. unfold Ones at 1. rewrite Niter_succ. reflexivity.
Qed.

Lemma Ones_succ_top:
  forall w n, Ones w (N.succ n) = Ones w n + 2^(w*n).
Proof.
  intros. induction n using N.peano_ind.
    rewrite N.mul_0_r. reflexivity.
    rewrite Ones_succ, Ones_succ, N.mul_succ_r, N.pow_add_r, <- N.add_assoc,
            (N.add_comm 1), N.add_assoc, <- N.mul_add_distr_r, <- IHn, Ones_succ.
    reflexivity.
Qed.

Lemma Ones_split:
  forall w i j, Ones w (i+j) = (Ones w i) + (Ones w j) * 2^(w*i).
Proof.
  intros. revert i. induction j using N.peano_ind; intro.
    rewrite N.mul_0_l, N.add_0_r, N.add_0_r. reflexivity.
    rewrite Ones_succ, <- N.add_succ_comm, N.mul_add_distr_r, <- N.mul_assoc,
            <- N.pow_add_r, (N.add_comm w), <- N.mul_succ_r, (N.add_comm _ (1*_)), N.add_assoc,
            N.mul_1_l, <- Ones_succ_top.
    apply IHj.
Qed.

Lemma split_digit: forall m n p, 0 < m -> m*n <= p -> p - n = p - m*n + (m-1)*n.
Proof.
  intros. rewrite N.mul_sub_distr_r. rewrite N.add_sub_assoc.
    rewrite N.sub_add by assumption. rewrite N.mul_1_l. reflexivity.
    apply N.mul_le_mono_nonneg_r. apply N.le_0_l. apply N.lt_pred_le. assumption.
Qed.

Lemma Ones_bound:
  forall p x, Ones (N.pos p) x < 2^(N.pos p * x).
Proof.
  intros. induction x using N.peano_ind.
    apply mp2_gt_0.
    rewrite Ones_succ_top, N.mul_succ_r, N.pow_add_r. eapply N.lt_le_trans.
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
  rewrite <- N.Div0.add_mod_idemp_l, N.Div0.mod_same, N.add_0_l.
  rewrite N.mod_small by (
    eapply N.le_lt_trans; [apply N.le_sub_l|]; eapply N.le_lt_trans; [exact H0|]; apply N.mod_upper_bound, N.pow_nonzero; discriminate 1).
  apply N.sub_lt; assumption.
Qed.

Lemma sub_lnot: forall x w, x < 2^w ->
  N.lnot x w = 2^w - x - 1.
Proof.
  intros.
  rewrite <- N.sub_add_distr, N.add_comm, N.sub_add_distr, N.sub_1_r, <- N.ones_equiv.
  destruct x.
    rewrite N.sub_0_r. apply N.lnot_0_l.
    apply N.lnot_sub_low, N.log2_lt_pow2. reflexivity. assumption.
Qed.

Lemma bytes_pos_lobound:
  forall mem i a
         (H: forall j, j < i -> mem Ⓑ[a + j] <> 0),
  Ones 8 i <= getmem 32 LittleE i mem a.
Proof.
  induction i using N.peano_ind; intros.
    reflexivity.
    rewrite Ones_succ, <- N.add_1_l, getmem_split, lor_plus.
      rewrite N.add_comm. apply N.add_le_mono.
        apply N.lt_pred_le, N.neq_0_lt_0. rewrite <- (N.add_0_r a). apply H. apply N.lt_0_succ.
        rewrite N.shiftl_mul_pow2. apply N.mul_le_mono_nonneg_r.
          apply N.le_0_l.
          apply IHi. intros. rewrite <- N.add_assoc, N.add_1_l. apply H. apply -> N.succ_lt_mono. assumption.
      apply land_lohi_0, getmem_bound.
Qed.

Lemma below_ones:
  forall mem w a
         (GM: getmem 32 LittleE w mem a < Ones 8 w),
  exists i, i < w /\ mem Ⓑ[a+i] = 0.
Proof.
  induction w using N.peano_ind; intros.
    contradict GM. apply N.nlt_0_r.
    rewrite Ones_succ, <- N.add_1_l, getmem_split in GM. destruct (mem Ⓑ[a]) eqn:M0.
      exists 0. split. apply N.lt_0_succ. rewrite N.add_0_r. exact M0.
      rewrite N.add_1_r in GM. destruct (IHw (N.succ a)) as [i [LOI MI]].

        apply (N.mul_lt_mono_pos_r (2^8)). reflexivity.
        rewrite <- N.shiftl_mul_pow2.
        apply (N.le_lt_add_lt 1 (N.pos p)). destruct p; discriminate 1.
        rewrite N.add_comm, <- lor_plus. exact GM.
        apply N.bits_inj_0. intro n. rewrite N.land_spec. destruct (N.lt_ge_cases n 8) as [LO|HI].
          rewrite N.shiftl_spec_low. apply Bool.andb_false_r. exact LO.
          rewrite bound_hibits_zero with (w:=8). reflexivity. rewrite <- M0. apply getmem_bound. exact HI.

        exists (N.succ i). split.
          revert LOI. apply N.succ_lt_mono.
          rewrite <- N.add_succ_comm. exact MI.
Qed.

Lemma testbit_pred:
  forall x y, N.testbit (N.pred x) y =
  match x with 0 => false | N.pos _ => xorb (N.testbit x y) (x mod 2^y =? 0) end.
Proof.
  intros. destruct x as [|x]. reflexivity.
  apply Bool.xorb_move_l_r_1.
  rewrite 2!N.testbit_odd, <- N.odd_add, (N.shiftr_div_pow2 (N.pred _)).
  rewrite <- (recompose_bytes y (N.pos x)) at 2.
  destruct (_ mod _) as [|p] eqn:LO.

    assert (H: 0 < N.pos x >> y).
      apply (N.mul_lt_mono_pos_r (2^y)), (N.add_lt_mono_l _ _ (N.pos x mod 2^y)). apply mp2_gt_0.
      rewrite N.mul_0_l, N.add_0_r, <- N.shiftl_mul_pow2, <- lor_plus, recompose_bytes, LO
        by (apply land_lohi_0, N.mod_lt, N.pow_nonzero; discriminate).
      reflexivity.
    rewrite N.lor_0_l, N.shiftl_mul_pow2.
    rewrite <- (N.sub_add 1 (_ >> y)) at 2 by apply (N.le_succ_l 0), H.
    rewrite N.add_1_r, N.mul_succ_l, <- N.add_pred_r by (apply N.pow_nonzero; discriminate).
    rewrite N.div_add_l by (apply N.pow_nonzero; discriminate).
    rewrite N.div_small by (apply N.lt_pred_l, N.pow_nonzero; discriminate).
    rewrite N.add_0_r, N.sub_1_r, N.odd_add, N.odd_pred by apply N.neq_0_lt_0, H.
    rewrite <- N.negb_odd, <- Bool.negb_xorb_r, Bool.xorb_nilpotent. reflexivity.

    rewrite lor_plus by (apply land_lohi_0; rewrite <- LO; apply N.mod_lt, N.pow_nonzero; discriminate).
    rewrite <- N.add_pred_l by (destruct p; discriminate).
    rewrite N.shiftl_mul_pow2, N.div_add by (apply N.pow_nonzero; discriminate).
    rewrite N.div_small by (rewrite <- LO; apply N.lt_lt_pred, N.mod_lt, N.pow_nonzero; discriminate).
    rewrite N.add_0_l, N.odd_add, Bool.xorb_nilpotent. reflexivity.
Qed.

Lemma odd_ones:
  forall n, n <> 0 -> N.odd (N.ones n) = true.
Proof.
  intros. rewrite N.ones_equiv, N.odd_pred by (apply N.pow_nonzero; discriminate).
  apply N.even_pow, H.
Qed.

Lemma extract_bit:
  forall b w xw x y z
    (H1: y*2^b < x/2^w) (H2: z <= x mod 2^w) (H3: b+w < xw) (H4: N.odd y = true),
  (x/2^w mod 2^b =? 0) = N.testbit (N.lxor (N.lnot x xw) (x - (z + (y*2^b + 1)*2^w))) (b+w).
Proof.
  intros.

  assert (YX: y <= x >> w >> b).
    rewrite 2!N.shiftr_div_pow2, <- (N.div_mul y (2^b)) by (apply N.pow_nonzero; discriminate).
    apply le_div, N.lt_le_incl, H1.

  rewrite <- N.shiftr_spec', N.shiftr_lxor.
  rewrite <- (recompose_bytes w x) at 3.
  rewrite lor_plus by (apply land_lohi_0, N.mod_lt, N.pow_nonzero; discriminate).
  rewrite N.lxor_spec, N.sub_add_distr, N.add_comm, <- N.add_sub_assoc,
          N.add_comm, N.shiftl_mul_pow2 by assumption.
  rewrite <- N.add_sub_assoc by (rewrite N.shiftr_div_pow2, N.add_1_r; apply N.mul_le_mono_r, N.le_succ_l, H1).
  rewrite <- N.mul_sub_distr_r, (N.shiftr_div_pow2 (_+_)), N.div_add by (apply N.pow_nonzero; discriminate).
  rewrite (N.div_small (_-_)) by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply N.mod_lt, N.pow_nonzero; discriminate ]).
  rewrite N.add_0_l, N.sub_add_distr, N.sub_1_r, <- (recompose_bytes b (x>>w)).
  rewrite lor_plus by (apply land_lohi_0, N.mod_lt, N.pow_nonzero; discriminate).
  rewrite N.shiftl_mul_pow2, <- N.add_sub_assoc by apply N.mul_le_mono_r, YX.
  rewrite <- N.mul_sub_distr_r, testbit_pred, N.Div0.mod_add, N.Div0.mod_mod.
  rewrite 2!N.testbit_odd, (N.shiftr_div_pow2 (_+_)), N.div_add by (apply N.pow_nonzero; discriminate).
  rewrite (N.div_small (_ mod _)) by (apply N.mod_lt, N.pow_nonzero; discriminate).
  rewrite N.add_0_l, N.odd_sub, H4 by apply YX.
  unfold N.lnot. rewrite 2!N.shiftr_lxor, (N.shiftr_shiftr (N.ones _)), (N.shiftr_div_pow2 (N.ones _)).
  rewrite N.ones_div_pow2 by (rewrite N.add_comm; apply N.lt_le_incl, H3).
  rewrite <- N.bit0_odd, N.lxor_spec, !N.bit0_odd, odd_ones by (rewrite N.add_comm; apply N.sub_gt, H3).
  destruct (_ mod _ + _) eqn:NZ.
    rewrite N.mul_sub_distr_r, N.add_sub_assoc in NZ by apply N.mul_le_mono_r, YX.
    rewrite <- N.shiftl_mul_pow2, <- lor_plus in NZ by (apply land_lohi_0, N.mod_lt, N.pow_nonzero; discriminate).
    rewrite recompose_bytes, N.shiftr_div_pow2 in NZ. contradict NZ. apply N.sub_gt, H1.
  rewrite Bool.xorb_true_r, <- Bool.xorb_assoc, Bool.xorb_nilpotent, N.shiftr_div_pow2, Bool.xorb_false_l.
  reflexivity.
Qed.

Lemma testbit_ones_true:
  forall w n b, b<>0 -> n < w -> N.testbit (Ones b w) (b*n) = true.
Proof.
  intros w n b H0 H.

  destruct b as [|b']. contradict H0. reflexivity. clear H0.

  rewrite <- (N.sub_add n w) by apply N.lt_le_incl, H.
  destruct (w-n) eqn:H1. contradict H. apply N.nlt_ge, N.sub_0_le. assumption.
  rewrite <- (N.succ_pred (N.pos p)), N.add_comm, Ones_split, Ones_succ by discriminate.
  rewrite <- lor_plus by (rewrite <- N.shiftl_mul_pow2; apply land_lohi_0, Ones_bound).
  erewrite N.lor_spec, bound_hibits_zero; [| apply Ones_bound | reflexivity].
  rewrite N.mul_pow2_bits_high, N.sub_diag by reflexivity.
  rewrite <- lor_plus by (rewrite N.land_comm, <- N.shiftl_mul_pow2; change 1 with (2^0);
                          apply land_lohi_0, N.pow_lt_mono_r; reflexivity).
  rewrite N.lor_spec, N.mul_pow2_bits_low by reflexivity.
  reflexivity.
Qed.

Lemma testbit_onesm1_true:
  forall w n b, b<>0 -> n<>0 -> n<w -> N.testbit (Ones b w - 1) (b*n) = true.
Proof.
  intros.
  destruct w. contradict H1. apply N.nlt_0_r.
  rewrite <- (N.succ_pred (N.pos p)) by discriminate 1.
  rewrite Ones_succ, N.add_sub. rewrite <- (N.mul_1_r b) at 2.
  destruct n. contradict H0. reflexivity.
  rewrite N.mul_pow2_bits_high by (apply N.mul_le_mono_nonneg_l; [ apply N.le_0_l | destruct p0; discriminate 1]).
  rewrite <- N.mul_sub_distr_l, N.sub_1_r. apply testbit_ones_true. assumption.
  apply -> N.pred_lt_mono. assumption. discriminate 1.
Qed.

Theorem noborrow_nonil:
  forall mem w a
         (GM: Ones 8 w <= getmem 32 LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem 32 LittleE w mem a) (8*w))
                              (getmem 32 LittleE w mem a - Ones 8 w))
                      (Ones 8 w - 1) = 0)
         i (IW: i < w),
  mem Ⓑ[a + i] <> 0.
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

  apply N.eqb_neq.
  rewrite Ones_split in TST at 1. rewrite Ones_succ in TST.
  apply (f_equal (fun x => N.testbit x (8 + 8*i))) in TST.
  rewrite N.bits_0, N.land_spec in TST.
  rewrite <- extract_bit in TST.
  rewrite <- TST.
  rewrite getmem_split, <- N.shiftr_div_pow2, N.shiftr_lor, (N.mul_comm 8).
  rewrite N.shiftr_shiftl_l by reflexivity.
  rewrite N.sub_diag, N.shiftl_0_r, N.shiftr_div_pow2.
  rewrite N.div_small by apply getmem_bound.
  rewrite N.lor_0_l, <- N.add_1_l, getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.Div0.mod_mul.
  rewrite N.lor_0_r.
  rewrite N.mod_small by apply getmem_bound.
  rewrite <- (N.mul_1_l 8) at 2. rewrite <- N.mul_add_distr_r, N.mul_comm. rewrite testbit_onesm1_true.
    rewrite Bool.andb_true_r. reflexivity.
    discriminate 1.
    rewrite N.add_1_l. apply N.succ_0_discr.
    rewrite N.add_comm, <- (N.add_0_r (_+_)), N.add_assoc. apply N.add_lt_mono_l. reflexivity.

  rewrite Ones_split, getmem_split in GM.
  rewrite lor_plus in GM by apply land_lohi_0, getmem_bound.
  rewrite N.shiftl_mul_pow2, (N.mul_comm 8) in GM.
  apply (N.Div0.div_le_mono _ _ (2^(i*8))) in GM.
  do 2 rewrite N.div_add in GM by (apply N.pow_nonzero; discriminate 1).
  rewrite N.mul_comm, N.div_small in GM by apply Ones_bound.
  rewrite N.mul_comm, N.div_small in GM by apply getmem_bound.
  apply N.le_succ_l. rewrite <- N.add_1_r, <- Ones_succ, getmem_split.
  rewrite lor_plus by apply land_lohi_0, getmem_bound.
  rewrite N.shiftl_mul_pow2.
  rewrite (N.mul_comm 8), N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small by apply getmem_bound.
  exact GM.

  rewrite getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mul_comm, N.Div0.mod_mul.
  rewrite N.mod_small by apply getmem_bound.
  rewrite N.lor_0_r. apply bytes_pos_lobound. exact IHi.

  rewrite N.add_comm, N.mul_add_distr_l. apply N.add_lt_mono_l.
  rewrite N.mul_succ_r. rewrite <- (N.add_0_l 8) at 1. apply N.add_lt_mono_r.
  apply N.mul_pos_pos; reflexivity.

  rewrite <- N.bit0_odd, <- (N.mul_0_r 8). apply testbit_ones_true.
    discriminate 1.
    reflexivity.

  subst w. clear TST IHi. revert a GM. induction i using N.peano_ind; intros.
    apply N.neq_0_lt_0. eapply N.lt_le_trans. apply N.lt_0_1. rewrite N.add_0_r. etransitivity.
      exact GM.
      rewrite <- N.add_1_l, getmem_split, getmem_0, N.lor_0_r. reflexivity.

    rewrite <- N.add_succ_comm. apply IHi.
    rewrite <- N.add_1_l, getmem_split, N.add_1_l, Ones_succ in GM.
    apply (N.Div0.div_le_mono _ _ (2^8)) in GM.
    rewrite N.div_add_l in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_small, N.add_0_r in GM; [|reflexivity].
    etransitivity. exact GM.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor, N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r, shiftr_low_pow2, N.lor_0_l.
      rewrite N.add_1_r. reflexivity. apply getmem_bound. reflexivity.
Qed.

Lemma lsd_pos:
  forall b x, b<>0 -> x<>0 -> exists n, x/2^(b*n) mod 2^b <> 0.
Proof.
  intros b x B0 X0. exists (N.log2 x / b).
  apply N.neq_0_lt_0. apply N.neq_0_lt_0 in X0. destruct (N.log2_spec x X0) as [LO HI].
  rewrite N.mod_small.
    eapply N.lt_le_trans.
      apply N.lt_0_1.
      erewrite <- N.div_same.
        apply le_div. etransitivity.
          apply N.pow_le_mono_r. discriminate 1. apply N.Div0.mul_div_le; assumption.
          assumption.
        apply N.pow_nonzero. discriminate 1.
    eapply N.mul_lt_mono_pos_l. apply mp2_gt_0. eapply N.le_lt_trans.
      apply N.Div0.mul_div_le.
      rewrite <- N.pow_add_r, <- N.mul_succ_r. eapply N.lt_le_trans.
        exact HI.
        apply N.pow_le_mono_r. discriminate 1. apply N.le_succ_l, N.mul_succ_div_gt. exact B0.
Qed.

Theorem borrow_nil:
  forall mem w a
         (GM: Ones 8 w <= getmem 32 LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem 32 LittleE w mem a) (8*w))
                              (getmem 32 LittleE w mem a - Ones 8 w))
                      (Ones 8 w - 1) <> 0),
  exists i, i < w /\ mem Ⓑ[a + i] = 0.
Proof.
  intros.
  destruct w as [|w]. contradict TST. rewrite N.land_0_r. reflexivity.
  rewrite <- (N.succ_pos_pred w) in *.
  apply (lsd_pos 8) in TST; [|discriminate 1]. destruct TST as [j TST].

  rewrite <- N.shiftr_div_pow2, N.shiftr_land, <- N.land_ones, <- N.land_assoc in TST.

  destruct j as [|j].
  rewrite N.mul_0_r, (N.shiftr_0_r (_-_)), Ones_succ, N.add_sub, <- N.shiftl_mul_pow2, (N.land_comm _ (N.ones _)) in TST.
  rewrite land_lohi_0 in TST by reflexivity.
  contradict TST. apply N.land_0_r.

  rewrite Ones_succ in TST at 2.
  rewrite N.add_sub, <- N.shiftl_mul_pow2 in TST.
  rewrite N.shiftr_shiftl_r in TST by (rewrite <- (N.mul_1_r 8) at 1; apply N.mul_le_mono_l; destruct j; discriminate 1).
  rewrite <- N.mul_pred_r in TST.
  destruct (N.le_gt_cases (N.pos j) (Pos.pred_N w)) as [JW|JW]; [|
    contradict TST;
    rewrite (shiftr_low_pow2 (Ones _ _)) by (eapply N.lt_le_trans; [ apply Ones_bound | apply N.pow_le_mono_r ; [ discriminate 1 | apply N.mul_le_mono_l, N.lt_le_pred, JW] ]);
    apply N.land_0_r ].
  rewrite <- (N.sub_add (N.pos j) (Pos.pred_N w)) in TST at 5 by exact JW.
  rewrite N.add_comm, Ones_split, (N.shiftr_div_pow2 (_+_)) in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 2 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ 8), N.pow_add_r, N.mul_assoc in TST.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite (Ones_succ_top _ (N.pred _)) in TST.
  rewrite <- (N.mul_1_l (2^(_*N.pred _))) in TST at 1.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in TST by apply Ones_bound.
  rewrite N.land_ones in TST.
  rewrite N.Div0.mod_add in TST.
  change (_ mod _) with (N.ones 1) in TST.
  rewrite N.land_ones, <- (N.div_1_r (N.shiftr _ _)) in TST.
  change 1 with (2^0) in TST at 1.
  rewrite <- N.testbit_spec', N.shiftr_spec', N.add_0_l in TST.
  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST at 4 by (
    etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
  rewrite N.add_comm, Ones_split in TST.
  rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
  rewrite Ones_succ in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ 8) in TST.

  destruct (N.le_gt_cases (Ones 8 (N.pred (N.pos j))) (getmem 32 LittleE (N.pred (N.pos j)) mem a)) as [LOJ|LOJ].

  rewrite <- extract_bit in TST.

  exists (N.pred (N.pos j)). split.

    apply N.lt_succ_r, N.le_le_pred. exact JW.

    rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST by (
      etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
    rewrite N.add_comm in TST.
    rewrite getmem_split in TST.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor in TST.
    rewrite N.mul_comm, shiftr_low_pow2 in TST by apply getmem_bound.
    rewrite N.shiftr_shiftl_l in TST by reflexivity.
    rewrite N.lor_0_l, N.sub_diag, N.shiftl_0_r in TST.
    rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
    rewrite <- N.add_1_l, getmem_split in TST.
    rewrite lor_plus in TST by apply land_lohi_0, getmem_bound.
    rewrite N.shiftl_mul_pow2, N.Div0.mod_add in TST.
    rewrite N.mod_small in TST by apply getmem_bound.
    destruct (getmem _ _ 1). reflexivity. contradict TST. reflexivity.

  apply N.le_succ_l. rewrite <- N.add_1_r, <- Ones_succ.
  rewrite <- N.sub_succ_l by apply N.le_le_pred, JW.
  rewrite <- (N.add_0_l (Ones _ _)).
  rewrite <- (N.div_small (Ones 8 (N.pred (N.pos j))) (2^(8 * N.pred (N.pos j)))) by apply Ones_bound.
  rewrite <- N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite <- Ones_split.
  rewrite N.add_sub_assoc by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, N.add_sub.
  apply le_div. exact GM.

  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones.
  rewrite N.mul_comm, N.mod_small by apply getmem_bound.
  rewrite N.land_ones, N.shiftl_mul_pow2, N.Div0.mod_mul, N.lor_0_r. exact LOJ.

  rewrite N.mul_succ_r, N.add_comm.
  apply N.add_lt_mono_r, N.mul_lt_mono_pos_l. reflexivity.
  eapply N.lt_le_trans. apply N.lt_pred_l. discriminate 1. exact JW.

  rewrite <- (N.succ_pred (_-_)), Ones_succ.
  change (2^8) with (2*2^N.pred 8).
  rewrite N.mul_comm, <- N.mul_assoc, N.add_comm. apply N.odd_add_mul_2.
  intro H. apply JW, N.lt_gt. eapply N.le_lt_trans. apply N.sub_0_le. exact H. apply N.lt_pred_l. discriminate 1.

  destruct (below_ones _ _ _ LOJ) as [k [KW MK]].
  exists k. split.
    eapply N.lt_le_trans.
      exact KW.
      apply N.le_le_pred, N.le_le_succ_r, JW.
    exact MK.
Qed.

Lemma nilfree0: forall m p, nilfree m p 0.
Proof. intros m p i H1. destruct i; discriminate. Qed.

Lemma nilfree_succ:
  forall m p k (BC: (0 =? m Ⓑ[k+p]) = false) (NF: nilfree m p k),
  nilfree m p (N.succ k).
Proof.
  intros. intros i H. apply N.lt_succ_r, N.le_lteq in H. destruct H.
    revert i H. exact NF.
    subst. apply N.neq_sym, N.eqb_neq. psimpl. rewrite N.add_comm. exact BC.
Qed.

Lemma succ_sub:
  forall x y, N.pos y <= x -> N.succ (x - N.pos y) = x - N.pred (N.pos y).
Proof.
  symmetry. rewrite <- N.sub_succ, N.succ_pred by discriminate.
  apply N.sub_succ_l, H.
Qed.

Lemma add_assoc_mod4:
  forall x y z, (x+y) mod 4 = 0 -> z < 4 -> x ⊕ (y + z) = x ⊕ y + z.
Proof.
  intros.
  rewrite N.add_assoc, <- N.Div0.add_mod_idemp_l.
  rewrite (N.mod_small (_+z)). reflexivity.
  rewrite (N.div_mod' (x+y) 4), H, N.add_0_r.
  change (2^32) with (4*2^30). rewrite N.Div0.mul_mod_distr_l.
  change (4*2^30) with (4*(N.pred (2^30))+4). apply N.add_le_lt_mono; [|assumption].
  apply N.mul_le_mono_pos_l. reflexivity. apply N.lt_le_pred, N.mod_upper_bound. discriminate.
Qed.

Lemma lnot_computation:
  forall m p k (LE: Ones 8 4 <= m Ⓓ[k+p]),
  (N.lnot (m Ⓓ[ p + k ]) 32 .^ (m Ⓓ[ p + k ] - Ones 8 4)) .& (Ones 8 4 - 1) =
  ((msub 25 33554431 (m Ⓓ[k+p])) .^ (16711423 + m Ⓓ[k+p])) .& 16843008.
Proof.
  intros.
  rewrite sub_lnot, <- N.sub_add_distr, N.add_comm, N.sub_add_distr, N.sub_1_r by apply getmem_bound.
  change (Ones 8 4 - 1) with (N.ones 25 .& 16843008).
  rewrite N.add_comm, N.land_assoc, N.land_ones, N_lxor_mod_pow2.
  change 25 with (N.min 32 25) at 1.
  rewrite <- mp2_mod_mod_min, <- msub_sub by apply N.lt_le_pred, getmem_bound.
  erewrite msub_mod_pow2, <- msub_mod_l by reflexivity.
  rewrite <- (N.Div0.mod_add (_ - Ones 8 4) 1), <- N.add_sub_swap, <- N.add_sub_assoc by
    first [ discriminate 1 | apply LE ].
  change (N.min 32 25) with (N.min 25 25). rewrite <- msub_mod_pow2 by reflexivity.
  rewrite <- N_lxor_mod_pow2, <- N.land_ones, <- N.land_assoc, (N.add_comm _ (_-_)).
  reflexivity.
Qed.

Lemma strlen_loopexit1:
  forall m p k (NF: nilfree m p k)
         (PK4: (k + p) mod 4 = 0)
         (BC1: (m Ⓓ[k+p] ⊖ 16843009 <? m Ⓓ[k+p]) = true)
         (BC2: (0 =? ((msub 25 33554431 (m Ⓓ[k+p])) .^ (16711423 + m Ⓓ[k+p])) .& 16843008) = true),
  ∃ k0, (4 + k ⊕ p) = (k0 ⊕ p) /\
        nilfree m p k0 /\
        (((msub 25 33554431 (m Ⓓ[k+p])) .^ (16711423 + m Ⓓ[k+p])) .& 16843008) = 0 /\
        (k0 + p) mod 4 = 0.
Proof.
  intros.
  apply Neqb_ok in BC2. symmetry in BC2.
  assert (LE: Ones 8 4 <= m Ⓓ[k+p]).
    apply (add_sub_mod_le _ (2^32)). discriminate. rewrite sub_sbop, <- msub_sbop by reflexivity. apply N.ltb_lt, BC1.

  exists (4+k). repeat split.
    intros i H. destruct (N.lt_ge_cases i k).
      apply NF; assumption.

      rewrite <- (N.sub_add k i) by assumption.
      rewrite (N.add_comm _ k). rewrite N.add_assoc.
      apply noborrow_nonil with (w:=4).
        rewrite N.add_comm. exact LE.
        rewrite lnot_computation; assumption.
        eapply N.add_lt_mono_r. rewrite N.sub_add; assumption.
        rewrite BC2. reflexivity.
        rewrite <- N.add_assoc, <- N.Div0.add_mod_idemp_l, N.Div0.mod_same, N.add_0_l. assumption.
Qed.

Lemma strlen_loopexit2:
  forall m p k (NF: nilfree m p k) (PK4: (k+p) mod 4 = 0)
         (BC1: (m Ⓓ[k+p] ⊖ 16843009 <? m Ⓓ[k+p]) = true)
         (BC2: (0 =? (msub 25 33554431 (m Ⓓ[k+p]) .^ (16711423 + m Ⓓ[k+p])) .& 16843008) = false),
  ∃ k0, (4 + k ⊕ p) = (k0 ⊕ p) /\
        nilfree m p (k0 - 4) /\
        4 <= k0 /\
        (m Ⓓ[k+p] ⊖ 16843009) = (m Ⓓ[k0-4+p] ⊖ Ones 8 4) /\
        (k0+p) mod 4 = 0 /\
        (∃ i, i < 4 /\ m Ⓑ[i + k0 - 4 + p] = 0).
Proof.
  intros.
  apply N.eqb_neq, not_eq_sym in BC2.
  assert (LE: Ones 8 4 <= m Ⓓ[k+p]).
    apply (add_sub_mod_le _ (2^32)). discriminate. rewrite sub_sbop, <- msub_sbop by reflexivity. apply N.ltb_lt, BC1.
  rewrite <- lnot_computation in BC2 by assumption.

  exists (4+k). repeat split.
    rewrite N.add_comm, N.add_sub. exact NF.
    apply N.le_add_r.
    rewrite (N.add_comm 4), N.add_sub. reflexivity.
    rewrite <- N.add_assoc, <- N.Div0.add_mod_idemp_l, N.Div0.mod_same. exact PK4.
    rewrite N.add_comm in LE. apply borrow_nil in BC2; try assumption.
      destruct BC2 as [i [I4 NIL]]. exists i. split. exact I4.
        rewrite (N.add_comm 4), N.add_assoc, N.add_sub.
        rewrite N.add_comm, (N.add_comm i), N.add_assoc. assumption.
Qed.

Lemma strlen_loopexit3:
  forall m p k (NF: nilfree m p k) (PK4: (k+p) mod 4 = 0)
         (BC: (m Ⓓ[k+p] ⊖ 16843009 <? m Ⓓ[k+p]) = false),
  ∃ k0, (4 + k ⊕ p) = (k0 ⊕ p) /\
        nilfree m p (k0 - 4) /\
        4 <= k0 /\
        (m Ⓓ[k+p] ⊖ 16843009) = (m Ⓓ[ k0 - 4 + p ] ⊖ Ones 8 4) /\
        (k0+p) mod 4 = 0 /\
        (∃ i, i < 4 ∧ m Ⓑ[ i + k0 - 4 + p ] = 0).
Proof.
  intros. exists (4+k). repeat split.
    rewrite N.add_comm, N.add_sub. exact NF.
    apply N.le_add_r.
    rewrite (N.add_comm 4), N.add_sub. reflexivity.
    rewrite <- N.add_assoc, <- N.Div0.add_mod_idemp_l, N.Div0.mod_same. exact PK4.

    apply N.ltb_ge in BC.
    erewrite <- (N.mod_small (getmem _ _ _ _ _)) in BC at 1 by apply getmem_bound.
    apply le_msub_r in BC; [|reflexivity].
    rewrite !N.mod_small in BC by (reflexivity || apply getmem_bound).
    apply below_ones in BC. destruct BC as [i [I4 NIL]].
    exists i. split. exact I4.
    rewrite (N.add_comm 4), N.add_assoc, N.add_sub.
    rewrite (N.add_comm i), <- N.add_assoc, (N.add_comm i), N.add_assoc.
    assumption.
Qed.

(* Finally we're ready to prove the main partial correctness theorem. *)
Theorem strlen_partial_correctness:
  forall s esp m t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s)
         (ESP: s R_ESP = esp) (MEM: s V_MEM32 = m),
  satisfies_all strlen_i386 (strlen_invs m esp) strlen_exit ((x',s')::t).
Proof.
  intros.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x86_step.

  (* Optional: This proof ignores AF OF and SF flags, so tell the evaluator
     to ignore values assigned to them. *)
  Ltac ignore_vars v ::= constr:(match v with
  | R_AF | R_OF | R_SF => true | _ => false end).

  (* Prove using Picinae's prove_invs theorem. *)
  apply prove_invs.

  (* Address 0 *)
  simpl. rewrite ENTRY.
  step. step. step. step. exists 0. psimpl. repeat split.
    intros i H1. destruct i; discriminate.
    rewrite <- (Neqb_ok _ _ BC). reflexivity.
    symmetry. apply Neqb_ok, BC.
  step. step. step. exists 0. psimpl. repeat split.
    apply nilfree0. symmetry. apply Neqb_ok. assumption.
  eassert (NF: nilfree m _ _).
    apply nilfree_succ; [|apply nilfree0].
    rewrite N.add_0_l. exact BC1.
  step. step. step. exists 1. psimpl. repeat split.
    apply NF.
    symmetry. apply Neqb_ok. assumption.
  apply nilfree_succ in NF; [|exact BC2].
  step. step. step. apply Neqb_ok, eq_sym in BC3. exists 2. psimpl. repeat split.
    exact NF.
    rewrite BC3. reflexivity.
    apply N.lxor_eq in BC3. rewrite <- (msub_mod_l 2 2) by reflexivity. change (2^2) with 4. rewrite BC3. reflexivity.
  exists 2. psimpl. repeat split.
    exact NF.
    change 4 with (2^2). apply lxor_bound. apply mp2_mod_lt. reflexivity.
    rewrite <- (msub_mod_l 2 2) by reflexivity. change (2^2) with 4. destruct (_ mod 4) eqn:H.
      discriminate.
      assert (LT: N.pos p < 4). rewrite <- H. apply N.mod_upper_bound. discriminate.
      repeat first [ discriminate | destruct p ]. reflexivity.
  exists 0. psimpl. repeat split.
    apply nilfree0.
    apply N.mod_upper_bound. discriminate.
    destruct (_ mod 4) eqn:H.
      discriminate.
      assert (LT: N.pos p0 < 4). rewrite <- H. apply N.mod_upper_bound. discriminate.
      repeat first [ discriminate | destruct p0 ]. reflexivity.

  (* Before splitting into cases, translate each hypothesis about the
     entry point store s to each instruction's starting store s1: *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply use_satall_lemma. assumption.
    eapply strlen_preserves_esp; eassumption.
    intro ESP1. simpl in ESP1.
  eapply use_endstates_lemma. eassumption.
    apply strlen_preserves_memory.
    intro MEM1. simpl in MEM1. symmetry in MEM1. rewrite MEM in MEM1.
  eapply models_at_invariant; try eassumption. apply strlen_welltyped. intro MDL1.
  clear - PRE ESP1 MEM1 MDL1. rename t1 into t. rename s1 into s.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 32 PRE.

  (* Optional: From this point onward, the proof also ignores PF. *)
  Ltac ignore_vars v ::= constr:(match v with
  | R_AF | R_OF | R_SF | R_PF => true | _ => false end).

  (* Address 38 *)
  destruct PRE as [k [EAX [NF [EDX4 MOD4]]]].
  step. step. exists k. repeat split.
    exact NF.
    symmetry. apply Neqb_ok. assumption.
  step. step. exists (1+k). repeat split.
    rewrite N.add_1_l. apply nilfree_succ; assumption.
    rewrite <- N.add_assoc, <- N.Div0.add_mod_idemp_r, MOD4. reflexivity.

  (* Addresses 49, 75, 101, 127 *)
  1-4: destruct PRE as [k [EAX [NF [EDX0 MOD4]]]]; repeat step;
       [apply strlen_loopexit1 | apply strlen_loopexit2 | apply strlen_loopexit3 ]; assumption.

  (* Address 153 *)
  destruct PRE as [k [EAX [NF [K4 [ECX [MOD4 NIL]]]]]].
  step. step. step. replace (_=?_) with (m Ⓑ[k-4 + m Ⓓ[ 4 + esp ]] =? 0).
  step. exists (k-4). repeat split; try assumption.
    rewrite add_msub_swap, msub_sub, mp2_add_l by assumption. reflexivity.
    apply N.eqb_eq, BC.
  apply nilfree_succ in NF; cycle 1.
    apply N.eqb_neq. apply N.eqb_neq in BC. intro H. apply BC. rewrite <- H. reflexivity.
  step. step.
    change 4 with (N.succ 3) in NF at 3. rewrite <- N.sub_succ_l, N.sub_succ in NF by assumption.
    apply N.eqb_neq in BC.
    rewrite (N.add_comm 257), (add_msub_swap 16), <- (msub_msub_distr 16), msub_0_r. rewrite <- xbits_equiv.
    change 2 with (1+1). rewrite getmem_split. simpl (1+1). simpl (8*1).
    rewrite N.add_1_r, <- N.add_succ_l, succ_sub by assumption. simpl (N.pred 4).
    rewrite xbits_lor, xbits_shiftl, xbits_0_i, xbits_above, N.lor_0_l, getmem_mod_r, N.shiftl_0_r by apply getmem_bound.
  step. exists (k-3). repeat split.
    rewrite msub_sub, mp2_add_l. reflexivity.
      transitivity 4. discriminate 1. assumption.
    assumption.
    symmetry. apply N.eqb_eq. assumption.
  step. step. step.
    apply nilfree_succ in NF; [|assumption].
    rewrite succ_sub in NF by (etransitivity; [|eassumption]; discriminate).
    apply N.eqb_neq, not_eq_sym in BC0.
    rewrite (N.add_comm 65793), (add_msub_swap 24), <- (msub_msub_distr 24), msub_0_r, <- xbits_equiv.
    change 3 with (1+1+1). rewrite !getmem_split. simpl (1+1). simpl (8*_).
    rewrite (N.add_comm _ 2), N.add_assoc, (N.add_comm 2), <- (Nsub_distr k 4 2) by (discriminate 1 || assumption). simpl (4-2).
    rewrite !xbits_lor, !xbits_shiftl, xbits_0_i, !xbits_above by (eapply N.lt_le_trans; [ apply getmem_bound | discriminate 1 ]).
    rewrite !N.shiftl_0_r, N.lor_0_l, getmem_mod_r.
  step. exists (k-2). repeat split.
    rewrite msub_sub, mp2_add_l. reflexivity.
      transitivity 4. discriminate 1. assumption.
    assumption.
    symmetry. apply N.eqb_eq. assumption.
  step. exists (k-1). repeat split.
    rewrite msub_sub, mp2_add_l. reflexivity.
      transitivity 4. discriminate 1. assumption.
    change 1 with (N.pred 2). rewrite <- succ_sub.
      apply nilfree_succ; assumption.
      transitivity 4. discriminate 1. assumption.
    destruct NIL as [i [I4 NIL]].
      rewrite <- N.add_sub_assoc, (N.add_comm i), <- Nsub_distr in NIL by (assumption || apply N.lt_le_incl, I4).
      destruct i as [|i]. contradiction. repeat (destruct i as [i|i|]; try discriminate I4); simpl (_-_) in NIL.
      assumption.
      rewrite NIL in BC1. discriminate BC1.
      rewrite NIL in BC0. contradict BC0. reflexivity.

  destruct (_=?_) eqn:H.
    apply N.eqb_eq in H. rewrite H. reflexivity.
    symmetry. apply N.eqb_neq. intro H'. apply N.eqb_neq in H. apply H.
      rewrite <- getmem_mod_r, <- (add_msub_l _ 1), <- (msub_mod_l 8 8) by reflexivity. rewrite H'. reflexivity.

  (* Address 182 *)
  destruct PRE as [k [EAX [NF NIL]]].
  step. exists (k mod 2^32). psimpl. repeat split.
    intros i H. apply NF. eapply N.lt_le_trans. exact H. apply mp2_mod_le.
    assumption.
Qed.
