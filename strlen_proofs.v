Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import strlen_i386.

Import X86Notations.
Open Scope N.

(* Use a flat memory model for these proofs. *)
Definition fh := htotal.

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
  forall s n s' x,
  exec_prog fh strlen_i386 0 s n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.



(* Example #3: Architectural calling convention compliance
   Strlen does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strlen_preserves_ebx:
  forall s n s' x,
  exec_prog fh strlen_i386 0 s n s' x -> s' R_EBX = s R_EBX.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.

Theorem strlen_preserves_readable:
  forall s n s' x,
  exec_prog fh strlen_i386 0 s n s' x -> s' A_READ = s A_READ.
Proof.
  intros. eapply noassign_prog_same; [|eassumption].
  prove_noassign.
Qed.


(* Proving that strlen restores ESP on exit is our first example of a property that
   requires stepwise symbolic interpretation of the program to verify.  We first
   define a set of invariants, one for each program point.  In this simple case,
   all program points have the same invariant, so we return the same one for all. *)
Definition esp_invs (esp:N) (_:addr) (s:store) := Some (s R_ESP = Ⓓ esp).

(* Next, we define the post-condition we wish to prove: *)
Definition esp_post (esp:N) (_:exit) (s:store) := s R_ESP = Ⓓ (esp ⊕ 4).

(* The invariant set and post-condition are combined into a single invariant-set
   using the "invs" function. *)
Definition strlen_esp_invset esp :=
  invs (esp_invs esp) (esp_post esp).

(* Now we pose a theorem that asserts that this invariant-set is satisfied at
   all points in the subroutine.  The "trueif_inv" function asserts that
   anywhere an invariant exists (e.g., at the post-condition), it is true. *)
Theorem strlen_preserves_esp:
  forall s esp mem n s' x'
         (ESP0: s R_ESP = Ⓓ esp) (MEM0: s V_MEM32 = Ⓜ mem)
         (RET: strlen_i386 s (mem Ⓓ[esp]) = None)
         (XP0: exec_prog fh strlen_i386 0 s n s' x'),
  trueif_inv (strlen_esp_invset esp strlen_i386 x' s').
Proof.
  intros.

  (* Use the prove_inv inductive principle from Picinae_theory.v. *)
  eapply prove_invs. exact XP0.

  (* We must first prove the pre-condition, which says that the invariant-set is
     satisfied on entry to the subroutine.  This is proved by assumption ESP0. *)
  exact ESP0.

  (* Now we enter the inductive case, wherein Coq asks us to prove that the invariant-set
     is preserved by every (reachable) instruction in the program.  Before breaking the
     goal down into many cases (one for each instruction in this case), it is wise to
     simplify and/or remove anything in the context that is unnecessary. In order for
     symbolic interpretation to succeed, the context must reveal the values of all
     relevant variables in store s1 (which denotes the store on entry to each instruction
     for which the goal must be proved).  The only two variables in our invariant-set are
     ESP and MEM.  The value of ESP will be revealed by our pre-condition (PRE).  We can
     get the value of MEM from MEM0 using our previously proved strlen_preserves_memory
     theorem. *)
  intros.
  assert (MEM: s1 V_MEM32 = Ⓜ mem).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  rewrite (strlen_nwc s1) in RET.
  clear s MEM0 XP0 ESP0 XP.

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
Definition nilfree (m:addr->N) (p:addr) (k:N) :=
  forall i, i < k -> m (p⊕i) <> 0.

(* The invariant-set for this property is much more complex than our previous
   examples.  At the entrypoint (address 0) we have no assumptions (True).
   Addresses 38, 153, and 182 are meets in the control-flow graph, so we place
   invariants at those points to simplify the analysis.  Address 49 is the
   start of an unrolled loop, where the loop body has been replicated at
   addresses 75, 101, and 127 for better performance.  We therefore put our
   loop invariant at all four addresses so that we can treat it like a rolled
   loop, and avoid duplications in the proof logic.  Address 186 is the
   return instruction at the end, so gets a special invariant. *)
Definition Ones (b n:N) := N.iter n (fun x => x * 2^b + 1) 0.
Definition strlen_invs (m:addr->N) (esp:N) (a:addr) (s:store) :=
  let p := m Ⓓ[esp⊕4] in
  match a with
  | 0 => Some True
  | 38 => Some (∃ k edx, s R_EAX = Ⓓ(p⊕k) /\ s R_EDX = Ⓓedx /\ nilfree m p k /\
                         edx < 4 /\ (p+k) mod 4 = 3)
  | 49 | 75 | 101 | 127 => Some (∃ k, s R_EAX = Ⓓ(p⊕k) /\ nilfree m p k /\
                                      s R_EDX = Ⓓ0 /\ (p+k) mod 4 = 0)
  | 153 => Some (∃ k, s R_EAX = Ⓓ(p⊕k) /\ nilfree m p (k-4) /\ 4 <= k /\
                      s R_ECX = Ⓓ(2^32 + m Ⓓ[p⊕(k-4)] ⊖ Ones 8 4) /\ (p+k) mod 4 = 0 /\
                        ∃ i, i < 4 /\ m (p⊕(k-4+i)) = 0)
  | 182 => Some (∃ k, s R_EAX = Ⓓ(p⊕k) /\ nilfree m p k /\ m (p⊕k) = 0)
  | 186 => Some (∃ k, s R_EAX = Ⓓk /\ nilfree m p k /\ m (p⊕k) = 0)
  | _ => None
  end.

(* The post-condition says that ESP gets restored and EAX is the index of the
   first nil character after input pointer p. *)
Definition strlen_post (m:addr->N) (esp:N) (_:exit) (s:store) :=
  let p := m Ⓓ[esp⊕4] in
  s R_ESP = Ⓓ(esp⊕4) /\ ∃ k, s R_EAX = Ⓓk /\ nilfree m p k /\ m (p⊕k) = 0.

(* The invariant-set and post-conditions are combined as usual: *)
Definition strlen_invset (mem:addr->N) (esp:N) :=
  invs (strlen_invs mem esp) (strlen_post mem esp).

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

(*
Lemma Nmod_add_sub_assoc:
  forall x y z w, z <= 2^w -> z <= y ->
  (2^w + ((x + y) mod 2^w) - z) mod 2^w = (x + (y - z)) mod 2^w.
Proof.
  intros.
  rewrite N.add_sub_swap by assumption.
  rewrite N.add_mod_idemp_r by (apply N.pow_nonzero; discriminate).
  rewrite N.add_comm, <- N.add_assoc, N.add_sub_assoc, (N.add_comm y),
          <- N.add_sub_assoc, (N.add_comm (2^w)), N.add_assoc by assumption.
  rewrite <- N.add_mod_idemp_r, N.mod_same by (apply N.pow_nonzero; discriminate).
  rewrite N.add_0_r. reflexivity.
Qed.

Lemma Nmod_sub_neg:
  forall x y w, y <= 2^w -> (2^w + x - y) mod 2^w = (x + (2^w - y)) mod 2^w.
Proof.
  intros. rewrite N.add_comm. rewrite N.add_sub_assoc by assumption. reflexivity.
Qed.

Lemma Nmod_add_sub:
  forall x y w, y <= 2^w -> (2^w + (x + y) mod 2^w - y) mod 2^w = x mod 2^w.
Proof.
  intros.
  rewrite N.add_sub_swap by assumption.
  rewrite N.add_mod_idemp_r by (apply N.pow_nonzero; discriminate).
  rewrite (N.add_comm x), N.add_assoc, N.sub_add by assumption.
  rewrite <- N.add_mod_idemp_l, N.mod_same by (apply N.pow_nonzero; discriminate).
  reflexivity.
Qed.

Lemma Nmod_sub_add_less:
  forall x y z w, y <= 2^w -> z <= y ->
  ((2^w + x - y) mod 2^w + z) mod 2^w = (2^w + x - (y - z)) mod 2^w.
Proof.
  intros.
  rewrite N.add_mod_idemp_l by (apply N.pow_nonzero; discriminate).
  rewrite Nsub_distr.
    reflexivity.
    assumption.
    etransitivity. eassumption. apply N.le_add_r.
Qed.

Lemma getmem_shiftr:
  forall n2 n1 m a (WTM: welltyped_memory m),
  getmem LittleE n1 m a >> (Mb*n2) = getmem LittleE (n1-n2) m (a+n2).
Proof.
  intros. destruct (N.le_ge_cases n1 n2).

    rewrite (proj2 (N.sub_0_le _ _)), getmem_0 by assumption. eapply shiftr_low_pow2, N.lt_le_trans.
      apply getmem_bound, WTM.
      apply N.pow_le_mono_r. discriminate. apply N.mul_le_mono_l. assumption.

    rewrite <- (N.add_sub n1 n2) at 1. rewrite N.add_comm, <- N.add_sub_assoc, getmem_split by assumption.
    rewrite N.shiftr_lor, N.shiftr_shiftl_r, N.sub_diag, N.shiftr_0_r by apply N.le_refl.
    rewrite shiftr_low_pow2 by apply getmem_bound, WTM. reflexivity.
Qed.
*)

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
    apply Nlt_0_pow2.
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
  rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate 1).
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
  forall mem i a (WTM: welltyped_memory mem)
         (H: forall j, j < i -> mem (a + j) <> 0),
  Ones Mb i <= getmem LittleE i mem a.
Proof.
  intros mem i a WTM. revert a. induction i using N.peano_ind; intros.
    reflexivity.
    rewrite Ones_succ, getmem_succ, lor_plus.
      rewrite N.add_comm. apply N.add_le_mono.
        apply N.lt_pred_le, N.neq_0_lt_0. rewrite <- (N.add_0_r a). apply H. apply N.lt_0_succ.
        rewrite N.shiftl_mul_pow2. apply N.mul_le_mono_nonneg_r.
          apply N.le_0_l.
          apply IHi. intros. rewrite N.add_succ_comm. apply H. apply -> N.succ_lt_mono. assumption.
      apply land_lohi_0, WTM.
Qed.

Lemma below_ones:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: getmem LittleE w mem a < Ones Mb w),
  exists i, i < w /\ mem (a+i) = 0.
Proof.
  intros mem w a WTM. revert a. induction w using N.peano_ind; intros.
    contradict GM. apply N.nlt_0_r.
    rewrite Ones_succ, getmem_succ in GM. destruct (mem a) eqn:M0.
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
      apply (N.mul_lt_mono_pos_r (2^y)), (N.add_lt_mono_l _ _ (N.pos x mod 2^y)). apply Nlt_0_pow2.
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
  rewrite <- N.mul_sub_distr_r, testbit_pred, N.mod_add, N.mod_mod by (apply N.pow_nonzero; discriminate).
  rewrite 2!N.testbit_odd, (N.shiftr_div_pow2 (_+_)), N.div_add by (apply N.pow_nonzero; discriminate).
  rewrite (N.div_small (_ mod _)) by (apply N.mod_lt, N.pow_nonzero; discriminate).
  rewrite N.add_0_l, N.odd_sub, H4 by apply YX.
  unfold N.lnot. rewrite 2!N.shiftr_lxor, (N.shiftr_shiftr (N.ones _)), (N.shiftr_div_pow2 (N.ones _)).
  rewrite N.ones_div_pow2 by (rewrite N.add_comm; apply N.lt_le_incl, H3).
  rewrite Nxor_bit0, odd_ones by (rewrite N.add_comm; apply N.sub_gt, H3).
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
  forall mem w a (WTM: welltyped_memory mem)
         (GM: Ones Mb w <= getmem LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE w mem a) (Mb*w))
                              (getmem LittleE w mem a - Ones Mb w))
                      (Ones Mb w - 1) = 0)
         i (IW: i < w),
  mem (a + i) <> 0.
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

  rewrite Ones_split, getmem_split in GM.
  rewrite lor_plus in GM by apply land_lohi_0, getmem_bound, WTM.
  rewrite N.shiftl_mul_pow2 in GM.
  apply (N.div_le_mono _ _ (2^(Mb*i))) in GM; [|apply N.pow_nonzero; discriminate 1].
  do 2 rewrite N.div_add in GM by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in GM by apply Ones_bound.
  rewrite N.div_small in GM by apply getmem_bound, WTM.
  apply N.le_succ_l. rewrite <- N.add_1_r, <- Ones_succ, getmem_split.
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
    apply N.neq_0_lt_0. eapply N.lt_le_trans. apply N.lt_0_1. rewrite N.add_0_r. etransitivity.
      exact GM.
      rewrite getmem_succ, N.lor_0_r. reflexivity.

    rewrite <- N.add_succ_comm. apply IHi.
    rewrite getmem_succ, Ones_succ in GM.
    apply (N.div_le_mono _ _ (2^Mb)) in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_add_l in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_small, N.add_0_r in GM; [|reflexivity].
    etransitivity. exact GM.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor, N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r, shiftr_low_pow2, N.lor_0_l.
      reflexivity. apply WTM. reflexivity.
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
          apply N.pow_le_mono_r. discriminate 1. apply N.mul_div_le; assumption.
          assumption.
        apply N.pow_nonzero. discriminate 1.
    eapply N.mul_lt_mono_pos_l. apply Nlt_0_pow2. eapply N.le_lt_trans.
      apply N.mul_div_le, N.pow_nonzero. discriminate 1.
      rewrite <- N.pow_add_r, <- N.mul_succ_r. eapply N.lt_le_trans.
        exact HI.
        apply N.pow_le_mono_r. discriminate 1. apply N.le_succ_l, N.mul_succ_div_gt. exact B0.
Qed.

Theorem borrow_nil:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: Ones Mb w <= getmem LittleE w mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE w mem a) (Mb*w))
                              (getmem LittleE w mem a - Ones Mb w))
                      (Ones Mb w - 1) <> 0),
  exists i, i < w /\ mem (a + i) = 0.
Proof.
  intros.
  destruct w as [|w]. contradict TST. rewrite N.land_0_r. reflexivity.
  rewrite <- (N.succ_pos_pred w) in *.
  apply (lsd_pos Mb) in TST; [|discriminate 1]. destruct TST as [j TST].

  rewrite <- N.shiftr_div_pow2, N.shiftr_land, <- N.land_ones, <- N.land_assoc in TST.

  destruct j as [|j].
  rewrite N.mul_0_r, (N.shiftr_0_r (_-_)), Ones_succ, N.add_sub, <- N.shiftl_mul_pow2, (N.land_comm _ (N.ones _)) in TST.
  rewrite land_lohi_0 in TST by reflexivity.
  contradict TST. apply N.land_0_r.

  rewrite Ones_succ in TST at 2.
  rewrite N.add_sub, <- N.shiftl_mul_pow2 in TST.
  rewrite N.shiftr_shiftl_r in TST by (rewrite <- (N.mul_1_r Mb) at 1; apply N.mul_le_mono_l; destruct j; discriminate 1).
  rewrite <- N.mul_pred_r in TST.
  destruct (N.le_gt_cases (N.pos j) (Pos.pred_N w)) as [JW|JW]; [|
    contradict TST;
    rewrite (shiftr_low_pow2 (Ones _ _)) by (eapply N.lt_le_trans; [ apply Ones_bound | apply N.pow_le_mono_r ; [ discriminate 1 | apply N.mul_le_mono_l, N.lt_le_pred, JW] ]);
    apply N.land_0_r ].
  rewrite <- (N.sub_add (N.pos j) (Pos.pred_N w)) in TST at 5 by exact JW.
  rewrite N.add_comm, Ones_split, (N.shiftr_div_pow2 (_+_)) in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 2 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb), N.pow_add_r, N.mul_assoc in TST.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite (Ones_succ_top _ (N.pred _)) in TST.
  rewrite <- (N.mul_1_l (2^(_*N.pred _))) in TST at 1.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in TST by apply Ones_bound.
  rewrite N.land_ones in TST.
  rewrite N.mod_add in TST by (apply N.pow_nonzero; discriminate 1).
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
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb) in TST.

  destruct (N.le_gt_cases (Ones Mb (N.pred (N.pos j))) (getmem LittleE (N.pred (N.pos j)) mem a)) as [LOJ|LOJ].

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
    destruct (mem _). reflexivity. contradict TST. reflexivity.

  apply N.le_succ_l. rewrite <- N.add_1_r, <- Ones_succ.
  rewrite <- N.sub_succ_l by apply N.le_le_pred, JW.
  rewrite <- (N.add_0_l (Ones _ _)).
  rewrite <- (N.div_small (Ones Mb (N.pred (N.pos j))) (2^(Mb * N.pred (N.pos j)))) by apply Ones_bound.
  rewrite <- N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite <- Ones_split.
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

  rewrite <- (N.succ_pred (_-_)), Ones_succ.
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

Lemma nilfree0: forall m p, nilfree m p 0.
Proof. intros m p i H1. destruct i; discriminate. Qed.

Lemma nilfree_succ:
  forall m p k (BC: (0 =? m (p⊕k)) = false) (NF: nilfree m p k),
  nilfree m p (N.succ k).
Proof.
  intros. intros i H. apply N.lt_succ_r, N.le_lteq in H. destruct H.
    revert i H. exact NF.
    subst. apply N.neq_sym, N.eqb_neq. exact BC.
Qed.

Lemma add_assoc_mod4:
  forall x y z, (x+y) mod 4 = 0 -> z < 4 -> x ⊕ (y + z) = x ⊕ y + z.
Proof.
  intros.
  rewrite N.add_assoc, <- N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small (_+z)). reflexivity.
  rewrite (N.div_mod' (x+y) 4), H, N.add_0_r.
  change (2^32) with (4*2^30). rewrite N.mul_mod_distr_l by discriminate.
  change (4*2^30) with (4*(N.pred (2^30))+4). apply N.add_le_lt_mono; [|assumption].
  apply N.mul_le_mono_pos_l. reflexivity. apply N.lt_le_pred, N.mod_upper_bound. discriminate.
Qed.

Lemma strlen_loopexit1:
  forall m p k (WTM: welltyped_memory m) (NF: nilfree m p k)
         (PK4: (p + k) mod 4 = 0)
         (BC1: (m Ⓓ[p⊕k] ⊕ 4278124287 <? m Ⓓ[p⊕k]) = true)
         (BC2: (0 =? (2^32 - m Ⓓ[p⊕k] - 1) .^ (m Ⓓ[p⊕k] + 16711423) .& 16843008) = true),
  ∃ k0, (Ⓓ (p + k ⊕ 4) : value) = Ⓓ (p ⊕ k0) /\
        nilfree m p k0 /\
        Ⓓ ((2^32 - m Ⓓ[p⊕k] - 1) .^ (m Ⓓ[p⊕k] + 16711423) .& 16843008) = Ⓓ 0 /\
        (p + k0) mod 4 = 0.
Proof.
  intros.

  assert (LE: Ones 8 4 <= m Ⓓ[ p ⊕ k ]).
    apply (add_sub_mod_le _ (2^32)). discriminate. apply N.ltb_lt, BC1.

  exists (k+4). repeat split.
    rewrite N.add_assoc. reflexivity.
    intros i H. destruct (N.lt_ge_cases i k).
      apply NF; assumption.

      rewrite <- (N.sub_add k i) by assumption.
      rewrite (N.add_comm _ k). rewrite N.add_assoc.
      rewrite <- N.add_mod_idemp_l by discriminate.
      rewrite N.mod_small.
        apply noborrow_nonil with (w:=4).
          exact WTM.
          exact LE.

          rewrite sub_lnot by apply getmem_bound, WTM.
          change (Ones Mb 4 - 1) with (N.ones 25 .& 16843008).
          rewrite N.land_assoc, N.land_ones, N_lxor_mod_pow2.
          rewrite <- (N.mod_add (_ - Ones Mb 4) 1), <- N.add_sub_swap, <- N.add_sub_assoc by
            first [ discriminate 1 | apply LE ].
          rewrite <- N_lxor_mod_pow2, <- N.land_ones, <- N.land_assoc.
          symmetry. apply Neqb_ok. apply BC2.

          eapply N.add_lt_mono_l. rewrite N.add_comm, N.sub_add; assumption.
        rewrite <- add_assoc_mod4.
          apply N.mod_upper_bound. discriminate.
          assumption.
          eapply N.add_lt_mono_l. rewrite N.add_comm, N.sub_add; assumption.

    apply Neqb_ok in BC2. rewrite <- BC2. reflexivity.
    rewrite N.add_assoc, <- N.add_mod_idemp_l, PK4 by discriminate. reflexivity.
Qed.

Lemma strlen_loopexit2:
  forall m p k (WTM: welltyped_memory m) (NF: nilfree m p k) (PK4: (p+k) mod 4 = 0)
         (BC1: (m Ⓓ[p⊕k] ⊕ 4278124287 <? m Ⓓ[p⊕k]) = true)
         (BC2: (0 =? (2^32 - m Ⓓ[p⊕k] - 1) .^ (m Ⓓ[p⊕k] + 16711423) .& 16843008) = false),
  ∃ k0, (Ⓓ (p + k ⊕ 4) : value) = Ⓓ (p ⊕ k0) /\
        nilfree m p (k0 - 4) /\
        4 <= k0 /\
        Ⓓ (m Ⓓ[p⊕k] ⊕ 4278124287) = Ⓓ (2^32 + m Ⓓ[p⊕(k0-4)] ⊖ Ones 8 4) /\
        (p+k0) mod 4 = 0 /\
        (∃ i, i < 4 /\ m (p ⊕ (k0 - 4 + i)) = 0).
Proof.
  intros.

  assert (LE: Ones 8 4 <= m Ⓓ[ p ⊕ k ]).
    apply (add_sub_mod_le _ (2^32)). discriminate. apply N.ltb_lt, BC1.

  exists (k+4). rewrite N.add_sub. repeat split.
    rewrite N.add_assoc. reflexivity.
    exact NF.
    rewrite N.add_comm. apply N.le_add_r.
    change 4278124287 with (2^32 - Ones 8 4). rewrite N.add_sub_assoc, N.add_comm by discriminate. reflexivity.
    rewrite N.add_assoc, <- N.add_mod_idemp_r, N.add_0_r by discriminate. assumption.

    rewrite <- sub_lnot in BC2 by apply getmem_bound, WTM.
    change 16711423 with (1*2^25 - Ones 8 4) in BC2.
    rewrite N.add_sub_assoc, N.add_sub_swap in BC2; [| apply LE | discriminate].
    change 16843008 with (N.ones 25 .& 16843008) in BC2.
    rewrite N.land_assoc, N.land_ones, N_lxor_mod_pow2, N.mod_add in BC2 by discriminate.
    rewrite <- N_lxor_mod_pow2, <- N.land_ones, <- N.land_assoc in BC2.
    apply N.eqb_neq, N.neq_sym, borrow_nil in BC2; try assumption.
    destruct BC2 as [i [I4 NIL]]. exists i. split. exact I4.
    rewrite add_assoc_mod4; assumption.
Qed.

Lemma strlen_loopexit3:
  forall m p k (WTM: welltyped_memory m) (NF: nilfree m p k) (PK4: (p+k) mod 4 = 0)
         (BC: (m Ⓓ[p⊕k] ⊕ 4278124287 <? m Ⓓ[p⊕k]) = false),
  ∃ k0, Ⓓ (p + k ⊕ 4) = Ⓓ (p ⊕ k0) /\
        nilfree m p (k0 - 4) /\
        4 <= k0 /\
        Ⓓ (m Ⓓ[p⊕k] ⊕ 4278124287) = Ⓓ (2^32 + m Ⓓ[ p ⊕ (k0 - 4) ] ⊖ Ones 8 4) /\
        (p+k0) mod 4 = 0 /\
        (∃ i, i < 4 ∧ m (p ⊕ (k0 - 4 + i)) = 0).
Proof.
  change 4278124287 with (2^32 - Ones 8 4).
  intros. exists (k+4). rewrite N.add_sub. repeat split.
    rewrite N.add_assoc. reflexivity.
    exact NF.
    rewrite N.add_comm. apply N.le_add_r.
    rewrite N.add_sub_assoc, N.add_comm by discriminate. reflexivity.
    rewrite N.add_assoc, <- N.add_mod_idemp_r, N.add_0_r by discriminate. assumption.

    apply N.ltb_ge, le_add_sub_mod in BC; [|reflexivity].
    apply below_ones in BC; [|exact WTM].
    destruct BC as [i [I4 NIL]]. exists i. split. exact I4.
    rewrite add_assoc_mod4; assumption.
Qed.

(* Finally we're ready to prove the main partial correctness theorem. *)
Theorem strlen_partial_correctness:
  forall s esp m n s' x
         (MDL0: models x86typctx s)
         (ESP0: s R_ESP = Ⓓesp) (MEM0: s V_MEM32 = Ⓜm)
         (RET: strlen_i386 s (m Ⓓ[esp]) = None)
         (XP0: exec_prog fh strlen_i386 0 s n s' x),
  trueif_inv (strlen_invset m esp strlen_i386 x s').
Proof.
  intros.
  eapply prove_invs. exact XP0.

  (* The pre-condition (True) is trivially satisfied. *)
  exact I.

  (* Before splitting into cases, translate each hypothesis about the
     entry point store s to each instruction's starting store s1: *)
  intros.
  assert (MDL: models x86typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strlen_welltyped. exact XP.
  assert (MEM: s1 V_MEM32 = Ⓜm).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  assert (WTM := x86_wtm MDL MEM). simpl in WTM.
  rewrite (strlen_nwc s1) in RET.
  assert (ESP := strlen_preserves_esp _ _ _ _ _ (Exit a1) ESP0 MEM0 RET XP).
  clear s MDL0 MEM0 ESP0 XP XP0.

  (* Break the proof into cases, one for each invariant-point. *)
  destruct_inv 32 PRE.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)
  Local Ltac step := time x86_step.

  (* Address 0 *)
  step. step. step. step. exists 0. repeat split.
    rewrite N.add_0_r, (N.mod_small (getmem _ _ _ _)). reflexivity. apply getmem_bound, WTM.
    intros i H1. destruct i; discriminate.
    rewrite <- (Neqb_ok _ _ BC). reflexivity.
    rewrite N.add_0_r. symmetry. apply Neqb_ok, BC.
  step. step. step. exists 0.
    rewrite N.add_0_r, (N.mod_small (getmem _ _ _ _)) by apply getmem_bound, WTM.
    repeat split. apply nilfree0. symmetry. apply Neqb_ok. assumption.
  eassert (NF: nilfree m _ _).
    apply nilfree_succ; [|apply nilfree0].
    rewrite N.add_0_r. rewrite N.mod_small. exact BC1. apply getmem_bound, WTM.
  step. step. step. exists 1. repeat split.
    apply NF.
    symmetry. apply Neqb_ok. assumption.
  apply nilfree_succ in NF; [|exact BC2].
  step. step. step. apply Neqb_ok, eq_sym in BC3. exists 2. repeat split.
    exact NF.
    rewrite BC3. reflexivity.
    apply N.lxor_eq in BC3. rewrite N.add_mod, BC3 by discriminate. reflexivity.
  exists 2. eexists. repeat split.
    exact NF.
    change 4 with (2^2) at 4. apply lxor_bound. apply N.mod_upper_bound. discriminate. reflexivity.
    rewrite <- N.add_mod_idemp_l by discriminate. destruct (_ mod 4) eqn:H.
      discriminate.
      assert (LT: N.pos p < 4). rewrite <- H. apply N.mod_upper_bound. discriminate.
      repeat first [ discriminate | destruct p ]. reflexivity.
  exists 0. eexists. repeat split.
    rewrite N.add_0_r, (N.mod_small (getmem _ _ _ _)) by apply getmem_bound, WTM. reflexivity.
    apply nilfree0.
    change 4 with (2^2) at 3. apply N.mod_upper_bound. discriminate.
    rewrite N.add_0_r. destruct (_ mod 4) eqn:H.
      discriminate.
      assert (LT: N.pos p0 < 4). rewrite <- H. apply N.mod_upper_bound. discriminate.
      repeat first [ discriminate | destruct p0 ]. reflexivity.

  (* Address 38 *)
  destruct PRE as [k [edx [EAX [EDX [NF [EDX4 MOD4]]]]]].
  step. step. exists k. repeat split.
    exact NF.
    symmetry. apply Neqb_ok. assumption.
  step. step. exists (N.succ k). repeat split.
    rewrite <- N.add_assoc, N.add_1_r. reflexivity.
    apply nilfree_succ; assumption.
    rewrite <- N.add_1_r, N.add_assoc, <- N.add_mod_idemp_l, MOD4 by discriminate. reflexivity.

  (* Addresses 49, 75, 101, 127 *)
  1-4: destruct PRE as [k [EAX [NF [EDX0 MOD4]]]]; (repeat step;
       [ apply strlen_loopexit1 | apply strlen_loopexit2 | apply strlen_loopexit3 ]; assumption).

  (* Address 153 *)
  destruct PRE as [k [EAX [NF [K4 [ECX [MOD4 NIL]]]]]].
  assert (PKI: forall i, i < 4 -> m Ⓓ[esp⊕4] ⊕ (k-4) + i = m Ⓓ[esp⊕4] ⊕ (k-(4-i))).
    intros. rewrite <- (N.mod_small (_+i) (2^32)).
      rewrite (N.add_mod_idemp_l (_+(k-4))), <- N.add_assoc, <- (Nsub_distr k 4 i);
        solve [ discriminate | reflexivity | assumption | apply N.lt_le_incl; assumption ].

      change (2^32) with (2^32-4+4) at 3. apply N.add_le_lt_mono; [|assumption].
      rewrite N.add_sub_assoc, (N.div_mod' (_+k) 4), MOD4, N.add_0_r by assumption.
      change 4 with (4*1) at 5. change (2^32) with (4*2^30) at 2. change (2^32 - 4) with (4*N.pred (2^30)).
      rewrite <- N.mul_sub_distr_l, N.mul_mod_distr_l by discriminate.
      apply N.mul_le_mono_l, N.lt_le_pred, N.mod_upper_bound. discriminate.
  step. step. step.
    rewrite (N.add_comm _ (getmem _ _ _ _)), <- (N.add_sub_assoc _ _ (Ones 8 4)) by discriminate.
    rewrite (N.add_comm _ (_+(_-_))), <- (N.add_sub_assoc _ _ 4278124287), <- N.add_assoc by discriminate.
    simpl (_-_+(_-_)).
    rewrite (N.add_comm (2^8)), <- (N.add_sub_assoc _ _ 255), <- (N.add_assoc _ (_-_)) by discriminate.
    simpl (_-_+(_-_)).
  step. exists (k-4). repeat split.
    rewrite <- N.add_sub_assoc.
      rewrite <- N.add_sub_assoc by exact K4. psimpl_goal. reflexivity.
      transitivity k. apply K4. rewrite N.add_comm. apply N.le_add_r.
    exact NF.
    symmetry. apply Neqb_ok, BC.
  apply (nilfree_succ _ _ _ BC) in NF. rewrite <- N.add_1_r, <- Nsub_distr in NF by (discriminate + exact K4).
  step. step. rewrite PKI by (reflexivity + exact WTM).
  step. exists (k-3). repeat split.
    rewrite <- Nsub_distr, <- !N.add_sub_assoc. psimpl_goal. reflexivity.
      transitivity 4. discriminate. exact K4.
      transitivity 4. discriminate. transitivity k. exact K4. rewrite N.add_comm. apply N.le_add_r.
      discriminate.
      transitivity (2^32). discriminate. apply N.le_add_r.
    exact NF.
    symmetry. apply Neqb_ok. exact BC0.
  apply (nilfree_succ _ _ _ BC0) in NF. rewrite <- N.add_1_r, <- Nsub_distr in NF;
    [|discriminate | transitivity 4; [ discriminate | exact K4 ]].
  step. step. step. rewrite PKI by (reflexivity + exact WTM).
  step. exists (k-2). repeat split.
    rewrite <- Nsub_distr, N.add_assoc, <- N.add_sub_assoc, <- N.add_assoc, <- N.add_mod_idemp_l, N.mod_same, N.add_0_l;
      try (discriminate || reflexivity).
      transitivity 4. discriminate. exact K4.
      etransitivity; [|apply N.le_add_r]. discriminate.
    exact NF.
    symmetry. apply Neqb_ok. exact BC1.
  apply (nilfree_succ _ _ _ BC1) in NF. rewrite <- N.add_1_r, <- Nsub_distr in NF;
    [|discriminate | transitivity 4; [ discriminate | exact K4 ]].
  step. exists (k-1). repeat split.
    rewrite <- Nsub_distr, N.add_assoc, <- N.add_sub_assoc, <- N.add_assoc, <- N.add_mod_idemp_l, N.add_0_l;
      try (discriminate || reflexivity).
      transitivity 4. discriminate. exact K4.
      etransitivity; [|apply N.le_add_r]. discriminate.
    exact NF.

    destruct NIL as [i [H NIL]]. change 4 with (N.succ (N.succ (N.succ (N.succ 0)))) in H.
    repeat (apply N.lt_succ_r, N.le_lteq in H; destruct H as [H|H]);
    [ destruct i; discriminate
    | subst i; rewrite <- Nsub_distr in NIL by (discriminate || exact K4);
      simpl (k-_) in NIL; rewrite NIL in *; (discriminate || reflexivity)..].

  (* Address 182 *)
  destruct PRE as [k [EAX [NF NIL]]].
  step. exists (k mod 2^32). repeat split.
    rewrite (N.add_comm _ k), N.add_assoc, N.add_sub, <- N.add_mod_idemp_l, N.add_0_l by discriminate. reflexivity.
    intros i H. apply NF. eapply N.lt_le_trans. exact H. apply N.mod_le. discriminate.
    rewrite N.add_mod_idemp_r by discriminate. exact NIL.

  (* Address 186 *)
  destruct PRE as [k [EAX [NF NIL]]].
  step. split; simpl_stores. reflexivity. exists k. repeat split; assumption.
Qed.
