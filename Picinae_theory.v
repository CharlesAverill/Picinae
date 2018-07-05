(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Interpreter Theory module:                          MMMMMMMMMMMMMMMMM^NZMMN+Z
   * quantification over IL syntax,                     MMMMMMMMMMMMMMM/.$MZM8O+
   * theory of store-updates and memory-accesses,        MMMMMMMMMMMMMM7..$MNDM+
   * theory of two's-complement binary numbers,           MMDMMMMMMMMMZ7..$DM$77
   * determinism of Unknown-free programs,                 MMMMMMM+MMMZ7..7ZM~++
   * monotonicity of stores,                                MMMMMMMMMMM7..ZNOOMZ
   * boundedness of While-free programs,                     MMMMMMMMMM$.$MOMO=7
   * inductive schemas for program analysis,                  MDMMMMMMMO.7MDM7M+
   * frame theorems for assignment-free programs, and          ZMMMMMMMM.$MM8$MN
   * functional interpretation of statements.                  $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
   To compile this module, first load the Picinae_core           ?MMMMMZ..MZM$ZZ
   module and compile it with menu option                         ?$MMMZ7.ZZM7DZ
   Compile->Compile_buffer.                                         7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import FunctionalExtensionality.
Require Setoid.



Module PicinaeTheory (Arch: Architecture).

Module PCore := PicinaeCore Arch.
Export PCore.
Open Scope N.

(* Convenience lemmas for inverted reasoning about typof_val. *)

Lemma value_bound:
  forall n w (TV: typof_val (VaN n w) (NumT w)), n < 2^w.
Proof. intros. inversion TV. assumption. Qed.

Lemma mem_welltyped:
  forall m w (TV: typof_val (VaM m w) (MemT w)), welltyped_memory m.
Proof. intros. inversion TV. assumption. Qed.


Section Quantification.

(* Recursive quantification of sub-expressions and sub-statements: *)

Fixpoint exps_in_exp {T:Type} (C:T->T->T) (P:exp->T) (e:exp) : T :=
  match e with
  | Var _ | Word _ _ | Unknown _ => P e
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => C (P e) (exps_in_exp C P e1)
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (exps_in_exp C P e2))
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (C (exps_in_exp C P e2) (exps_in_exp C P e3)))
  end.

Fixpoint exps_in_stmt {T:Type} (C:T->T->T) (b:T) (P:exp->T) (q:stmt) : T :=
  match q with
  | Nop | CpuExn _ => b
  | Move _ e | Jmp e => exps_in_exp C P e
  | Seq q1 q2 => C (exps_in_stmt C b P q1) (exps_in_stmt C b P q2)
  | While e q0 => C (exps_in_exp C P e) (exps_in_stmt C b P q0)
  | If e q1 q2 => C (exps_in_exp C P e) (C (exps_in_stmt C b P q1) (exps_in_stmt C b P q2))
  end.

Fixpoint stmts_in_stmt {T:Type} (C:T->T->T) (P:stmt->T) (q:stmt) : T :=
  match q with
  | Nop | CpuExn _ | Move _ _ | Jmp _ => P q
  | While _ q0 => C (P q) (stmts_in_stmt C P q0)
  | Seq q1 q2 | If _ q1 q2 => C (P q) (C (stmts_in_stmt C P q1) (stmts_in_stmt C P q2))
  end.

Definition forall_exps_in_exp := exps_in_exp and.
Definition forall_exps_in_stmt := exps_in_stmt and True.
Definition exists_exp_in_exp := exps_in_exp or.
Definition exists_exp_in_stmt := exps_in_stmt or False.
Definition forall_stmts_in_stmt := stmts_in_stmt and.
Definition exists_stmt_in_stmt := stmts_in_stmt or.
Definition forall_exps_in_prog P (p:program) :=
  forall a q sz, p a = Some (sz,q) -> forall_exps_in_stmt P q.
Definition exists_exp_in_prog P (p:program) :=
  exists a q sz, p a = Some (sz,q) /\ exists_exp_in_stmt P q.
Definition forall_stmts_in_prog P (p:program) :=
  forall a q sz, p a = Some (sz,q) -> forall_stmts_in_stmt P q.
Definition exists_stmt_in_prog P (p:program) :=
  exists a q sz, p a = Some (sz,q) /\ exists_stmt_in_stmt P q.

End Quantification.


Section StoreTheory.

(* The getmem/setmem memory accessors are defined as Peano recursions over N,
   rather than natural number recursions.  This is important for keeping proof
   terms small, but can make it more difficult to write inductive proofs.  To
   ease this burden, we here define machinery for inductively reasoning about
   getmem/setmem.

   Proofs that inductively expand getmem/setmem should typically perform the
   following steps:

   (1) Use Peano induction to induct over length argument:
         induction len using N.peano_ind.

   (2) Within the proof, unfold the base case (where len=0) using the getmem_0
       or setmem_0 theorems.

   (3) Unfold inductive cases (where len = N.succ _) using the getmem_succ
       or setmem_succ theorems. *)

(* Base cases for getmem/setmem *)
Theorem getmem_0: forall e m a, getmem e N0 m a = N0.
Proof. reflexivity. Qed.

Theorem setmem_0: forall e m a v, setmem e N0 m a v = m.
Proof. reflexivity. Qed.

(* Unfold getmem/setmem by one byte (for inductive cases of proofs). *)
Theorem getmem_succ:
  forall e len m a, getmem e (N.succ len) m a =
    match e with BigE => N.lor (getmem e len m (N.succ a)) (N.shiftl (m a) (Mb*len))
               | LittleE => N.lor (m a) (N.shiftl (getmem e len m (N.succ a)) Mb)
    end.
Proof.
  intros. unfold getmem.
  rewrite (N.recursion_succ (@eq (addr->N))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

Theorem setmem_succ:
  forall e len m a v, setmem e (N.succ len) m a v =
    match e with BigE => setmem e len (update N.eq_dec m a (N.shiftr v (Mb*len))) (N.succ a) (v mod 2^(Mb*len))
               | LittleE => setmem e len (update N.eq_dec m a match len with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
    end.
Proof.
  intros. unfold setmem.
  rewrite (N.recursion_succ (@eq ((addr->N)->addr->N->(addr->N)))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

(* special cases for when getmem/setmem are applied to access a single memory byte *)
Corollary getmem_1: forall e m a, getmem e 1 m a = m a.
Proof.
  intros. change 1 with (N.succ 0).
  rewrite getmem_succ, getmem_0, N.mul_0_r, N.shiftl_0_r, N.lor_0_l, N.lor_0_r.
  destruct e; reflexivity.
Qed.

Corollary setmem_1: forall e, setmem e 1 = update N.eq_dec.
Proof.
  intros. extensionality m. extensionality a. extensionality v.
  change 1 with (N.succ 0).
  rewrite setmem_succ, !setmem_0, N.mul_0_r, N.shiftr_0_r.
  destruct e; reflexivity.
Qed.


(* Break an (i+j)-byte number read/stored to/from memory into two numbers of size i and j. *)
Theorem getmem_split:
  forall e i j m a, getmem e (i+j) m a =
    match e with BigE => N.lor (getmem e j m (a+i)) (N.shiftl (getmem e i m a) (Mb*j))
               | LittleE => N.lor (getmem e i m a) (N.shiftl (getmem e j m (a+i)) (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, getmem_0, N.shiftl_0_l, N.shiftl_0_r, N.lor_0_r, N.lor_0_l. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, getmem_succ, N.add_succ_l. destruct e.
      rewrite N.shiftl_lor, N.shiftl_shiftl, N.lor_assoc, <- IHi, <- N.mul_add_distr_l. apply getmem_succ.
      rewrite (N.mul_succ_r _ i), <- N.shiftl_shiftl, <- N.lor_assoc, <- N.shiftl_lor, <- IHi. apply getmem_succ.
Qed.

Theorem setmem_split:
  forall e i j m a v, setmem e (i+j) m a v =
    match e with BigE => setmem e j (setmem e i m a (N.shiftr v (Mb*j))) (a+i) match i with N0 => v | Npos _ => v mod 2^(Mb*j) end
               | LittleE => setmem e j (setmem e i m a match j with N0 => v | Npos _ => v mod 2^(Mb*i) end) (a+i) (N.shiftr v (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, N.shiftr_0_r, setmem_0, setmem_0. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, !setmem_succ, N.add_succ_l. destruct e.

      rewrite <- (N.succ_pos_spec i), N.shiftr_shiftr, <- N.mul_add_distr_l, (N.add_comm j), setmem_succ, IHi.
      rewrite <- N.land_ones, <- N.land_ones, N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
      rewrite N.ones_div_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.mul_add_distr_l at 2. rewrite N.add_sub, N.land_ones, <- N.land_assoc, N.land_ones, N.land_ones.
      rewrite N.ones_mod_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.land_ones. destruct i; reflexivity.

      rewrite setmem_succ, IHi. destruct j.
        rewrite N.add_0_r, setmem_0, setmem_0. reflexivity.
        destruct i.
          rewrite N.mul_0_r, N.add_0_l, setmem_0, setmem_0, N.mul_1_r, N.shiftr_0_r. reflexivity.
          destruct (N.pos _ + N.pos _) eqn:H.
            apply N.eq_add_0 in H. destruct H. discriminate H.

            rewrite N.shiftr_shiftr.
            rewrite <- (N.land_ones _ (_*N.succ _)), <- (N.land_ones (N.land _ _)), <- N.land_assoc.
            rewrite N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
            rewrite N.land_ones.
            rewrite N.ones_mod_pow2, N.ones_div_pow2 by (rewrite N.mul_succ_r, N.add_comm; apply N.le_add_r).
            rewrite N.land_ones, N.land_ones, N.mul_succ_r, N.add_sub, (N.add_comm (_*_)).
            reflexivity.
Qed.


(* Symmetric updates preserve the partial order relation. *)

Theorem pfsub_update {A B} {eq: forall (a b:A), {a=b}+{a<>b}}:
  forall (f g: A -> option B) (SS: f ⊆ g) (x:A) (y:option B),
  update eq f x y ⊆ update eq g x y.
Proof.
  intros. unfold update. intros z y' H. destruct (eq z x).
    assumption.
    apply SS. assumption. 
Qed.

Definition updateall {A B:Type} (f g: A -> option B) (x:A) : option B :=
  match g x with None => f x | Some y => Some y end.

Theorem updateall_subset {A B}:
  forall (f g: A->option B), f ⊆ g -> updateall g f = g.
Proof.
  unfold pfsub, updateall. intros.
  apply functional_extensionality. intro x. specialize H with (x:=x). destruct (f x).
    symmetry. apply H. reflexivity.
    reflexivity.
Qed.

Theorem subset_updateall {A B}:
  forall (f g: A->option B), f ⊆ updateall g f.
Proof. unfold pfsub, updateall. intros. rewrite H. reflexivity. Qed.

(* Frame property: Updating variable x does not affect the value of any other variable z. *)
Theorem update_frame:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y z (NE: z<>x),
  update eq s x y z = s z.
Proof.
  intros. unfold update. destruct (eq z x).
    exfalso. apply NE. assumption.
    reflexivity.
Qed.

(* Updating x and then reading it returns its new value. *)
Theorem update_updated:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y,
  update eq s x y x = y.
Proof.
  intros. unfold update. destruct (eq x x).
    reflexivity.
    exfalso. apply n. reflexivity.
Qed.

(* Reversing the order of assignments to two different variables yields the same store. *)
Theorem update_swap:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y})
         (s:A->B) x1 x2 y1 y2 (NE:x1<>x2),
  update eq (update eq s x1 y1) x2 y2 = update eq (update eq s x2 y2) x1 y1.
Proof.
  intros. extensionality z. unfold update.
  destruct (eq z x2).
    subst z. destruct (eq x2 x1).
      exfalso. apply NE. symmetry. assumption.
      reflexivity.
    destruct (eq z x1); reflexivity.
Qed.

(* Overwriting a store value discards the earlier update. *)
Theorem update_cancel:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y1 y2,
  update eq (update eq s x y1) x y2 = update eq s x y2.
Proof.
  intros. apply functional_extensionality. intro z. unfold update.
  destruct (eq z x); reflexivity.
Qed.

(* Equivalent updates within a sequence of updates can be disregarded when searching
   for updates that cancel each other via update_cancel. *)
Theorem update_inner_same:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s1 s2:A->B) x1 y1 x2 y2,
    update eq s1 x2 y2 = update eq s2 x2 y2 ->
  update eq (update eq s1 x1 y1) x2 y2 = update eq (update eq s2 x1 y1) x2 y2.
Proof.
  intros. destruct (eq x1 x2).
    subst x2. do 2 rewrite update_cancel. assumption.
    rewrite (update_swap eq s1), (update_swap eq s2) by assumption. rewrite H. reflexivity.
Qed.

(* If variable v's value u is known for store s, then s[v:=u] is the same as s.
   This fact is useful for "stocking" store expressions with explicit updates that
   reveal the values of known variables, allowing tactics to use that information to
   make progress without searching the rest of the proof context. *)
Theorem store_upd_eq {s:store} {v u}:
  forall (SV: s v = u), s = update vareq s v u.
Proof.
  intro.
  extensionality v0.
  destruct (vareq v0 v).
    subst v0. rewrite update_updated. exact SV.
    rewrite update_frame. reflexivity. assumption.
Qed.

(* setmem doesn't modify addresses below a, or address at or above a+w. *)
Theorem setmem_frame_low:
  forall e len m a v a' (LT: a' < a),
  setmem e len m a v a' = m a'.
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.
    rewrite setmem_succ. destruct e;
      rewrite IHlen by apply N.lt_lt_succ_r, LT; apply update_frame, N.lt_neq, LT.
Qed.

Theorem setmem_frame_high:
  forall e len m a v a' (LE: a + len <= a'),
  setmem e len m a v a' = m a'.
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.

    assert (LT: a < a'). eapply N.lt_le_trans; [|exact LE]. apply N.lt_add_pos_r, N.lt_0_succ.
    rewrite setmem_succ. destruct e; (rewrite IHlen;
    [ apply update_frame, not_eq_sym, N.lt_neq, LT
    | rewrite N.add_succ_l; apply N.le_succ_l; (eapply N.lt_le_trans; [|exact LE]); apply N.add_lt_mono_l, N.lt_succ_diag_r ]).
Qed.

(* getmem inverts setmem *)
Lemma recompose_bytes:
  forall w v, N.lor (v mod 2^w) (N.shiftl (N.shiftr v w) w) = v.
Proof.
  intros.
  rewrite <- N.ldiff_ones_r, <- N.land_ones, N.lor_comm.
  apply N.lor_ldiff_and.
Qed.

Theorem getmem_setmem:
  forall e len m a v,
  getmem e len (setmem e len m a v) a = match len with N0 => N0 | Npos _ => v end.
Proof.
  induction len using N.peano_ind; intros.
    apply getmem_0.
    rewrite <- N.succ_pos_spec at 3. rewrite getmem_succ, setmem_succ. destruct e; rewrite IHlen; destruct len.
      rewrite N.lor_0_l, N.mul_0_r, setmem_0, N.shiftl_0_r, N.shiftr_0_r. apply update_updated.
      rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
      rewrite setmem_0, N.shiftl_0_l, N.lor_0_r. apply update_updated.
      rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
Qed.

End StoreTheory.


Section TwosComplement.

(* Reinterpreting an unsigned nat as a signed integer in two's complement form
   always yields an integer in range [-2^w, 2^w), where w is one less than the
   bitwidth of the original unsigned number. *)

Definition signed_range (w:N) (z:Z) :=
  (match w with N0 => z = Z0 | _ =>
    - Z.of_N (2^N.pred w)%N <= z < Z.of_N (2^N.pred w)%N
   end)%Z.

Remark N2Z_pow2_pos:
  forall w, (0 < Z.of_N (2^w))%Z.
Proof. intros. rewrite N2Z.inj_pow. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg. Qed.

Remark N2Z_pow2_nonzero:
  forall w, Z.of_N (2^w) <> Z0.
Proof. intros. apply Z.neq_sym, Z.lt_neq, N2Z_pow2_pos. Qed.

Lemma hibits_zero_bound:
  forall n w,
    (forall b, w<=b -> N.testbit n b = false) ->
  n < 2^w.
Proof.
  intros.
  destruct n. destruct (2^w) eqn:H1. apply N.pow_nonzero in H1. contradict H1. discriminate 1. reflexivity.
  apply N.compare_nge_iff. intro P.
    apply N.log2_le_pow2 in P; [|reflexivity].
    apply H in P. rewrite N.bit_log2 in P. discriminate P. discriminate 1.
Qed.

Lemma bound_hibits_zero:
  forall w n b, n < 2^w -> w<=b -> N.testbit n b = false.
Proof.
  intros. destruct n. reflexivity. apply N.bits_above_log2, N.log2_lt_pow2. reflexivity.
  eapply N.lt_le_trans. eassumption.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Theorem signbit:
  forall n w (LT: n < 2^w), N.testbit n (N.pred w) = (2^(N.pred w) <=? n).
Proof.
  intros. destruct (_ <=? _) eqn:H.

    destruct (N.testbit _ _) eqn:SB. reflexivity.
    exfalso. apply N.leb_le in H. apply H, N.lt_gt, hibits_zero_bound.
    intros b LE. apply N.lt_eq_cases in LE. destruct LE.
      eapply bound_hibits_zero. exact LT. apply N.lt_pred_le. assumption.
      subst b. assumption.

    eapply bound_hibits_zero. apply N.leb_gt, H. reflexivity.
Qed.

Theorem toZ_bounds:
  forall n w, n < 2^w -> signed_range w (toZ w n).
Proof.
  intros. unfold toZ, signed_range.
  destruct w as [|w]. apply N.lt_1_r in H. subst n. rewrite N.bits_0. reflexivity.
  rewrite signbit by assumption. destruct (_ <=? _) eqn:SB; split.

    apply Z.le_add_le_sub_l. rewrite Z.add_opp_r.
    rewrite <- N2Z.inj_sub by (apply N.pow_le_mono_r; [ discriminate 1 | apply N.le_pred_l]).
    apply N2Z.inj_le.
    rewrite <- (N.mul_1_l (2^(N.pred _))).
    rewrite <- (N.succ_pred (N.pos w)) at 1 by discriminate 1.
    rewrite N.pow_succ_r', <- N.mul_sub_distr_r, N.mul_1_l.
    apply N.leb_le, SB.

    eapply Z.lt_le_trans.
      apply Z.lt_sub_0. apply N2Z.inj_lt. assumption.
      apply N2Z.is_nonneg.

    transitivity Z0; [apply Z.opp_nonpos_nonneg|]; apply N2Z.is_nonneg.

    apply N2Z.inj_lt, N.leb_gt, SB.
Qed.

Theorem ofZ_bound:
  forall z w, ofZ w z < 2^w.
Proof.
  intros. rewrite <- (N2Z.id (2^w)). unfold ofZ. apply Z2N.inj_lt;
  solve [ apply Z.mod_pos_bound, N2Z_pow2_pos | apply N2Z.is_nonneg ].
Qed.

(* ofZ inverts toZ *)
Theorem ofZ_toZ:
  forall n w (LT: n < 2^w), ofZ w (toZ w n) = n.
Proof.
  intros. unfold toZ, ofZ. destruct (N.testbit _ _).

    rewrite <- Zminus_mod_idemp_r.
    rewrite Z.mod_same by apply N2Z_pow2_nonzero.
    rewrite Z.sub_0_r, <- N2Z.inj_mod, N2Z.id by (apply N.pow_nonzero; discriminate 1).
    apply N.mod_small. assumption.

    rewrite Z.mod_small. apply N2Z.id. split.
      apply N2Z.is_nonneg.
      apply N2Z.inj_lt. assumption.
Qed.

Corollary toZ_inj:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
    toZ w n1 = toZ w n2 -> n1 = n2.
Proof.
  intros.
  rewrite <- (ofZ_toZ n1 w), <- (ofZ_toZ n2 w), H by assumption.
  reflexivity.
Qed.

Theorem ofZ_inj:
  forall z1 z2 w (SR1: signed_range w z1) (SR2: signed_range w z2),
    ofZ w z1 = ofZ w z2 -> z1 = z2.
Proof.
  match goal with |- forall z1 z2, ?P => cut (forall z1 z2 (LE: z2 <= z1), P)%Z end.
    intros. destruct (Z.le_gt_cases z2 z1); [|symmetry]; eapply H; try eassumption.
    apply Z.lt_le_incl. assumption. symmetry. assumption.

  unfold ofZ. intros.
  apply Zminus_eq. rewrite <- (Z.mod_small (_-_) (Z.of_N (2^w))). rewrite Zminus_mod.
  apply Z2N.inj in H; try (apply Z.mod_pos_bound; change Z0 with (Z.of_N 0);
    apply N2Z.inj_lt, N.neq_0_lt_0, N.pow_nonzero; discriminate 1).
  apply Zeq_minus in H. rewrite H. reflexivity.

  split. apply Zle_minus_le_0, LE.
  destruct w as [|w]. rewrite SR1,SR2. reflexivity.
  rewrite <- (N.succ_pred (Npos w)) by discriminate 1. rewrite N.pow_succ_r', N2Z.inj_mul.
  change (Z.of_N 2) with (1+1)%Z. rewrite Z.mul_add_distr_r, Z.mul_1_l, <- Z.sub_opp_r.
  apply Z.sub_lt_le_mono. apply SR1. apply SR2.
Qed.

Theorem toZ_ofZ:
  forall z w (SR: signed_range w z), toZ w (ofZ w z) = z.
Proof.
  intros. eapply ofZ_inj; try eassumption.
    apply toZ_bounds, ofZ_bound.
    apply ofZ_toZ, ofZ_bound.
Qed.

Lemma ofZ_eqm:
  forall z1 z2 w, eqm (Z.of_N (2^w)) z1 z2 <-> ofZ w z1 = ofZ w z2.
Proof.
  unfold ofZ. split; intro.
    rewrite H. reflexivity.
    apply Z2N.inj; solve [ apply H | apply Z.mod_pos_bound, N2Z_pow2_pos ].
Qed.

Lemma toZ_Neqm:
  forall n1 n2 w, toZ w n1 = toZ w n2 -> n1 mod 2^w = n2 mod 2^w.
Proof.
  unfold toZ. intros.
  apply N2Z.inj. rewrite !N2Z.inj_mod by (apply N.pow_nonzero; discriminate 1).
  apply (f_equal (fun z => Z.modulo z (Z.of_N (2^w)))) in H. repeat destruct (N.testbit _ _);
    repeat rewrite Zminus_mod, Z.mod_same, Z.sub_0_r, Z.mod_mod in H by apply N2Z_pow2_nonzero;
    rewrite H; reflexivity.
Qed.

Lemma eqm_toZ:
  forall w n z, eqm (Z.of_N (2^w)) (Z.of_N n) z -> eqm (Z.of_N (2^w)) (toZ w n) z.
Proof.
  intros. unfold eqm,toZ. destruct (N.testbit _ _);
  [ rewrite <- Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r by (
      rewrite N2Z.inj_pow; apply Z.pow_nonzero; [ discriminate 1 | apply N2Z.is_nonneg]) |];
  apply H.
Qed.

Lemma toZ_eqm:
  forall w n, eqm (Z.of_N (2^w)) (toZ w n) (Z.of_N n).
Proof.
  intros. unfold toZ. destruct (N.testbit _ _).
    unfold eqm. rewrite <- Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r by apply N2Z_pow2_nonzero. reflexivity.
    reflexivity.
Qed.

Theorem ofZ_add:
  forall w z1 z2, (ofZ w z1 + ofZ w z2) mod 2^w = ofZ w (z1 + z2).
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_add by apply Z.mod_pos_bound, N2Z_pow2_pos.
  rewrite <- (N2Z.id (2^w)) at 3.
  rewrite <- Z2N.inj_mod by solve [ apply N2Z_pow2_pos | apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound, N2Z_pow2_pos ].
  rewrite <- Z.add_mod by apply N2Z_pow2_nonzero.
  reflexivity.
Qed.

Theorem signed_sub:
  forall w n1 n2, n2 < 2^w -> (2^w + n1 - n2) mod 2^w = sbop Z.sub w n1 n2.
Proof.
  intros. unfold sbop.
  rewrite <- (ofZ_toZ (_ mod _) w) by (apply N.mod_upper_bound, N.pow_nonzero; discriminate 1).
  apply ofZ_eqm, eqm_toZ.
  rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate 1).
  unfold eqm. rewrite Z.mod_mod by apply N2Z_pow2_nonzero.
  rewrite N2Z.inj_sub, N2Z.inj_add by (eapply N.lt_le_incl, N.lt_le_trans; [ exact H | apply N.le_add_r ]).
  rewrite <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l by apply N2Z_pow2_nonzero.
  apply Zminus_eqm; apply eqm_sym, toZ_eqm.
Qed.

Theorem signed_neg:
  forall w n, n < 2^w -> (2^w - n) mod 2^w = ofZ w (- toZ w n).
Proof.
  intros. rewrite <- (N.add_0_r (2^w)) at 1. rewrite <- Z.sub_0_l. apply signed_sub. assumption.
Qed.

Theorem ofZ_mul:
  forall w z1 z2, (ofZ w z1 * ofZ w z2) mod 2^w = ofZ w (z1 * z2).
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_mul by apply Z.mod_pos_bound, N2Z_pow2_pos.
  rewrite <- (N2Z.id (2^w)) at 3.
  rewrite <- Z2N.inj_mod by solve [ apply N2Z_pow2_pos | apply Z.mul_nonneg_nonneg; apply Z.mod_pos_bound, N2Z_pow2_pos ].
  rewrite <- Z.mul_mod by apply N2Z_pow2_nonzero.
  reflexivity.
Qed.

Theorem ofZ_mod_pow2:
  forall w z n, (ofZ w z) mod 2^n = ofZ w (z mod Z.of_N (2^n)).
Proof.
  intros. rewrite <- (N2Z.id (2^n)) at 1. unfold ofZ. rewrite <- Z2N.inj_mod.
    rewrite !N2Z.inj_pow, <- !Z.land_ones, <- !Z.land_assoc, (Z.land_comm (Z.ones _)) by apply N2Z.is_nonneg. reflexivity.
    apply Z.mod_pos_bound, N2Z_pow2_pos.
    apply N2Z_pow2_pos.
Qed.

Theorem ofZ_shiftl:
  forall w z n,
  (N.shiftl (ofZ w z) n) mod 2^w = ofZ w (Z.shiftl z (Z.of_N n)).
Proof.
  intros. unfold ofZ.
  rewrite N.shiftl_mul_pow2, Z.shiftl_mul_pow2 by apply N2Z.is_nonneg.
  rewrite <- (N2Z.id (2^n)), <- Z2N.inj_mul.
    rewrite <- (N2Z.id (2^w)) at 2. rewrite <- Z2N.inj_mod.
      rewrite Z.mul_mod_idemp_l, N2Z.inj_pow by apply N2Z_pow2_nonzero. reflexivity.
      apply Z.mul_nonneg_nonneg.
        apply Z.mod_pos_bound, N2Z_pow2_pos.
        apply Z.lt_le_incl, N2Z_pow2_pos.
      apply N2Z_pow2_pos.
    apply Z.mod_pos_bound, N2Z_pow2_pos.
    apply Z.lt_le_incl, N2Z_pow2_pos.
Qed.

Lemma testbit_ofZ:
  forall w z n, N.testbit (ofZ w z) n = andb (n <? w) (Z.testbit z (Z.of_N n)).
Proof.
  intros. destruct (N.lt_ge_cases n w).
    replace (n <? w) with true.
      unfold ofZ. rewrite <- Z.testbit_of_N. rewrite Z2N.id.
        rewrite N2Z.inj_pow. apply Z.mod_pow2_bits_low, N2Z.inj_lt, H.
        apply Z.mod_pos_bound, N2Z_pow2_pos.
      symmetry. apply N.ltb_lt. assumption.
    replace (n <? w) with false.
      eapply bound_hibits_zero. apply ofZ_bound. assumption.
      symmetry. apply N.ltb_ge. assumption.
Qed.

Theorem ofZ_land:
  forall w z1 z2, N.land (ofZ w z1) (ofZ w z2) = ofZ w (Z.land z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.land_spec, !testbit_ofZ, Z.land_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lor:
  forall w z1 z2, N.lor (ofZ w z1) (ofZ w z2) = ofZ w (Z.lor z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lor_spec, !testbit_ofZ, Z.lor_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lxor:
  forall w z1 z2, N.lxor (ofZ w z1) (ofZ w z2) = ofZ w (Z.lxor z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lxor_spec, !testbit_ofZ, Z.lxor_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lnot:
  forall w z, N.lnot (ofZ w z) w = ofZ w (Z.lnot z).
Proof.
  intros. apply N.bits_inj. intro b. destruct (N.lt_ge_cases b w).

    rewrite N.lnot_spec_low by assumption.
    rewrite !testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
    apply N.ltb_lt in H. rewrite H. reflexivity.

    rewrite N.lnot_spec_high by assumption.
    rewrite !testbit_ofZ. apply N.ltb_ge in H. rewrite H. reflexivity.
Qed.

End TwosComplement.


Section Determinism.

(* The semantics of eval_exp, exec_stmt, and exec_prog are deterministic
   as long as there are no Unknown expressions. *)

Definition not_unknown e := match e with Unknown _ => False | _ => True end.

Theorem eval_exp_deterministic:
  forall {e s v1 v2} (NU: forall_exps_in_exp not_unknown e)
         (E1: eval_exp s e v1) (E2: eval_exp s e v2), v1=v2.
Proof.
  induction e; intros; inversion E1; inversion E2; clear E1 E2; subst;
  unfold forall_exps_in_exp in NU; simpl in NU;
    repeat match type of NU with _ /\ _ => let H := fresh NU in destruct NU as [H NU] end;
  try (remember (match n0 with N0 => e3 | _ => e2 end) as e);
  repeat match goal with [ IH: forall _ _ _, _ -> eval_exp _ ?E _ -> eval_exp _ ?E _ -> _=_,
                           H0: exps_in_exp and not_unknown ?E,
                           H1: eval_exp ?S ?E ?V1,
                           H2: eval_exp ?S ?E ?V2 |- _ ] =>
           specialize (IH S V1 V2 H0 H1 H2); clear H0 H1 H2;
           try (injection IH; clear IH; intros); subst;
           try match type of E' with
             eval_exp _ (match ?N with N0 => _ | _ => _ end) _ => destruct N
           end
         end;
  try reflexivity.

  rewrite SV in SV0. injection SV0. intro. assumption.
  exfalso. assumption.
Qed.

Theorem exec_stmt_deterministic:
  forall {s q n s1 x1 s2 x2} (NU: forall_exps_in_stmt not_unknown q)
         (X1: exec_stmt s q n s1 x1) (X2: exec_stmt s q n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 X2.
  dependent induction X1; intros; inversion X2; subst;
  try solve [ split;reflexivity ];
  try destruct NU as [NU1 NU2].

  replace u0 with u.
    split; reflexivity.
    apply (eval_exp_deterministic NU E E0).

  assert (H:=eval_exp_deterministic NU E E0).
  injection H. intros. subst. split; reflexivity.

  apply IHX1; assumption.

  apply (IHX1 NU1) in XS1. destruct XS1. discriminate.

  apply (IHX1_1 NU1) in XS. destruct XS. discriminate.

  apply (IHX1_1 NU1),proj1 in XS1. subst. apply (IHX1_2 NU2) in XS0. assumption.

  apply IHX1; repeat first [ assumption | split ].

  apply IHX1.
    destruct NU2. destruct c; assumption.
    assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst. assumption.
Qed.

Theorem exec_prog_deterministic:
  forall {p a s m n s1 x1 s2 x2}
  (NU: forall a', match p a' with None => True | Some (_,q) => forall_exps_in_stmt not_unknown q end)
  (XP1: exec_prog p a s m n s1 x1) (XP2: exec_prog p a s m n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 XP2. dependent induction XP1; intros; inversion XP2; subst;
  assert (NUa:=NU a);
  try (rewrite LU0 in LU; first [ discriminate LU
                                | injection LU; clear LU; intros; subst; rewrite LU0 in NUa ]);
  try solve [ split;reflexivity ];
  assert (ESD:=exec_stmt_deterministic NUa XS XS0);
  destruct ESD as [ESD1 ESD2]; try (injection ESD2; clear ESD2; intro); subst.

  replace a'0 with a' in XP.
    apply IHXP1. assumption.
    destruct x0 as [x0|]; [destruct x0|]; first
    [ discriminate
    | injection EX; injection EX0; intros; subst; subst; reflexivity ].

  destruct x2; discriminate.

  destruct x; discriminate.

  split; reflexivity.
Qed.

End Determinism.


Section Monotonicity.

(* Some monotonicity properties: *)

(* exec_stmt and exec_prog are monotonic with respect to their input and output
   stores (i.e., there is no "delete variable" operation). *)

Theorem exec_stmt_nodelete:
  forall {s q n s' x} (XS: exec_stmt s q n s' x) v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XS; try apply IHXS; try assumption.
  unfold update in V'. destruct (vareq v0 v). discriminate. assumption.
  apply IHXS1, IHXS2. assumption.
Qed.

Theorem exec_prog_nodelete:
  forall {p a s m n s' x} (XP: exec_prog p a s m n s' x)
         v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XP; try assumption;
  apply (exec_stmt_nodelete XS); try apply IHXP; assumption.
Qed.

Theorem eval_exp_mono:
  forall {e v s1} s2 (E: eval_exp s1 e v) (SS: s1 ⊆ s2),
  eval_exp s2 e v.
Proof.
  induction e; intros; inversion E; clear E; subst;
  repeat match goal with [ IH: forall _ _ _, eval_exp _ ?E _ -> _ -> eval_exp _ ?E _,
                           H: eval_exp _ ?E _ |- _ ] =>
    eapply IH in H; [|exact SS]
  end;
  econstructor; try eassumption.

  apply SS. assumption.

  intros. eapply mem_readable_mono. exact SS. apply R. assumption.

  intros. eapply mem_writable_mono. exact SS. apply W. assumption.

  eapply IHe2; [eassumption|].
  intros x y. unfold update. intro. destruct (vareq x v). assumption.
  apply SS. assumption.

  destruct n1.
    eapply IHe3; eassumption.
    eapply IHe2; eassumption.
Qed.

Theorem exec_stmt_mono:
  forall {s1 q m s1' x} s2 (XS: exec_stmt s1 q m s1' x) (PO: s1 ⊆ s2),
  exec_stmt s2 q m (updateall s2 s1') x.
Proof.
  intros. revert s2 PO. dependent induction XS; intros;
  try (rewrite updateall_subset; [ try constructor | assumption ]).

  replace (updateall s2 (s[v:=Some u])) with (s2[v:=Some u]).
    apply XMove. apply (eval_exp_mono _ E PO).
    extensionality x. unfold update, updateall. destruct (vareq x v).
      reflexivity.
      unfold pfsub in PO. specialize PO with (x:=x). destruct (s x).
        apply PO. reflexivity.
        reflexivity.

  apply XJmp with (w:=w). apply (eval_exp_mono _ E PO).

  apply XSeq1. apply IHXS. assumption.

  apply XSeq2 with (s2:=updateall s0 s2).
    apply IHXS1. assumption.
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXS2. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_stmt_nodelete XS2 z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XWhile. apply IHXS. assumption.

  apply XIf with (c:=c). apply (eval_exp_mono _ E PO). apply IHXS. assumption.
Qed.

Theorem exec_prog_mono:
  forall {p a s1 m n s1' x} s2 (XP: exec_prog p a s1 m n s1' x) (PO: s1 ⊆ s2),
  exec_prog p a s2 m n (updateall s2 s1') x.
Proof.
  intros. revert s2 PO. dependent induction XP; intros.

  replace (updateall s2 s) with s2.
    constructor.
    symmetry. apply updateall_subset. assumption.

  apply XPStep with (sz:=sz) (q:=q) (s2:=updateall s0 s2) (x1:=x1) (a':=a'); try assumption.
    apply (exec_stmt_mono _ XS PO).
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXP. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_prog_nodelete XP z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XPDone with (sz:=sz) (q:=q); try assumption.
    apply (exec_stmt_mono _ XS PO).
Qed.

End Monotonicity.


Section Boundedness.

(* If there are no while-loops, we can compute a necessary and sufficient recursion bound to
   avoid an Unfinished condition for execution of any statement. *)

Fixpoint step_bound (q:stmt) : option nat :=
  match q with
  | Nop | Move _ _ | Jmp _ | CpuExn _ => Some 1%nat
  | Seq q1 q2 | If _ q1 q2 => match step_bound q1, step_bound q2 with
                              | Some n1, Some n2 => Some (S (max n1 n2))
                              | _, _ => None
                              end
  | While _ _ => None
  end.

Theorem step_bound_pos:
  forall q n (SB: step_bound q = Some n), (0<n)%nat.
Proof.
  induction q; intros.
  all: simpl in SB; try (injection SB; clear SB; intro; subst n).
  1-4: exact Nat.lt_0_1.
  2: discriminate.
  all: destruct (step_bound q1); destruct (step_bound q2); try discriminate.
  all: injection SB; clear SB; intro; subst n.
  all: apply Nat.lt_0_succ.
Qed.

Theorem stmt_finish:
  forall s q n n' s' x
         (SB: step_bound q = Some n) (LT: (n <= n')%nat)
         (XS: exec_stmt s q n' s' x),
  x <> Some Unfinished.
Proof.
  intros.
  revert n SB LT. dependent induction XS; intros; try discriminate.

  exfalso. apply le_not_lt in LT. apply LT. revert SB. apply step_bound_pos.

  3: destruct c.
  all: simpl in SB; destruct (step_bound q1); destruct (step_bound q2); try discriminate.
  all: injection SB; clear SB; intro; subst n0.
  2: rename IHXS2 into IHXS.
  all: eapply IHXS; [reflexivity|].
  all: transitivity (max n1 n2); [ first [ apply Max.le_max_l | apply Max.le_max_r ]
                                 | apply le_S_n; assumption ].
Qed.

(* A stmt that finishes within n steps will also finish within (S n) steps. *)
Theorem exec_stmt_incbound:
  forall m s q s' x (FIN: x <> Some Unfinished) (XS: exec_stmt s q m s' x),
  exec_stmt s q (S m) s' x.
Proof.
  induction m; intros; inversion XS; clear XS; subst.
    contradict FIN. reflexivity.
    apply XNop.
    apply XMove. exact E.
    eapply XJmp. exact E.
    apply XExn.
    apply XSeq1. apply IHm. exact FIN. exact XS0.
    eapply XSeq2.
      apply IHm. discriminate 1. exact XS1.
      apply IHm. exact FIN. exact XS0.
    apply XWhile. apply IHm. exact FIN. exact XS0.
    eapply XIf. exact E. apply IHm. exact FIN. exact XS0.
Qed.

Corollary exec_stmt_raisebound:
  forall m' m s q s' x (LE: (m <= m')%nat) (FIN: x <> Some Unfinished) (XS: exec_stmt s q m s' x),
  exec_stmt s q m' s' x.
Proof.
  intros. pattern m'. revert m' LE. apply le_ind.
    exact XS.
    intros. apply exec_stmt_incbound. exact FIN. assumption.
Qed.

End Boundedness.


Section InvariantProofs.

(* To prove properties of while-loops, it suffices to prove that each loop iteration
   preserves the property.  This is equivalent to stepping the loop three small-steps
   at a time (to unfold the While->If->Seq expansion of the loop). *)
Theorem while_inv:
  forall (P: store -> Prop)
         s e q m s' x (XS: exec_stmt s (While e q) m s' x) (PRE: P s)
         (INV: forall s c m s' x (PRE: P s)
                      (EX: eval_exp s e (VaN (Npos c) 1))
                      (XS: exec_stmt s q m s' x), P s'),
  P s'.
Proof.
  intros. revert s s' x XS PRE.
  rewrite (Nat.div_mod m 3); [|discriminate].
  induction (Nat.div m 3) as [|m'].

  simpl. destruct (snd _); intros.
    inversion XS; inversion XS0; inversion XS1; subst. exact PRE.
    destruct y.
      inversion XS; inversion XS0; subst. exact PRE.
      inversion XS; subst. exact PRE.

  rewrite Nat.mul_succ_r. rewrite (plus_comm _ 3). rewrite <- plus_assoc. intros.
  inversion XS; inversion XS0; subst. destruct c; inversion XS1; subst.
    exact PRE.
    eapply INV. exact PRE. exact E. exact XS2.
    eapply IHm'.
      exact XS3.
      eapply INV. exact PRE. exact E. exact XS2.
Qed.

(* Append a step to an exec_prog computation. *)
Theorem exec_prog_append:
  forall p n a s m sz q s2 a1 s' x'
         (XP: exec_prog p a s m n s2 (Exit a1))
         (LU: p a1 = Some (sz,q))
         (XS: exec_stmt s2 q m s' x'),
    exec_prog p a s m (S n) s' (match x' with None => Exit (a1+sz)
                                            | Some x' => x' end).
Proof.
  induction n; intros; inversion XP; subst.
    destruct x'; [destruct e|]; econstructor; solve [ eassumption | reflexivity | apply XPZero ].
    eapply XPStep; try eassumption. eapply IHn; eassumption.
    discriminate.
Qed.

(* Split an exec_prog computation into two parts. *)
Theorem exec_prog_split:
  forall p a s m n1 n2 s' x'
         (XP: exec_prog p a s m (n1 + S n2)%nat s' x'),
  exists s1 a1, exec_prog p a s m n1 s1 (Exit a1) /\ exec_prog p a1 s1 m (S n2) s' x'.
Proof.
  intros. revert n2 XP. induction n1; intros.
    exists s,a. split. apply XPZero. exact XP.
    rewrite Nat.add_succ_comm in XP. destruct (IHn1 _ XP) as [s1 [a1 [XP1 XP2]]]. inversion XP2; subst. exists s2,a'. split.
      eapply exec_prog_append in XP1; [|exact LU | exact XS]. destruct x1 as [e|]; [destruct e|].
        discriminate EX.
        injection EX as; subst. exact XP1.
        discriminate EX.
        injection EX as; subst. exact XP1.
      assumption.
Qed.

(* Concatenate two exec_prog comptations into one whole. *)
Theorem exec_prog_concat:
  forall p a s m n1 n2 s1 a1 s' x'
         (XP1: exec_prog p a s m n1 s1 (Exit a1)) (XP2: exec_prog p a1 s1 m (S n2) s' x'),
  exec_prog p a s m (n1 + S n2)%nat s' x'.
Proof.
  intros. revert n2 s1 a1 XP1 XP2. induction n1; intros.
    inversion XP1; subst. exact XP2.
    rewrite <- Nat.add_1_r in XP1. apply exec_prog_split in XP1. destruct XP1 as [s2 [a2 [XP0 XP1]]]. rewrite Nat.add_succ_comm. eapply IHn1.
     exact XP0.
     inversion XP1; subst.
       eapply XPStep. exact LU. exact XS. exact EX. inversion XP; subst. exact XP2.
       discriminate EX.
Qed.

(* To prove that a property holds at the conclusion of a program's execution, it suffices
   to prove that the property is preserved by every statement in the program. *)
Theorem prog_inv_universal:
  forall (P: exit -> store -> Prop)
         (p:program) a0 s0 m n s' x' (XP: exec_prog p a0 s0 m n s' x') (PRE: P (Exit a0) s0)
         (INV: forall a1 s1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1)
                      (XS: exec_stmt s1 q m s1' x1),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1'),
  P x' s'.
Proof.
  intros. revert a0 s0 XP PRE. induction n; intros; inversion XP; subst.
    exact PRE.
    apply (IHn a' s2).
      exact XP0.
      specialize (INV a0 s0 sz q s2 x1 LU PRE XS). destruct x1; [destruct e|]; first
      [ discriminate EX
      | injection EX; intro; subst a'; exact INV ].
    specialize (INV a0 s0 sz q s' (Some x') LU PRE XS). exact INV.
Qed.

(* Alternatively, one may prove that the property is preserved by all the reachable statements.
   (The user's invariant may adopt a precondition of False for unreachable statements.) *)
Theorem prog_inv_reachable:
  forall (P: exit -> store -> nat -> Prop)
         (p:program) a0 s0 m n s' x' (XP: exec_prog p a0 s0 m n s' x') (PRE: P (Exit a0) s0 O)
         (INV: forall a1 s1 n1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1 n1) (LT: (n1 < n)%nat)
                      (XP: exec_prog p a0 s0 m n1 s1 (Exit a1))
                      (XS: exec_stmt s1 q m s1' x1)
                      (XP': match x1 with None => exec_prog p (a1+sz) s1' m (n - S n1) s' x'
                                        | Some (Exit a2) => exec_prog p a2 s1' m (n - S n1) s' x'
                                        | Some x2 => x'=x2 end),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1' (S n1)),
  P x' s' n.
Proof.
  intros.
  assert (H: exists a1 s1 n2, (n2 <= n)%nat /\ exec_prog p a0 s0 m (n - n2) s1 (Exit a1) /\ P (Exit a1) s1 (n - n2)%nat /\ exec_prog p a1 s1 m n2 s' x').
    exists a0,s0,n. rewrite Nat.sub_diag. repeat split.
      apply le_n.
      apply XPZero.
      exact PRE.
      exact XP.
  destruct H as [a1 [s1 [n2 [LE [XP1 [PRE1 XP2]]]]]].
  clear XP. revert a1 s1 LE PRE1 XP1 XP2. induction n2; intros.
    inversion XP2; clear XP2; subst. rewrite Nat.sub_0_r in PRE1. exact PRE1.
    inversion XP2; clear XP2; subst.
      apply (IHn2 a' s2).
        transitivity (S n2). apply le_S, le_n. assumption.

        specialize (INV a1 s1 (n - S n2)%nat sz q s2 x1 LU PRE1 (Nat.sub_lt n (S n2) LE (Nat.lt_0_succ n2)) XP1 XS).
        rewrite minus_Sn_m, Nat.sub_succ in INV by exact LE.
        replace (n - (n - n2))%nat with n2 in INV by (apply plus_minus; symmetry; apply Nat.sub_add, le_Sn_le, LE).
        destruct x1; [destruct e|].
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.

        destruct n. inversion LE. apply le_S_n in LE. rewrite Nat.sub_succ_l; [|exact LE].
        replace (Exit a') with (match x1 with None => Exit (a1 + sz)
                                            | Some x => x end).
          eapply exec_prog_append. exact XP1. exact LU. exact XS.
          destruct x1; [destruct e|]; first [ discriminate EX | injection EX; intro; subst; reflexivity ].

        exact XP.
      specialize (INV a1 s1 (n-1)%nat sz q s' (Some x') LU PRE1 (Nat.sub_lt n 1 LE Nat.lt_0_1) XP1 XS).
      rewrite minus_Sn_m, Nat.sub_succ, Nat.sub_0_r in INV by exact LE.
      apply INV. destruct x'.
        reflexivity.
        discriminate EX.
        reflexivity.
Qed.

(* Rather than assigning and proving an invariant at every machine instruction, we can generalize
   the above to allow users to assign invariants to only a few machine instructions.  To prove that
   all the invariants are satisfied, the user can prove that any execution that starts in an
   invariant-satisfying state and that reaches another invariant always satisfies the latter. *)

(* The "next invariant satisfied" property is true if we're at an invariant point and the state
   satisfies that invariant, or we're not at an invariant point and (inductively) taking one
   exec_prog step leads to a "next invariant satisfied" state. *)
Inductive next_inv_sat (PS: exit -> store -> nat -> option Prop):
            bool -> exit -> program -> store -> nat -> nat -> nat -> store -> exit -> Prop :=
| NISHere x p s m n n' s' x' (TRU: match PS x s n with None => False | Some P => P end):
    next_inv_sat PS true x p s m n n' s' x'
| NISStep p s m n n' s' x' a
          (STEP: forall sz q s1 x1 (LT: (n < n')%nat)
                        (IL: p a = Some (sz,q)) (XS: exec_stmt s q m s1 x1)
                        (XP': match x1 with None => exec_prog p (a+sz) s1 m (n' - S n) s' x'
                              | Some (Exit a2) => exec_prog p a2 s1 m (n' - S n) s' x'
                              | Some x2 => x'=x2 end),
                 next_inv_sat PS (match PS match x1 with None => Exit (a+sz) | Some x1 => x1 end s1 (S n) with
                                  | Some _ => true | None => false end)
                              match x1 with None => Exit (a+sz) | Some x1 => x1 end
                              p s1 m (S n) n' s' x'):
    next_inv_sat PS false (Exit a) p s m n n' s' x'.

(* Proving the "next invariant satisfied" property for all invariant points proves partial
   correctness of the program. *)
Theorem prog_inv:
  forall (PS: exit -> store -> nat -> option Prop) (p:program) a0 s0 m n s' x'
         (XP: exec_prog p a0 s0 m n s' x')
         (PRE: match PS (Exit a0) s0 O with Some P => P | None => False end)
         (INV: forall a1 s1 n1
                      (XP: exec_prog p a0 s0 m n1 s1 (Exit a1))
                      (PRE: match PS (Exit a1) s1 n1 with Some P => P | None => False end),
               next_inv_sat PS false (Exit a1) p s1 m n1 n s' x'),
  match PS x' s' n with Some P => P | None => True end.
Proof.
  intros.
  assert (NIS: next_inv_sat PS (match PS x' s' n with Some _ => true | None => false end) x' p s' m n n s' x').
    pattern x' at -3, s' at -3, n at -3. eapply prog_inv_reachable.
      exact XP.
      destruct (PS (Exit a0) s0 O) eqn:PS0.
        apply NISHere. rewrite PS0. exact PRE.
        exfalso. exact PRE.
      intros. specialize (INV a1 s1 n1 XP0). destruct (PS (Exit a1) s1 n1) eqn:PS1.

        inversion PRE0; subst. rewrite PS1 in TRU. specialize (INV TRU).
        inversion INV; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.

        inversion PRE0; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.
  destruct (PS x' s' n) eqn:PS'.
    inversion NIS. rewrite PS' in TRU. exact TRU.
    exact I.
Qed.

End InvariantProofs.


Section FrameTheorems.

(* Statements and programs that contain no assignments to some IL variable v
   leave that variable unchanged in the output store. *)

Fixpoint noassign v q :=
  match q with
  | Nop | Jmp _ | CpuExn _ => True
  | Seq q1 q2 | If _ q1 q2 => noassign v q1 /\ noassign v q2
  | While _ q' => noassign v q'
  | Move v1 q => v<>v1
  end.

Theorem noassign_inv:
  forall v q (H:noassign v q) m (s s':store) x,
  exec_stmt s q m s' x -> s' v = s v.
Proof.
  induction q; intros; inversion H0; subst; try reflexivity.
    destruct (vareq v0 v).
      exfalso. subst. apply H. reflexivity.
      apply update_frame. apply H.
    eapply IHq1. exact (proj1 H). exact XS.
    transitivity (s2 v).
      eapply IHq2. exact (proj2 H). exact XS0.
      eapply IHq1. exact (proj1 H). exact XS1.

    pattern s'. eapply while_inv.
      exact H0.
      reflexivity.
      intros. rewrite <- PRE. eapply IHq. exact H. exact XS0.

    destruct c.
      eapply IHq2. exact (proj2 H). exact XS.
      eapply IHq1. exact (proj1 H). exact XS.
Qed.

Definition prog_noassign v (p:program) :=
  forall a, match p a with None => True | Some (_,q) => noassign v q end.

Theorem prog_noassign_inv:
  forall v p (NP: prog_noassign v p) m s' x
         n a s (EP: exec_prog p a s m n s' x),
  s' v = s v.
Proof.
  intros. pattern x, s'. eapply prog_inv_universal.
    exact EP.
    reflexivity.
    intros. rewrite <- PRE. apply (noassign_inv v) in XS.
      exact XS.
      specialize (NP a1). rewrite IL in NP. exact NP.
Qed.

End FrameTheorems.


Section FInterp.

(* Functional Interpretation of Programs:
   In this section we define an interpreter that is purely functional instead of inductive.  Since programs
   can be non-deterministic (if there are Unknown expressions), this interpreter only computes one possible
   value of each variable.  We then prove that this result is correct according to the operational semantics.
   When there are no unknowns, determinism of the semantics (proved above) proves that the result is precise.
   This facilitates a series of tactics that can interpret common-case expressions and statements in proofs
   to automatically infer the resulting store after execution of each assembly language instruction.

   In order to help Coq expression simplification to infer a value for each symbolic expression, we define
   our interpreter in terms of "untyped values" (uvalues), which always contain both a memory value and a
   numeric value.  This allows the interpreter to progress even when Coq can't automatically infer an
   expression's type. *)

Inductive uvalue := VaU (z:bool) (m:addr->N) (n:N) (w:N).

Definition zstore (_:addr) := 0.

Definition uvalue_of (v:value) :=
  match v with
  | VaN n w => VaU true zstore n w
  | VaM m w => VaU false m 0 w
  end.

Definition of_uvalue (v:uvalue) :=
  match v with VaU z m n w => if z then VaN n w else VaM m w end.

Definition utowidth (w n:N) : uvalue :=
  VaU true zstore (N.modulo n (2^w)) w.

Definition utobit (b:bool) : uvalue :=
  VaU true zstore (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth w (n1+n2)
  | OP_MINUS => utowidth w (2^w + n1 - n2)
  | OP_TIMES => utowidth w (n1*n2)
  | OP_DIVIDE => VaU true zstore (n1/n2) w
  | OP_SDIVIDE => VaU true zstore (sbop Z.quot w n1 n2) w
  | OP_MOD => VaU true zstore (N.modulo n1 n2) w
  | OP_SMOD => VaU true zstore (sbop Z.rem w n1 n2) w
  | OP_LSHIFT => utowidth w (N.shiftl n1 n2)
  | OP_RSHIFT => VaU true zstore (N.shiftr n1 n2) w
  | OP_ARSHIFT => VaU true zstore (ashiftr w n1 n2) w
  | OP_AND => VaU true zstore (N.land n1 n2) w
  | OP_OR => VaU true zstore (N.lor n1 n2) w
  | OP_XOR => VaU true zstore (N.lxor n1 n2) w
  | OP_EQ => utobit (n1 =? n2)
  | OP_NEQ => utobit (negb (n1 =? n2))
  | OP_LT => utobit (n1 <? n2)
  | OP_LE => utobit (n1 <=? n2)
  | OP_SLT => utobit (slt w n1 n2)
  | OP_SLE => utobit (sle w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => utowidth w ((2^w) - n)
  | OP_NOT => VaU true zstore (N.lnot n w) w
  end.

Definition uget (v:option value) : uvalue :=
  match v with None => VaU true zstore 0 0
             | Some u => uvalue_of u
  end.

Lemma fold_uget:
  forall v, match v with None => VaU true zstore 0 0
                       | Some u => uvalue_of u
            end = uget v.
Proof. intros. reflexivity. Qed.

Definition bits_of_mem len := N.mul Mb len.

Fixpoint feval_exp (e:exp) (s:store) : uvalue :=
  match e with
  | Var v => uget (s v)
  | Word n w => VaU true zstore n w
  | Load e1 e2 en len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ _, VaU _ _ n _ => VaU true zstore (getmem en len m n) (bits_of_mem len)
      end
  | Store e1 e2 e3 en len =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ m _ mw, VaU _ _ a _, VaU _ _ v _ => VaU false (setmem en len m a v) 0 mw
      end
  | BinOp bop e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w, VaU _ _ n2 _ => feval_binop bop w n1 n2
      end
  | UnOp uop e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => feval_unop uop n w
      end
  | Cast c w' e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast c w w' n) w'
      end
  | Let v e1 e2 => feval_exp e2 (update vareq s v (Some (of_uvalue (feval_exp e1 s))))
  | Unknown _ => VaU true zstore 0 0
  | Ite e1 e2 e3 =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ _ n1 _, VaU b2 m2 n2 w2, VaU b3 m3 n3 w3 =>
          VaU (if n1 then b3 else b2) (if n1 then m3 else m2) (if n1 then n3 else n2) (if n1 then w3 else w2)
      end
  | Extract n1 n2 e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                             (cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2))
      end
  | Concat e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w1, VaU _ _ n2 w2 => VaU true zstore (N.lor (N.shiftl n1 w2) n2) (w1+w2)
      end
  end.

Definition NoMemAcc := True.
Definition MemAcc (RW: store -> addr -> Prop) (s:store) a len :=
  forall n, n < len -> RW s (a+n).

Fixpoint memacc_exp (e:exp) (s:store) : Prop :=
  match e with
  | Load e1 e2 _ len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc mem_readable s a len
      end
  | Store e1 e2 _ _ len =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc mem_writable s a len
      end
  | Var _ | Word _ _ | Unknown _ => NoMemAcc
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => memacc_exp e1 s
  | BinOp _ e1 e2 | Concat e1 e2 => memacc_exp e1 s /\ memacc_exp e2 s
  | Let v e1 e2 => memacc_exp e1 s /\ memacc_exp e2 (update vareq s v (Some (of_uvalue (feval_exp e1 s))))
  | Ite e1 e2 e3 =>
      match feval_exp e1 s with
      | VaU _ _ n w => if n then memacc_exp e3 s else memacc_exp e2 s
      end
  end.

Fixpoint exp_known (e:exp) :=
  match e with
  | Var _ | Word _ _ => true
  | Unknown _ => false
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => exp_known e1
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ => if exp_known e1 then exp_known e2 else false
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ => if exp_known e1 then (if exp_known e2 then exp_known e3 else false) else false
  end.

Lemma uvalue_inv: forall u, of_uvalue (uvalue_of u) = u.
Proof.
  intros. destruct u; reflexivity.
Qed.

Definition canonical_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then m = zstore else n = 0 end.

Lemma can_uvalue_inv: forall u (C: canonical_uvalue u), uvalue_of (of_uvalue u) = u.
Proof.
  intros. destruct u. destruct z; simpl in C; subst; reflexivity.
Qed.

Lemma canonical_conv:
  forall v, canonical_uvalue (uvalue_of v).
Proof.
  intro. destruct v; reflexivity.
Qed.

Lemma canonical_uget:
  forall v, canonical_uvalue (uget v).
Proof.
  intros. destruct v.
    apply canonical_conv.
    reflexivity.
Qed.

Lemma canonical_feval:
   forall e s, canonical_uvalue (feval_exp e s).
Proof.
  induction e; intros; simpl;
  repeat match goal with |- context [ feval_exp ?e ?s ] => destruct (feval_exp e s) eqn:? end;
  try reflexivity.
  apply canonical_uget.
  destruct b; reflexivity.
  destruct u; reflexivity.
  rewrite <- Hequ. apply IHe2.
  destruct n;
    match goal with [ H: _ = ?u |- _ ?u ] => rewrite <- H; generalize s; assumption end.
Qed.

Theorem reduce_binop:
  forall bop w n1 n2, eval_binop bop w n1 n2 = of_uvalue (feval_binop bop w n1 n2).
Proof.
  intros. destruct bop; reflexivity.
Qed.

Theorem reduce_unop:
  forall uop w n, eval_unop uop w n = of_uvalue (feval_unop uop w n).
Proof.
  intros. destruct uop; reflexivity.
Qed.

Theorem reduce_exp:
  forall e s u (K: exp_known e = true) (E: eval_exp s e u), u = of_uvalue (feval_exp e s).
Proof.
  induction e; intros; inversion E; clear E; subst; simpl;
  simpl in K; repeat (apply andb_prop in K; let K':=fresh "K" in destruct K as [K' K]);
  repeat match goal with [ IH: forall _ _, exp_known ?e = _ -> _, K: exp_known ?e = _, E: eval_exp _ ?e _ |- _ ] =>
    apply (IH _ _ K) in E;
    try (let b := fresh "b" in destruct (feval_exp e _) as [b ? ? ?]; destruct b; try discriminate E; injection E as)
  end; subst; try reflexivity.

    rewrite SV. symmetry. apply uvalue_inv.

    apply reduce_binop.

    apply reduce_unop.

    discriminate K.

    destruct n.
      apply (IHe3 _ _ K) in E'. destruct (feval_exp e2 s). destruct (feval_exp e3 _). subst u. reflexivity.
      apply (IHe2 _ _ K1) in E'. destruct (feval_exp e2 _). destruct (feval_exp e3 _). subst u. reflexivity.
Qed.

Theorem memacc_exp_true:
  forall e s u (K: exp_known e = true) (E: eval_exp s e u),
  memacc_exp e s.
Proof.
  induction e; intros; try exact I;
    try (unfold exp_known in K; fold exp_known in K; apply andb_prop in K; destruct K as [K1 K2]);
    inversion E; subst;
    unfold memacc_exp; fold memacc_exp;
    try first [ eapply IHe; [ exact K | exact E1 ]
              | split; [ eapply IHe1; [ exact K1 | exact E1 ]
                       | eapply IHe2; [ exact K2 | exact E2 ] ] ].

  (* Load *)
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. rewrite <- E1, <- E2. exact R.

  (* Store *)
  apply andb_prop, proj1 in K2.
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. rewrite <- E1, <- E2. exact W.

  (* Let *)
  split.
    eapply IHe1. exact K1. exact E1.
    eapply IHe2. exact K2. apply reduce_exp in E1; [|exact K1]. rewrite <- E1. exact E2.

  (* Ite *)
  apply reduce_exp in E1; [|exact K1]. apply (f_equal uvalue_of) in E1. rewrite can_uvalue_inv in E1 by apply canonical_feval.
  rewrite <- E1. simpl. apply andb_prop in K2. destruct n1.
    eapply IHe3. exact (proj2 K2). exact E'.
    eapply IHe2. exact (proj1 K2). exact E'.
Qed.


(* With the above, we can now reduce common-case exec_stmt hypotheses into hypotheses of the
   form s' = ... /\ x' = ..., which allows us to infer the final store s' and exit state x'
   and substitute them away throughout the proof context. *)

Lemma reduce_seq_move:
  forall x1 (FIN: x1 <> Some Unfinished)
         s1 v e q m s1' (XS: exec_stmt s1 (Seq (Move v e) q) m s1' x1),
  if exp_known e then
    (let u := of_uvalue (feval_exp e s1) in exec_stmt (s1[v:=Some u]) q (pred m) s1' x1) /\
    memacc_exp e s1
  else
    exists u, exec_stmt (s1[v:=Some u]) q (pred m) s1' x1.
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  inversion XS0; subst. contradict FIN. reflexivity.
  inversion XS1; subst.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E. subst u. exact XS0. exact K.
      eapply memacc_exp_true. exact K. exact E.
    eexists. exact XS0.
Qed.

Lemma reduce_nop:
  forall x1 (FIN: x1 <> Some Unfinished)
         s1 m s1' (XS: exec_stmt s1 Nop m s1' x1),
  s1' = s1 /\ x1 = None.
Proof.
  intros. inversion XS; subst.
  contradict FIN. reflexivity.
  split; reflexivity.
Qed.

Lemma reduce_move:
  forall x1 (FIN: x1 <> Some Unfinished)
         s1 v e m s1' (XS: exec_stmt s1 (Move v e) m s1' x1),
  if exp_known e then
    ((let u := of_uvalue (feval_exp e s1) in s1' = s1[v:=Some u]) /\ x1 = None) /\
    memacc_exp e s1
  else exists u, (s1' = s1[v:=Some u] /\ x1 = None).
Proof.
  intros.
  inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E. rewrite E. split; reflexivity. exact K.
      eapply memacc_exp_true. exact K. exact E.
    exists u. split; reflexivity.
Qed.

Lemma reduce_jmp:
  forall x1 (FIN: x1 <> Some Unfinished)
         s1 e m s1' (XS: exec_stmt s1 (Jmp e) m s1' x1),
  if exp_known e then
    (s1' = s1 /\ x1 = Some (Exit (match feval_exp e s1 with VaU _ _ a _ => a end))) /\
    memacc_exp e s1
  else exists a, (s1' = s1 /\ x1 = Some (Exit a)).
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      split. reflexivity.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      simpl in E. rewrite <- E. reflexivity.

      eapply memacc_exp_true. exact K. exact E.

    exists a. split; reflexivity.
Qed.

Lemma reduce_if:
  forall x1 (FIN: x1 <> Some Unfinished)
         s1 e q1 q2 m s1' (XS: exec_stmt s1 (If e q1 q2) m s1' x1),
  if exp_known e then
    (exec_stmt s1 (match feval_exp e s1 with VaU _ _ c _ => if c then q2 else q1 end) (pred m) s1' x1) /\
    memacc_exp e s1
  else
    exists (c:N), exec_stmt s1 (if c then q2 else q1) (pred m) s1' x1.
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      rewrite <- E. simpl. destruct c; assumption.

      eapply memacc_exp_true. exact K. exact E.

    eexists. exact XS0.
Qed.

End FInterp.


(* Using the functional interpreter, we now define a set of tactics that reduce expressions to values,
   and statements to stores & exits.  These tactics are carefully implemented to avoid simplifying
   anything other than the machinery of the functional interpreter, so that Coq does not spin out of
   control attempting to execute the entire program.  Our objective is to infer a reasonably small,
   well-formed symbolic expression that captures the result of executing each assembly instruction.
   This result can be further reduced by the user (e.g., using "simpl") if desired.  Call-by-value
   strategy is used here, since our goal is usually to reduce as much as possible of the target
   expression, which might include arguments of an enclosing unexpandable function. *)

Declare Reduction simpl_exp :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ].

Ltac simpl_exp :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ];
  repeat simpl (bits_of_mem _).

Tactic Notation "simpl_exp" "in" hyp(H) :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ] in H;
  repeat simpl (bits_of_mem _) in H.


(* Statement simplification most often gets stuck at variable-reads, since the full content of the
   store is generally not known (s is a symbolic expression).  We can often push past this obstacle
   by applying the update_updated and update_frame theorems to automatically infer that the values
   of variables not being read are irrelevant.  The "simpl_stores" tactic does so. *)

Remark if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.
Proof. intros. destruct n; reflexivity. Qed.

Ltac simpl_stores :=
  repeat first [ rewrite update_updated | rewrite update_frame; [|discriminate 1] ];
  repeat rewrite if_N_same;
  repeat match goal with |- context [ update vareq ?S ?V ?U ] =>
    match S with context c [ update vareq ?T V _ ] => let r := context c[T] in
      replace (update vareq S V U) with (update vareq r V U) by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Tactic Notation "simpl_stores" "in" hyp(H) :=
  repeat first [ rewrite update_updated in H | rewrite update_frame in H; [|discriminate 1] ];
  repeat rewrite if_N_same in H;
  repeat match type of H with context [ update vareq ?S ?V ?U ] =>
    match S with context c [ update vareq ?T V _ ] => let r := context c[T] in
      replace (update vareq S V U) with (update vareq r V U) in H by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.


(* To facilitate expression simplification, it is often convenient to first consolidate all information
   about known variable values into the expression to be simplified.  The "stock_store" tactic searches the
   proof context for hypotheses of the form "s var = value", where "var" is some variable appearing in the
   expression to be reduced and "s" is the store, and adds "s[var:=value]" to the expression. *)

Ltac stock_store :=
  lazymatch goal with |- exec_stmt _ ?Q _ _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch goal with |- exec_stmt ?S _ _ _ _ =>
        lazymatch S with context [ update vareq _ V _ ] => fail | _ =>
          erewrite (@store_upd_eq _ V) by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Goal is not of the form (exec_stmt ...)"
  end.

Tactic Notation "stock_store" "in" hyp(XS) :=
  lazymatch type of XS with exec_stmt _ ?Q _ _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch type of XS with exec_stmt ?S _ _ _ _ =>
        lazymatch S with context [ update vareq _ V _ ] => fail | _ =>
          erewrite (@store_upd_eq _ V) in XS by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* Replace any unresolved variable lookups as fresh Coq variables after functional evaluation. *)

Ltac destr_ugets H :=
  try (rewrite fold_uget in H; repeat rewrite fold_uget in H;
       repeat match type of H with context [ uget ?X ] =>
         let UGET := fresh "UGET" in
         let utyp := fresh "utyp" in let mem := fresh "mem" in let n := fresh "n" in let w := fresh "w" in
         destruct (uget X) as [utyp mem n w] eqn:UGET
       end).

(* As the functional interpreter interprets stmts within a sequence, it infers memory access
   hypotheses as a side-effect of interpreting Load and Store expressions.  It splits these
   off into separate hypotheses in order to continue stepping the main exec_stmt hypothesis.
   Many are redundant (e.g., because Load or Store is applied to the same expression multiple
   times within the stmt), so we automatically clear any redundant ones. *)

Ltac nomemaccs T :=
  lazymatch T with NoMemAcc => idtac
  | if _ then ?E1 else ?E2 => nomemaccs E1; nomemaccs E2
  | ?E1 /\ ?E2 => nomemaccs E1; nomemaccs E2
  | _ => fail
  end.

Ltac destruct_memacc H :=
  lazymatch type of H with
  | _=_ /\ _=_ => idtac
  | exists _, _ => let u := fresh "u" in destruct H as [u H]; simpl_exp in H; simpl_stores in H
  | ?H1 /\ ?H1 =>
    lazymatch goal with
    | [ _:H1 |- _ ] => clear H
    | _ => apply proj1 in H; destruct_memacc H
    end
  | ?H1 /\ ?H2 =>
    lazymatch goal with
    | [ _:H1, _:H2 |- _ ] => clear H
    | [ _:H1 |- _ ] => apply proj2 in H; destruct_memacc H
    | [ _:H2 |- _ ] => apply proj1 in H; destruct_memacc H
    | _ => let H' := fresh "ACC" in destruct H as [H H']; destruct_memacc H; destruct_memacc H'
    end
  | ?T => try (nomemaccs T; clear H)
  end.

(* Finally, simplifying a hypothesis of the form (exec_stmt ...) entails applying the functional
   interpreter to each statement in the sequence (usually a Move), using simpl_stores to try to
   infer any unresolved variable-reads, using destr_ugets to abstract any unresolved store-reads,
   and repeating this until we reach a conditional or the end of the sequence.  (We don't attempt
   to break conditionals into cases automatically here, since often the caller wants to decide
   which case distinction is best.)

   Here, parameter "tac" is a caller-supplied tactic (taking a hypothesis as its argument) which
   is applied to simplify the expression after each step within a stmt.  This is most often useful
   for simplifying memory access hypotheses before they get split off from the main hypothesis. *)

Ltac finish_simpl_stmt tac H :=
  simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H; tac H; destruct_memacc H.

Tactic Notation "simpl_stmt" "using" tactic(tac) "in" hyp(H) :=
  lazymatch type of H with exec_stmt _ _ _ _ ?X =>
    let K := fresh "FIN" in enough (K: X <> Some Unfinished); [
    repeat (apply reduce_seq_move in H; [|exact K]; finish_simpl_stmt tac H);
    first [ apply reduce_nop in H; [|exact K]; unfold cast in H
          | apply reduce_move in H; [|exact K]; finish_simpl_stmt tac H
          | apply reduce_jmp in H; [|exact K]; finish_simpl_stmt tac H
          | apply reduce_if in H; [|exact K];
            simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H;
            match type of H with
            | exists _, _ => let c := fresh "c" in
                             destruct H as [c H]; simpl_exp in H; simpl_stores in H; destr_ugets H
            | _ => tac H; destruct_memacc H
            end ];
    clear K |]
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.

(* Combining all of the above, our most typical simplification regimen first stocks the store
   of the exec_stmt with any known variable values from the context, then applies the functional
   interpreter, and then unfolds a few basic constants. *)

Tactic Notation "bsimpl" "using" tactic(tac) "in" hyp(H) :=
  stock_store in H; simpl_stmt using tac in H; unfold tobit in H.

End PicinaeTheory.
