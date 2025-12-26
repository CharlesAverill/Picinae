Require Import tmr_ft.
Require Import Picinae_riscv.
Import RVFaultTolerance.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia ZifyN ZifyBool.

Import ListNotations.
Open Scope N_scope.

Section Invariants.
    Variable mem : memory.
    Variable in_a in_b : addr.
    Variable len : N.

    Definition k_equal (p1 p2 : addr) (k : N) : Prop :=
        forall (i : N),
            i < k ->
            mem Ⓑ[p1 + i] = mem Ⓑ[p2 + i].

    (* The output of tmr is zero if and only if the two
       memory regions match up to `len` bytes *)
    Definition postcondition (s : store) : Prop :=
        s R_A0 = 0 <-> k_equal in_a in_b len.

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
              s V_MEM32 = mem)
        | 0x40 => Inv 0
            (* Either the invariant is satisfied or we skipped something
               and all bets are off *)
            (exists k,
              s V_MEM32 = mem /\
              s R_A4 = in_a ⊕ k /\
              s R_A7 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              s R_A0 = in_a /\ s R_A1 = in_b /\
              s R_A5 = in_a /\ s R_A6 = in_b /\
              k < len < 2^32 /\
              ((s R_T1 = 0) <-> k_equal in_a in_b k)
            )
        | 0x60 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A0 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              s R_A5 = in_a /\ s R_A6 = in_b /\
              k < len < 2^32 /\
              ((s R_A3 = 0) <-> k_equal in_a in_b k) /\
              ((s R_T1 = 0) <-> k_equal in_a in_b len)
            )
        | 0x80 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A6 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              ((s R_A1 = 0) <-> k_equal in_a in_b k) /\
              ((s R_A3 = 0) <-> k_equal in_a in_b len) /\
              ((s R_T1 = 0) <-> k_equal in_a in_b len)
            )
        | 0xdc | 0xe0 => Post 0 (postcondition s)
        | _ => NoInv
        end.

    Definition tmr : program := lift_riscv tmr_ft.

    Definition exits0 := make_exits 0 tmr invs.
    Definition invs0 := make_invs 0 tmr invs.
End Invariants.

Lemma k_equal_inv : forall mem a b k,
    k_equal mem a b (1 + k) ->
    k_equal mem a b k.
Proof.
    intros. unfold k_equal in *.
    intros. apply H. lia.
Qed.

Lemma k_equal_step : forall mem a b k,
    k_equal mem a b k ->
    mem Ⓑ[a + k] = mem Ⓑ[b + k] ->
    k_equal mem a b (1 + k).
Proof.
    intros. unfold k_equal in *.
    intros. assert (i = k \/ i < k) by lia. destruct H2.
        subst. assumption.
    now apply H.
Qed.

Lemma or_xor_zero : forall a b c,
    a .| b .^ c = 0 ->
    a = 0 /\ b = c.
Proof.
    intros.
    replace a with 0 in * by (symmetry; eapply N.lor_eq_0_l, H).
    split. reflexivity.
    psimpl in H.
    now apply N.lxor_eq.
Qed.

Lemma neq_lxor : forall a b,
    a <> b -> a .^ b <> 0.
Proof.
    intros a b H Contra.
    apply N.lxor_eq in Contra. contradiction.
Qed.    

(* Proof in fault-free context *)
Theorem tmr_correctness:
  forall s mem t xs' in_a in_b len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len),
  satisfies_all tmr (invs0 mem in_a in_b len)
                    (exits0 mem in_a in_b len) (xs'::t).
Proof using.
    Local Ltac step := time r5_step.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro 1 *)
    destruct PRE as (A0 & A1 & A2 & Mem). {
    step.
    - (* len = 0 *)
        (* apply N.eqb_eq in BC. *)
        repeat step. split; intro.
            unfold k_equal. lia.
            reflexivity.
    - (* len <> 0 *)
        repeat step.
            discriminate.
        exists 0. psimpl; repeat split; auto.
        lia. apply (models_var R_A2) in MDL. rewrite <- A2. apply MDL.
        unfold k_equal. lia.
    }

    (* Loop 1 *)
    destruct PRE as (k & Mem & A4 & A7 & A2 & A0 & A1 & A5 & A6 & Bound & Eq). {
    repeat step.
    - (* loop *)
        exists (k ⊕ 1). psimpl. repeat split; auto. lia. lia.
        -- unfold k_equal. intros.
           apply or_xor_zero in H. destruct H.
           assert (i < k \/ i = k) by lia. destruct H2.
               now apply Eq.
           now subst.
        -- intros. rewrite N.mod_small in H by lia.
           pose proof (k_equal_inv _ _ _ _ H). apply Eq in H0.
           specialize (H k ltac:(lia)).
           now rewrite H, N.lxor_nilpotent, H0.
    - (* break and go to next one *)
        exists 0. psimpl. repeat split; auto; intros.
        lia. lia. unfold k_equal; lia.
        all: replace len with (1 + k) in * by lia.
        -- apply or_xor_zero in H. destruct H. rewrite H in *.
           apply k_equal_step.
              now apply Eq.
              now rewrite H0.
        -- replace (s R_T1) with 0. psimpl.
           apply N.lxor_eq_0_iff.
           symmetry. apply H. lia.
           apply k_equal_inv in H. apply Eq in H.
           now rewrite H.
    }

    (* Loop 2 *)
    destruct PRE as (k & Mem & A0 & A1 & A2 & A5 & A6 & Bound & Eq & Last). {
    repeat step.
    - exists (k ⊕ 1). psimpl. repeat (split; auto); try lia.
        -- unfold k_equal. intros.
           apply or_xor_zero in H. destruct H.
           assert (i < k \/ i = k) by lia. destruct H2.
               now apply Eq.
           now subst.
        -- intros. rewrite N.mod_small in H by lia.
           pose proof (k_equal_inv _ _ _ _ H). apply Eq in H0.
           specialize (H k ltac:(lia)).
           now rewrite H, N.lxor_nilpotent, H0.
    - (* break and go to next one *)
        exists 0. psimpl. repeat (split; auto); intros.
        lia. lia. unfold k_equal; lia.
        all: replace len with (1 + k) in * by lia.
        -- apply or_xor_zero in H. destruct H. rewrite H in *.
           apply k_equal_step.
              now apply Eq.
              now rewrite H0.
        -- replace (s R_A3) with 0. psimpl.
           apply N.lxor_eq_0_iff.
           symmetry. apply H. lia.
           apply k_equal_inv in H. apply Eq in H.
           now rewrite H.
    }

    (* Loop 3 *)
    destruct PRE as (k & Mem & A5 & A6 & A2 & Bound & Eq & Last1 & Last2). {
    repeat step.
    - exists (k ⊕ 1). psimpl. repeat (split; auto); try lia.
        -- unfold k_equal. intros.
           apply or_xor_zero in H. destruct H.
           assert (i < k \/ i = k) by lia. destruct H2.
               now apply Eq.
           now subst.
        -- intros. rewrite N.mod_small in H by lia.
           pose proof (k_equal_inv _ _ _ _ H). apply Eq in H0.
           specialize (H k ltac:(lia)).
           now rewrite H, N.lxor_nilpotent, H0.
    - (* exit *)
        replace len with (1 + k) in * by lia.
        split; intro.
        -- destruct N.ltb eqn:E in H. discriminate. clear H.
            apply N.ltb_ge, N.le_0_r, N.lor_eq_0_iff in E.
            destruct E.
            rewrite N.land_lor_distr_r in H, H0.
            apply N.lor_eq_0_iff in H, H0. destruct H, H0.
            rewrite N.land_lor_distr_r in H1.
            apply N.lor_eq_0_iff in H1. destruct H1.
            destruct (N.eq_dec (s R_T1) 0).
                rewrite e in *. now apply Last2.
            destruct (N.eq_dec (s R_A3) 0).
                rewrite e in *. now apply Last1.
            destruct (N.eq_dec (s R_A1) 0).
                rewrite e in *; clear e H1 H0 Last1 Last2.
                apply k_equal_step. now apply Eq.
            destruct (N.eq_dec (s R_T1) (s R_A3)).
                rewrite e in *; clear e.
                rewrite N.land_diag in H. contradiction.
            destruct (N.eq_dec (s R_T1) (mem Ⓑ[ in_b + k ] .^ mem Ⓑ[ in_a + k ])).
                rewrite e in *; clear e.
                rewrite N.land_diag in H3. contradiction.
            destruct (N.eq_dec (s R_A3) (mem Ⓑ[ in_b + k ] .^ mem Ⓑ[ in_a + k ])).
                rewrite e in *; clear e.
                rewrite N.land_diag in H2. contradiction.
            (* How the heck do I show that this is a contradiction? *)
            admit.
            admit.
    }
Admitted.
