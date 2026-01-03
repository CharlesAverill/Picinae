Require Import memcmp_ft.
Require Import Picinae_riscv.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia ZifyN ZifyBool.

Import ListNotations.
Open Scope N_scope.

Module FaultModel' <: FaultModel.
    Import FTC.
    Definition fault_spacing := 1.
    Theorem fault_spacing_small : fault_spacing < 2^w.
    Proof. unfold fault_spacing, w. lia. Qed.

    Definition max_faults := 2.
End FaultModel'.
Module FT' := RVFaultTolerance FaultModel'.
Import FT'.

Section FaultTolerantInvariants.
    Variable mem : memory.
    Variable in_a in_b : addr.
    Variable len : N.

    Definition k_equal (p1 p2 : addr) (k : N) : Prop :=
        forall (i : N),
            i < k ->
            mem Ⓑ[p1 + i] = mem Ⓑ[p2 + i].

    (* The output of CRYPTO_memcmp is zero if and only if the two
       memory regions match up to `len` bytes *)
    Definition postcondition (s : store) : Prop :=
        s R_A0 = 0 <-> k_equal in_a in_b len.

    Definition ft_invs' T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
              s V_MEM32 = mem /\
              fault_assumptions s)
        | 0x28 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              fault_invs s /\
              ((s R_A0 = 0) <-> k_equal in_a in_b k)
            )
        | 0x80 | 0x84 | 0x90 | 0x94 => Post 0 (postcondition s)
        | _ => NoInv
        end.

    Definition fault_memcmp := inject_skip (lift_riscv memcmp_ft).

    Definition ft_exits0' := make_exits 0 fault_memcmp ft_invs'.
    Definition ft_invs0' := make_invs 0 fault_memcmp ft_invs'.
End FaultTolerantInvariants.

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

(* Proof in fault-free context *)
Theorem crypto_memcmp_ft_correctness':
  forall s mem t xs' in_a in_b len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (FAULT: fault_assumptions s),
  satisfies_all fault_memcmp
                       (ft_invs0' mem in_a in_b len)
                       (ft_exits0' mem in_a in_b len) (xs'::t).
Proof using.
    Ltac step := fault_step r5_step.
    Tactic Notation "estep" tactic(T) :=
        eager_step r5_step by T.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. now repeat (split; [assumption|]).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_skip_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & Mem & FC).
    Local Ltac solve_inv MDL A2 :=
        exists 0; psimpl; repeat split; auto; try solve_fault_invs;
            [lia|
            apply (models_var R_A2) in MDL; rewrite <- A2; apply MDL
            |unfold k_equal; lia].
    estep (solve_inv MDL A2 || split; intro; unfold k_equal; lia).

    (* Loop *)
    destruct PRE as (k & Mem & A5 & A1 & A2 & Bound & FC & Eq).
    Local Ltac solve_inv' k Eq :=
        let X := fresh "X" in
        let Y := fresh "Y" in
        let Z := fresh "Z" in
        let W := fresh "W" in
        let Inv := fresh "Inv" in
        let i := fresh "i" in
        exists (k ⊕ 1); psimpl; repeat split;
        [lia|lia|solve_fault_invs
        | unfold k_equal; intros X i Z; apply or_xor_zero in X; destruct X;
            assert (i < k \/ i = k) as Y by lia; destruct Y;
            [now apply Eq|now subst]
        | repeat split; intros W; rewrite N.mod_small in W by lia;
            pose proof (k_equal_inv _ _ _ _ W) as Inv; apply Eq in Inv;
            specialize (W k ltac:(lia));
            now rewrite W, N.lxor_nilpotent, Inv].
    Local Ltac solve_post k len s Eq :=
        let X := fresh "H" in
        let i := fresh "i" in
        let ILen := fresh "ilen" in
        let KLen := fresh "klen" in
        assert (1 + k = len) as KLen by lia;
        subst len;
        split; intro X;
            [apply k_equal_step;
              apply or_xor_zero in X; destruct X;
              [apply Eq; assumption|now symmetry]
            |replace (s R_A0) with 0; psimpl;
              [apply N.lxor_eq_0_iff; symmetry; apply X; lia
              |apply k_equal_inv in X; symmetry; apply Eq, X]
            ].
    estep (
        idtac "Solving";
        solve_inv' k Eq || solve_post k len s Eq).
Qed.
