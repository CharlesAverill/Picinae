Require Import memcmp_ft.
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

    (* The output of CRYPTO_memcmp is zero if and only if the two
       memory regions match up to `len` bytes *)
    Definition postcondition (s : store) : Prop :=
        s R_A0 = 0 <-> k_equal in_a in_b len.

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
              s V_MEM32 = mem)
        | 0x28 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              ((s R_A0 = 0) <-> k_equal in_a in_b k)
            )
        | 0x80 | 0x84 | 0x90 | 0x94 => Post 0 (postcondition s)
        | _ => NoInv
        end.

    Definition memcmp : program := lift_riscv memcmp_ft.

    Definition exits0 := make_exits 0 memcmp invs.
    Definition invs0 := make_invs 0 memcmp invs.
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

(* Proof in fault-free context *)
Theorem crypto_memcmp_correctness:
  forall s mem t xs' in_a in_b len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len),
  satisfies_all memcmp (invs0 mem in_a in_b len)
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

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & Mem). {
    step.
    - (* len = 0 *)
        (* apply N.eqb_eq in BC. *)
        repeat step. split; intro.
            unfold k_equal. lia.
            reflexivity.
    - (* len <> 0 *)
        repeat step.
            lia.
        exists 0. psimpl; repeat split; auto.
        lia. apply (models_var R_A2) in MDL. rewrite <- A2. apply MDL.
        unfold k_equal. lia.
    }

    (* Loop *)
    destruct PRE as (k & Mem & A5 & A1 & A2 & Bound & Eq). {
    repeat step.
    - (* in_a + k + 1 <> in_a + len, loop *)
        exists (k ⊕ 1). psimpl. repeat split. lia. lia.
        -- unfold k_equal. intros.
           apply or_xor_zero in H. destruct H.
           assert (i < k \/ i = k) by lia. destruct H2.
               now apply Eq.
           now subst.
        -- intros. rewrite N.mod_small in H by lia.
           pose proof (k_equal_inv _ _ _ _ H). apply Eq in H0.
           specialize (H k ltac:(lia)).
           now rewrite H, N.lxor_nilpotent, H0.
    - discriminate.
    - (* in_a + k + 1 = in_a + len, break *)
        assert (1 + k = len) by lia. subst len.
        clear BC0 BC.
        split; intro.
        -- apply or_xor_zero in H. destruct H. rewrite H in *.
           apply k_equal_step.
              now apply Eq.
              now rewrite H0.
        -- replace (s R_A0) with 0. psimpl.
           apply N.lxor_eq_0_iff.
           symmetry. apply H. lia.
           apply k_equal_inv in H. apply Eq in H.
           now rewrite H.
    }
Qed.

Section FaultTolerantInvariants.
    Variable mem : memory.
    Variable in_a in_b : addr.
    Variable len : N.

    Definition ft_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
              s V_MEM32 = mem /\ s V_FC = 1)
        | 0x28 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              s V_FC <= 1 /\
              ((s R_A0 = 0) <-> k_equal mem in_a in_b k)
            )
        | 0x80 | 0x84 | 0x90 | 0x94 => Post 0 (postcondition mem in_a in_b len s)
        | _ => NoInv
        end.

    Definition fault_memcmp := inject_fault memcmp.

    Definition ft_exits0 := make_exits 0 fault_memcmp ft_invs.
    Definition ft_invs0 := make_invs 0 fault_memcmp ft_invs.
End FaultTolerantInvariants.
    
(* Proof in fault-free context *)
Theorem crypto_memcmp_ft_correctness:
  forall s mem t xs' in_a in_b len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (FC: s V_FC = 1),
  satisfies_all fault_memcmp
                       (ft_invs0 mem in_a in_b len)
                       (ft_exits0 mem in_a in_b len) (xs'::t).
Proof using.
    Local Ltac step ::= 
        match goal with
        | [s' : store, FC : ?s' V_FC <= 1 |- _] =>
            let H := fresh "H" in
            assert (s' V_FC = 0 \/ s' V_FC = 1) as H by lia;
            clear FC; destruct H
        | _ => idtac
        end;
        time r5_step;
        repeat match goal with
        | [n : N, BC : ?n mod 2 = _ |- _] => clear BC n
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_fault_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & Mem & FC). {
    Local Ltac solve_inv MDL A2 :=
        exists 0; psimpl; repeat split; auto;
            [lia|
            apply (models_var R_A2) in MDL; rewrite <- A2; apply MDL
            |lia|unfold k_equal; lia].
    step.
    - (* len = 0, no fault *)
        repeat step; split; intro;
            unfold k_equal; lia.
    - (* len <> 0, no fault *)
        repeat (step; [| repeat step; solve_inv MDL A2]); solve_inv MDL A2.
    - (* fault *) 
        repeat step.
            split; intro; unfold k_equal; lia.
        solve_inv MDL A2.
    }

    (* Loop *)
    destruct PRE as (k & Mem & A5 & A1 & A2 & Bound & FC & Eq). {
    Local Ltac solve_inv' k Eq :=
        let X := fresh "X" in
        let Y := fresh "Y" in
        let Z := fresh "Z" in
        let W := fresh "W" in
        let Inv := fresh "Inv" in
        let i := fresh "i" in
        exists (k ⊕ 1); psimpl; repeat split;
        [lia|lia|lia
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
    repeat step.
    par: match goal with
        | [ |- context[exists _, _] ] => solve_inv' k Eq
        | [ |- context[_ /\ _]] => solve_post k len s Eq
        | _ => idtac
        end.
    }
Qed.
