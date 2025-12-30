Require Import register_checksum.
Require Import Picinae_riscv.
Import RVFaultTolerance.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia ZifyN ZifyBool.

Import ListNotations.
Open Scope N_scope.

Section Invariants.
    Variable    a1 a2 a3 a4 a5 a6 a7
             s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             checksum fc : N.

    Definition postcondition : Prop :=
        (     a1 ⊕ a2 ⊕ a3 ⊕ a4 ⊕ a5 ⊕ a6 ⊕ a7 ⊕
         s0 ⊕ s1 ⊕ s2 ⊕ s3 ⊕ s4 ⊕ s5 ⊕ s6 ⊕ s7 ⊕ s8 ⊕ s9 ⊕ s10 ⊕ s11
            = checksum).

    Definition regs (s : store) : Prop :=
        s R_A0 = checksum /\
        s R_A1 = a1 /\
        s R_A2 = a2 /\
        s R_A3 = a3 /\
        s R_A4 = a4 /\
        s R_A5 = a5 /\
        s R_A6 = a6 /\
        s R_A7 = a7 /\

        s R_S0 = s0 /\
        s R_S1 = s1 /\
        s R_S2 = s2 /\
        s R_S3 = s3 /\
        s R_S4 = s4 /\
        s R_S5 = s5 /\
        s R_S6 = s6 /\
        s R_S7 = s7 /\
        s R_S8 = s8 /\
        s R_S9 = s9 /\
        s R_S10 = s10 /\
        s R_S11 = s11.

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0 (regs s)
        | 0x1c0 | 0x1c4 => Post 0 (~ postcondition)
        | 0x1c8 | 0x1cc => Post 0 (postcondition)
        | _ => NoInv
        end.

    Definition register_checksum : program :=
        lift_riscv register_checksum.

    Definition exits0 := make_exits 0 register_checksum invs.
    Definition invs0 := make_invs 0 register_checksum invs.
End Invariants.

(* Proof in fault-free context *)
Theorem register_checksum_correctness:
  forall s t xs' a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (REGS: regs a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum s),
  satisfies_all register_checksum 
        (invs0 a1 a2 a3 a4 a5 a6 a7
               s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               checksum)
        (exits0 a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum) (xs'::t).
Proof using.
    Local Ltac step := time r5_step.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. now unfold regs in REGS.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s12 into s. rename a0 into a.

    destruct_inv 32 PRE.

    destruct PRE as
        (CHK & A1 & A2 & A3 & A4 & A5 & A6 & A7 &
          S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).

    repeat step.
    - lia.
    - discriminate.
    - intro Contra. unfold postcondition in Contra.
      psimpl in Contra. lia.
Qed.

Section FaultTolerantInvariants.
    Variable    a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum : N.

    Definition register_checksum_faulty : program :=
        inject_skip (register_checksum).

    Definition invs' T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        let regs := regs a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum in
        let postcondition := postcondition a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum in
        match a with
        | 0x0 => Inv 0 (regs s /\ s V_FC = 1)
        (* Goal space cinch *)
        | 0x98 => Inv 0 (regs s /\ s V_FC <= 1 /\
                         s R_T1 = a1 ⊕ a2 ⊕ a3 ⊕ a4 ⊕ a5 ⊕ a6 ⊕ a7)
        | 0x1c0 | 0x1c4 => Post 0 (~ postcondition)
        | 0x1c8 | 0x1cc => Post 0 (postcondition)
        | _ => NoInv
        end.

    Definition exits0' := make_exits 0 register_checksum_faulty invs'.
    Definition invs0' := make_invs 0 register_checksum_faulty invs'.
End FaultTolerantInvariants.

Lemma register_checksum_faulty_wt:
    welltyped_prog rvtypctx register_checksum_faulty.
Proof.
Admitted.

(* Proof in single-fault context *)
Theorem register_checksum_correctness_faulty:
  forall s t xs' a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (REGS: regs a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum s)
         (FC: s V_FC = 1),
  satisfies_all register_checksum_faulty 
        (invs0' a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum)
        (exits0' a1 a2 a3 a4 a5 a6 a7
                 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 checksum) (xs'::t).
Proof using.
    Local Ltac step ::= 
        match goal with
        | [s' : store, FC : ?s' V_FC <= 1 |- _] =>
            let H := fresh "H" in
            assert (s' V_FC = 0 \/ s' V_FC = 1) as H by lia;
            clear FC; destruct H
        | _ => idtac
        end;
        r5_step;
        repeat match goal with
        | [n : N, BC : ?n mod 2 = _ |- _] => clear BC n
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step.
        split; [now unfold regs in REGS|assumption].

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply register_checksum_faulty_wt).
    clear - PRE MDL. rename t1 into t. rename s12 into s. rename a0 into a.

    destruct_inv 32 PRE.

    destruct PRE as
        ((CHK & A1 & A2 & A3 & A4 & A5 & A6 & A7 &
          S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11) & 
          FC). {
    replace s with (update s V_FC 1) by
        now erewrite store_upd_eq.

    repeat (match goal with
            | [|- context[Addr ?x]] =>
                idtac x "/" 460
            end; step; [|
        time (repeat step; idtac "Solving invariant";
        repeat split; psimpl; auto; lia)]).

    split. unfold regs; psimpl;
        repeat split; auto.
    split; reflexivity.
    }

    destruct PRE as
        ((CHK & A1 & A2 & A3 & A4 & A5 & A6 & A7 &
          S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11) & 
          FC & T1).

    Ltac solve_post :=
        match goal with
        | [BC: _, BC0: _ |- _ -> False] =>
            let Contra := fresh "Contra" in
            intro Contra; unfold postcondition in Contra;
            psimpl in Contra; rewrite Contra in BC0;
            rewrite N.eqb_refl in BC0; discriminate
        | [BC: (_ =? _) = true |- _] =>
            apply N.eqb_eq in BC; now rewrite BC
        end.

    repeat (match goal with
            | [|- context[Addr ?x]] =>
                idtac x "/" 460
            end; step; match goal with 
            | [|- context[update _ V_FC 0]] => 
                idtac "Faulted, stepping to postcondition...";
                time (repeat time step; idtac "Solving postcondition";
                    solve_post)
            | _ => idtac
            end).

    apply N.eqb_eq in BC0; now rewrite BC0.
    intro Contra; unfold postcondition in Contra;
        psimpl in Contra; rewrite Contra in BC1;
        rewrite N.eqb_refl in BC1; discriminate.
    intro Contra; unfold postcondition in Contra;
        psimpl in Contra; rewrite Contra in BC0;
        rewrite N.eqb_refl in BC0; discriminate.
Qed.
