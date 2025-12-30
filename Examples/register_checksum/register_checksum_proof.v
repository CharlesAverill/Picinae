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
             checksum : N.

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
        inject_memory_corruption (inject_skip register_checksum).

    Definition invs' :=
            invs a1 a2 a3 a4 a5 a6 a7
                 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 checksum.

    Definition exits0' := make_exits 0 register_checksum_faulty invs'.
    Definition invs0' := make_invs 0 register_checksum_faulty invs'.
End FaultTolerantInvariants.

(* Proof in single-fault context *)
Theorem register_checksum_correctness_faulty:
  forall s t xs' a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (REGS: regs a1 a2 a3 a4 a5 a6 a7
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     checksum s),
  satisfies_all register_checksum 
        (invs0' a1 a2 a3 a4 a5 a6 a7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                checksum)
        (exits0' a1 a2 a3 a4 a5 a6 a7
                 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 checksum) (xs'::t).
Proof using.
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

    repeat step; try lia;
        intro Contra; unfold postcondition in Contra;
        psimpl in Contra; lia.
Qed.
