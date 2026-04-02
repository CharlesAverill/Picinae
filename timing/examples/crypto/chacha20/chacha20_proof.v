Require Import ChaCha20.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_ChaCha20 <: ProgramInformation.
    Definition entry_addr : N := 0x224.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0xcc0 => true
        | _ => false
    end | _ => false end.

    Definition binary := ChaCha20.
End Program_ChaCha20.

Module RISCVTiming := RISCVTiming cpu Program_ChaCha20.
Module ChaCha20Auto := RISCVTimingAutomation RISCVTiming.
Import Program_ChaCha20 ChaCha20Auto.

Definition time_of_chacha20_quarter : N :=
  tadd + txor + tslli 0x10 +
  tadd + txor + tslli 0xc +
  tadd + txor + tslli 0x8 +
  tadd + txor + tsw + tslli 0x7 +
  tsw + tsw + tjalr.

Definition time_of_chacha20_block (t : trace) : Prop :=
  cycle_count_of_trace t = taddi + 13 * tsw + 4 * taddi +
      4 * (tsw + tlui + taddi) + 
      8 * (tsw + taddi + 4 * tlbu + 4 * tsb + tlw) +
      tsw + 4 * tlbu + 4 * tsb + tlw + 
      2 * (taddi + 4 * tlbu + 4 * tsb + tlw) +
      4 * taddi + 10 * tsw + taddi + tsw + tsw +
      10 * (4 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        tsw + 6 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        8 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        4 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        4 * taddi + 4 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter + 
        taddi + taddi) + 9 * ttbne + tfbne +
    172 * tsb + 108 * tlbu + 65 * tlw +
    16 * (tsrli 0x8 + tsrli 0x10 + tsrli 0x18) +
    16 * tadd + 16 * txor + 7 * taddi + 
    4 * tlui + tjalr.

Definition ChaCha20_timing_invs (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x224 => Some (cycle_count_of_trace t' = 0)
| 0x4b8 => Some (1 <= s R_S3 <= 10 /\
    cycle_count_of_trace t' = taddi + 13 * tsw + 4 * taddi +
        4 * (tsw + tlui + taddi) + 
        8 * (tsw + taddi + 4 * tlbu + 4 * tsb + tlw) +
        tsw + 4 * tlbu + 4 * tsb + tlw + 
        2 * (taddi + 4 * tlbu + 4 * tsb + tlw) +
        4 * taddi + 10 * tsw + taddi + tsw + tsw +
        (10 - s R_S3) * (4 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          tsw + 6 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          8 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          4 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          4 * taddi + 4 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter + 
          taddi + taddi + ttbne)
  )
| 0xcc0 => Some (time_of_chacha20_block t)
| _ => None end | _ => None end.

Local Ltac step := tstep r5_step.

(* Find any N or memory variables that are unused in the goal and try to clear them *)
Ltac clear_unused :=
  repeat match goal with
  | H : N |- _ =>
    tryif (clear dependent H) then idtac else fail
  | H : memory |- _ =>
    tryif (clear dependent H) then idtac else fail
  end.

Ltac important x :=
  match x with
  | R_S3 => true | R_RA => true
  | _ => false
  end.

(* Attempt to generalize the contents of a register if they are not important to the
   control flow of the program *)
Ltac generalize_reg :=
  repeat multimatch goal with
  | [|- context[update _ ?r (?f ?x)]] =>
    match important r with
    | true => idtac
    | false => generalize (f x); intros
    end
  | _ => idtac
  end;
  clear_unused.

(* Step and generalize *)
Ltac gstep := step; generalize_reg.

Theorem ChaCha20_timing:
  forall s (t : trace) s' x'
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_prog
    (ChaCha20_timing_invs)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    simpl. rewrite ENTRY. unfold entry_addr. step. reflexivity.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - (* 0x224 -> 4b8 *)
      repeat gstep. 
      split.
        lia.
        hammer.
    - (* 0x4b8 -> 0x5ec *)
      destruct PRE as (S3 & Cycles).
      do 206 gstep.
      -- (* Invariant 0x4b8 after looping *)
        replace (s' R_S3 ⊖ 1) with (s' R_S3 - 1) in * by
          (rewrite msub_nowrap; psimpl; lia).
        apply Bool.negb_true_iff in BC.
        split.
          apply N.eqb_neq in BC; lia.
        (* Some manual reformatting of the goal helps hammer out *)
        replace (10 - (s' R_S3 - 1)) with 
          (1 + (10 - s' R_S3)) by lia.
        repeat rewrite (N.mul_add_distr_r 1).
        (* We don't want N.sub to be unfolded in the RHS while hammer should be
           focusing on cycle_count_of_trace *)
        match goal with
        |[|-context[(10 - _) * ?x]] =>
          remember x as loop_body_time
        end.
        remember (10 - (s' R_S3)) as loop_iterations.
        hammer.
        (* Now we can put the subs back in *)
        subst loop_iterations loop_body_time.
        unfold time_of_chacha20_quarter.
        hammer.
      -- (* Postcondition after breaking out of the loop *)
        repeat gstep. (* ~437 steps *)
        hammer.
        unfold time_of_chacha20_quarter.
        apply Bool.negb_false_iff, N.eqb_eq in BC.
          rewrite msub_nowrap in BC by (psimpl; lia). psimpl in BC.
        replace (s' R_S3) with 1 in * by lia.
        hammer.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall t,
    time_of_chacha20_block t = 
    (ChaCha20Auto.cycle_count_of_trace t = 
      12375 + 982 * T_data_latency + 170 * T_inst_latency).
Proof.
    intros. unfold time_of_chacha20_block. f_equal.
    unfold time_of_chacha20_quarter, taddi, tsw, tlui,
      tlbu, tlw, tadd, txor, tslli, ttbne, tfbne, tjalr, tjal,
      tsb, tsrli, T_shift_latency, NEORV32BaseConfig.CPU_FAST_SHIFT_EN. lia.
Qed.
