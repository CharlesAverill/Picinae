Require Import Picinae_theory.
Require Import riscv_collatz_smc.
Require Import Picinae_riscv.
Require Import NArith.
Require Import Lia ZifyN ZifyBool.

Import RISCVNotations.

Definition collatz_start : N :=  0x100.
Definition collatz_end   : N :=  0x100 + 4 * 10.

Section Invariants.
  Variables inp : N.
  Variable  s0 : store.

  Definition postcondition (s:store) :=
    s R_A0 = if N.even inp then inp >> 1 else inp ⊕ (1 ⊕ inp >> 1).
  Definition mem_unchanged (s:store) := s0 V_MEM32 = s V_MEM32 /\ s0 A_EXEC = s A_EXEC.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ => match a with
      | 0x100 => Some (mem_unchanged s /\ s R_A0 = inp)
      | 0x124 => Some (postcondition s)
      | _ => None end
    | _ => None end.
End Invariants.

Definition collatz_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x124 => true
  | _ => false
  end | _ => false end.

(* Overwrite the psa_some hook to use `cbv` rather than `cbv -[N.add]`.
   The RISCV program definition needs to reduce addition, whereasthe `-[N.add]`
   modifier was added to prevent aggressive reduction of `variable+offset`
   addresses in variably-placed ARMv7 code. *)
Ltac psa_some_hook ::=
  effinv_none_hook;
  cbv;
  match goal with |- ?G => idtac G end.

Theorem collatz_correctness:
  forall s t s' x' inp
         (ENTRY: startof t (x',s') = (Addr 0x100,s))
         (MDL: models rvtypctx s)
         (INP: s R_A0 = inp)
         (MEM: collatz_riscv s)
         (EXEC: collatz_riscv_aexec (s A_EXEC))
,
(* We define our program as rv_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-12 with all other bytes 0.
*)
  satisfies_all rv_prog (invs inp s) collatz_exit ((x',s')::t).
Proof.
Local Ltac step := time ISA_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY.
  step. repeat (split; try assumption).

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try (eassumption || apply welltyped_rvprog).
  clear MDL; intros MDL.
  clear - PRE MDL MEM EXEC. rename s into s0, t1 into t, s1 into s.

  destruct_inv 32 PRE.
  destruct PRE as ((MEMSAME & EXECSAME) & INP).
  unfold collatz_riscv, collatz_riscv_aexec in *; rewrite MEMSAME, EXECSAME in *.
  clear MEMSAME EXECSAME.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  Show Ltac Profile .
  Show Ltac Profile "reduce_getmem".
  (*
      tactic                                        local  total   calls       max
─────────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─reduce_getmem ------------------------------  67.5%  67.5%      80    1.369s
└reduce_getmem_hyp --------------------------  58.2%  64.1%     262    0.401s
 ├─erewrite (getmem_byte MEM) ---------------  54.9%  54.9%     119    0.367s
 ├─psimpl_lhs -------------------------------   0.0%   5.9%     119    0.029s
 │└psimpl_exp_goal --------------------------   0.0%   5.9%     119    0.029s
 │└_psimpl_exp_hyp --------------------------   0.0%   5.6%       0    0.028s
 │└__psimpl_exp_hyp -------------------------   0.1%   5.6%     119    0.028s
 │└<Picinae.Picinae_riscv.PSimpl_RISCV_v1_1.p   0.1%   3.7%     119    0.019s
 │└compute in H -----------------------------   3.0%   3.0%     119    0.016s
 └─lia --------------------------------------   0.0%   3.3%     357    0.008s
  └Zify.zify --------------------------------   0.1%   3.0%     476    0.008s
  └Zify.zify_to_euclidean_division_equations    0.1%   2.1%       0    0.007s
─reduce_frames ------------------------------   0.0%  25.3%      35    0.607s
└easy ---------------------------------------   0.1%  24.4%     136    0.078s
└inversion H --------------------------------  23.9%  23.9%    2022    0.071s
─solve_mod_rec ------------------------------   2.2%   5.5%      66    0.101s
└assert (H : a mod n = iN) by lia -----------   0.0%   5.2%      66    0.038s
└lia ----------------------------------------   0.0%   5.2%      66    0.038s
└Zify.zify ----------------------------------   0.0%   5.1%     108    0.037s
└Zify.zify_to_euclidean_division_equations --   0.0%   5.0%       0    0.037s
└PreOmega.Z.to_euclidean_division_equations_w   0.0%   4.9%     108    0.036s
└PreOmega.Z.euclidean_division_equations_clea   4.2%   4.3%     108    0.032s


     total time:     42.322s

 tactic                                        local  total   calls       max
─────────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─step ---------------------------------------   0.0% 100.0%       8    6.632s
─ISA_step -----------------------------------   0.0% 100.0%       8    6.632s
─effinv_none_hook ---------------------------   0.0%  99.5%      32    2.302s
─reduce_getmem ------------------------------  67.2%  67.2%      80    1.496s
─ISA_invseek --------------------------------   0.0%  65.9%       8    4.531s
─reduce_getmem_hyp --------------------------  58.0%  63.8%     262    0.420s
─erewrite (getmem_byte MEM) -----------------  54.6%  54.6%     119    0.384s
─ISA_invhere --------------------------------   0.0%  34.1%       8    2.302s
─psa_some_hook ------------------------------   0.0%  32.5%       8    2.204s
─reduce_frames ------------------------------   0.0%  26.3%      56    0.631s
─easy ---------------------------------------   0.1%  25.3%     143    0.088s
─inversion H --------------------------------  24.8%  24.8%    2285    0.076s
─lia ----------------------------------------   0.0%  10.9%     847    0.043s
─Zify.zify ----------------------------------   0.2%  10.1%    1071    0.043s
─Zify.zify_to_euclidean_division_equations --   0.1%   8.4%       0    0.042s
─PreOmega.Z.to_euclidean_division_equations_w   0.1%   7.5%    2190    0.041s
─psimpl_lhs ---------------------------------   0.0%   6.4%     211    0.031s
─PreOmega.Z.euclidean_division_equations_clea   6.2%   6.3%    1095    0.037s
─psimpl_exp_goal ----------------------------   0.0%   6.0%     167    0.031s
─_psimpl_exp_hyp ----------------------------   0.0%   5.7%       0    0.029s
─__psimpl_exp_hyp ---------------------------   0.1%   5.6%     286    0.029s
─solve_mod_rec ------------------------------   2.3%   5.6%      66    0.116s
─assert (H : a mod n = iN) by lia -----------   0.0%   5.3%      66    0.043s
─<Picinae.Picinae_riscv.PSimpl_RISCV_v1_1.psi   0.1%   3.7%     143    0.018s
─compute in H -------------------------------   3.0%   3.0%     183    0.016s

 tactic                                        local  total   calls       max
─────────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─step ---------------------------------------   0.0% 100.0%       8    6.632s
└ISA_step -----------------------------------   0.0% 100.0%       8    6.632s
 ├─ISA_invseek ------------------------------   0.0%  65.9%       8    4.531s
 │ ├─effinv_none_hook -----------------------   0.0%  32.9%       8    2.297s
 │ │ ├─reduce_getmem ------------------------  22.7%  22.7%      24    1.467s
 │ │ │└reduce_getmem_hyp --------------------  19.8%  21.7%      88    0.401s
 │ │ │└erewrite (getmem_byte MEM) -----------  18.7%  18.7%      40    0.363s
 │ │ └─reduce_frames ------------------------   0.0%   7.9%       8    0.616s
 │ │  └easy ---------------------------------   0.0%   7.6%      43    0.080s
 │ │  └inversion H --------------------------   7.5%   7.5%     637    0.072s
 │ └─psa_some_hook --------------------------   0.0%  32.5%       8    2.204s
 │  └effinv_none_hook -----------------------   0.0%  32.5%       8    2.204s
 │   ├─reduce_getmem ------------------------  22.4%  22.4%      24    1.430s
 │   │└reduce_getmem_hyp --------------------  19.5%  21.4%      88    0.384s
 │   │└erewrite (getmem_byte MEM) -----------  18.4%  18.4%      40    0.352s
 │   └─reduce_frames ------------------------   0.0%   7.8%       8    0.602s
 │    └easy ---------------------------------   0.0%   7.5%      43    0.082s
 │    └inversion H --------------------------   7.4%   7.4%     637    0.073s
 └─ISA_invhere ------------------------------   0.0%  34.1%       8    2.302s
  └effinv_none_hook -------------------------   0.0%  34.1%      16    2.302s
   ├─reduce_getmem --------------------------  22.1%  22.1%      32    1.496s
   │└reduce_getmem_hyp ----------------------  18.7%  20.7%      86    0.420s
   │└erewrite (getmem_byte MEM) -------------  17.5%  17.5%      39    0.384s
   ├─reduce_frames --------------------------   0.0%   9.2%      16    0.631s
   │└easy -----------------------------------   0.0%   8.9%      50    0.088s
   │└inversion H ----------------------------   8.7%   8.7%     748    0.076s
   └─solve_mod_rec --------------------------   1.0%   2.2%      26    0.116s
    └assert (H : a mod n = iN) by lia -------   0.0%   2.1%      26    0.043s
    └lia ------------------------------------   0.0%   2.1%      26    0.043s
    └Zify.zify ------------------------------   0.0%   2.1%      44    0.042s
    └Zify.zify_to_euclidean_division_equation   0.0%   2.0%       0    0.041s
    └PreOmega.Z.to_euclidean_division_equatio   0.0%   2.0%      44    0.041s
   *)

  assert (inp mod 2 < 2) by lia.
  destruct (inp mod 2) as [|p] eqn:EQ; try destruct p; try lia.

  step.
  Set Printing Parentheses.
  (* The goal now is just a typical Rocq goal. It is true because inp is even,
     so we must show (1+inp)>>1 = inp>>1, which is true because the increment
     is forgotten after shifting right. *)
  rewrite mod2_0_even in EQ; rewrite EQ.
  destruct inp;[reflexivity|].
  destruct p; reflexivity || discriminate || idtac. cbn. rewrite N.mod_small;[reflexivity|].
  pose proof (models_var R_A0 MDL). cbn in H0. lia.

  step.
  rewrite mod2_1_neven in EQ; rewrite EQ. reflexivity.
  (* Qed did not finish in 18458s (5h 05m) *)
Time Qed.
