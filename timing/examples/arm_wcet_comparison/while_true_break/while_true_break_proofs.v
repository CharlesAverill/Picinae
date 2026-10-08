Require Import while_true_break_lifted.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module Program_while_true_break <: ProgramInformation.
    Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x34 => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
        (* 0x0 : MOV RDX,RDI *)
        | 0x0 => mov_r64_r64
        (* 0x3 : LEA RCX,[RDI + RDI*0x1] *)
        | 0x3 => lea_r64_addr
        (* 0x7 : MOV RAX,RDI *)
        | 0x7 => mov_r64_r64
        (* 0xa : IMUL RDX,RDI *)
        | 0xa => imul_r64_r64
        (* 0xe : CMP RCX,RDX *)
        | 0xe => cmp_r64_r64
        (* 0x11 : JNC 0x... *)
        | 0x11 => jnc_addr
        (* 0x13 : NOP dword ptr CS:[RAX + RAX*0x1] (lifted to address calc) *)
        | 0x13 => nop
        (* 0x1e : NOP *)
        | 0x1e => nop
        (* 0x20 : SUB RAX,0x1 *)
        | 0x20 => sub_r64_i
        (* 0x24 : MOV RDX,RAX *)
        | 0x24 => mov_r64_r64
        (* 0x27 : LEA RCX,[RAX + RAX*0x1] *)
        | 0x27 => lea_r64_addr
        (* 0x2b : IMUL RDX,RAX *)
        | 0x2b => imul_r64_r64
        (* 0x2f : CMP RCX,RDX *)
        | 0x2f => cmp_r64_r64
        (* 0x32 : JC 0x... *)
        | 0x32 => jc_addr
        (* 0x34 : RET *)
        | 0x34 => ret
        | _ => time_inf
        end.

    Definition lifted_prog := while_true_break_amd64.
End Program_while_true_break.

Module AMD64Timing := AMD64Timing cpu Program_while_true_break.
Module while_true_breakAuto := AMD64TimingAutomation AMD64Timing.
Import Program_while_true_break while_true_breakAuto.

Definition time_of_while_true_break (n : N) (t : trace) :=
  cycle_count_of_trace t <=
    mov_r64_r64 + lea_r64_addr + mov_r64_r64 + imul_r64_r64 + cmp_r64_r64 +
    jnc_addr +
    if (n * n <=? n + n) then ret else (
        nop + nop +
        (* loop iters *)
        (n - 2) * (
            sub_r64_i + mov_r64_r64 + lea_r64_addr + imul_r64_r64 +
            cmp_r64_r64 + jc_addr
        ) + ret
    ).

Definition while_true_break_timing_invs (n : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
    s R_RDI = n /\ 0 <= n < 1000 /\
    cycle_count_of_trace t' = 0
  )
| 0x20 => Some (
    3 <= n < 1000 /\
    3 <= s R_RAX <= n /\
    n * n <=? n + n = false /\
    cycle_count_of_trace t' <=
        mov_r64_r64 + lea_r64_addr + mov_r64_r64 + imul_r64_r64 + cmp_r64_r64 +
        jnc_addr + nop + nop +
        (* loop iters *)
        (n - s R_RAX) * (
            sub_r64_i + mov_r64_r64 + lea_r64_addr + imul_r64_r64 +
            cmp_r64_r64 + jc_addr
        )
  )
| 0x34 => Some (time_of_while_true_break n t)
| _ => None end | _ => None end.

Lemma Contra : forall n,
    n * n <= n + n -> n <= 2.
Proof.
    induction n using N.peano_ind; intros.
        lia.
    lia.
Qed.

Theorem while_true_break_timing:
  forall s t s' x' n
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (RDI: s R_RDI = n)
         (EDI: 0 <= n < 1000),
  satisfies_all
    lifted_prog
    (while_true_break_timing_invs n)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep x64_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.

    - destruct PRE as (RDI & Bounds & Cycles).
        repeat step.
        rewrite N.mod_small in BC by lia.
        assert (n * n < 2^64). {
            change (2^64) with (2^32 * 2^32).
            rewrite <- N.square_lt_mono. lia.
        }
        rewrite N.mod_small in BC by lia.
        split.
            destruct n using N.peano_ind. discriminate.
            destruct n using N.peano_ind. discriminate.
            destruct n using N.peano_ind. discriminate.
            lia.
        split.
            destruct n using N.peano_ind. discriminate.
            destruct n using N.peano_ind. discriminate.
            lia.
        split. lia.
        hammer.
        rewrite N.mod_small in BC by lia.
        assert (n * n < 2^64). {
            change (2^64) with (2^32 * 2^32).
            rewrite <- N.square_lt_mono. lia.
        }
        rewrite N.mod_small in BC by lia.
        replace (n * n <=? n + n) with true by lia.
        hammer.
    - destruct PRE as (NBounds & Bounds & Path & Cycles).
        repeat step.
        split. assumption.
        split.
            rewrite msub_nowrap by (psimpl; lia). psimpl. split; [| lia].
            destruct (s' R_RAX) using N.peano_ind. lia.
            destruct n0 using N.peano_ind. lia.
            destruct n0 using N.peano_ind. clear IHn0 IHn1.
                cbv [N.succ Pos.succ] in BC. psimpl in BC. discriminate.
            destruct n0 using N.peano_ind. clear IHn0 IHn1 IHn2.
                cbv [N.succ Pos.succ] in BC. psimpl in BC. discriminate.
                clear. lia.
        split. assumption.
        hammer.
            rewrite msub_nowrap by (psimpl; lia).
            psimpl. rewrite N.sub_sub_distr by lia. lia.

        rewrite Path.
        hammer.
        rewrite msub_nowrap, msub_nowrap in BC by lia.
        psimpl in BC. rewrite N.mod_small in BC by lia.
        rewrite N.mod_small in BC.
        replace (s' R_RAX - 2 + s' R_RAX) with
            ((s' R_RAX - 1) + (s' R_RAX - 1)) in BC by lia.
        apply N.ltb_ge, Contra in BC.
        assert (s' R_RAX = 3) by lia. clear BC. rewrite H in Cycles.
        replace (n - 2) with (1 + (n - 3)) by lia. lia.
        change (2^64) with (2^32 * 2^32). rewrite <- N.square_lt_mono.
        lia.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_while_true_break := TimingProof i5_7300u.

Goal forall (n : N) (t : trace),
    i5_7300u_while_true_break.time_of_while_true_break n t =
    (i5_7300u_while_true_break.while_true_breakAuto.cycle_count_of_trace t <=
        (if n <=? 2 then 52 else 56 + (n - 2) * 26)).
    intros.
    unfold i5_7300u_while_true_break.time_of_while_true_break. simpl.
    replace (n * n <=? n + n) with (n <=? 2).
    unfold i5_7300u.ret. psimpl.
    reflexivity.
    destruct n using N.peano_ind. reflexivity.
    destruct n using N.peano_ind. reflexivity.
    lia.
Qed.
