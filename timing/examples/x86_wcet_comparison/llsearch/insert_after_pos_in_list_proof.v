Require Import insert_after_pos_in_list_lifted.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module p <: LinkedListParams.
  Definition w := 64.
  Definition e := LittleE.
  Definition dw := 8.
  Definition pw := 8.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_amd64.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Module Program_insert_in_sorted_list <: ProgramInformation.
    Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x3d | 0x4f => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
        (* 0x001012c0: TEST RDI,RDI *)
        | 0x0 => test_r64_r64
        (* 0x001012c3: JZ 0x001012fb *)
        | 0x3 => jz_addr
        (* 0x001012c5: TEST RSI,RSI *)
        | 0x5 => test_r64_r64
        (* 0x001012c8: JZ 0x001012fb *)
        | 0x8 => jz_addr
        (* 0x001012ca: XOR EAX,EAX *)
        | 0xa => xor_r32_r32
        (* 0x001012cc: TEST RDX,RDX *)
        | 0xc => test_r64_r64
        (* 0x001012ce: JNZ 0x001012e7 *)
        | 0xf => jnz_addr
        (* 0x001012d0: JMP 0x00101300 *)
        | 0x11 => jmp_addr
        (* 0x001012e0: ADD RAX,0x1 *)
        | 0x20 => add_r64_i
        (* 0x001012e3: CMP RDX,RAX *)
        | 0x24 => cmp_r64_r64
        (* 0x001012e5: JZ 0x00101300 *)
        | 0x27 => jz_addr
        (* 0x001012e7: MOV RCX,RDI *)
        | 0x29 => mov_r64_r64
        (* 0x001012ea: MOV RDI,qword ptr [RDI + 0x8] *)
        | 0x2c => mov_r64_m64
        (* 0x001012ee: TEST RDI,RDI *)
        | 0x30 => test_r64_r64
        (* 0x001012f1: JNZ 0x001012e0 *)
        | 0x33 => jnz_addr
        (* 0x001012f3: MOV qword ptr [RSI + 0x8],RDI *)
        | 0x35 => mov_m64_r64
        (* 0x001012f7: MOV qword ptr [RCX + 0x8],RSI *)
        | 0x39 => mov_m64_r64
        (* 0x001012fb: RET *)
        | 0x3d => ret
        (* 0x00101300: MOV RCX,RDI *)
        | 0x40 => mov_r64_r64
        (* 0x00101303: MOV RDI,qword ptr [RDI + 0x8] *)
        | 0x43 => mov_r64_m64
        (* 0x00101307: MOV qword ptr [RSI + 0x8],RDI *)
        | 0x47 => mov_m64_r64
        (* 0x0010130b: MOV qword ptr [RCX + 0x8],RSI *)
        | 0x4b => mov_m64_r64
        (* 0x0010130f: RET *)
        | 0x4f => ret
        | _ => time_inf
        end.

    Definition lifted_prog := linked_list_insert_after_pos_in_list_amd64.
End Program_insert_in_sorted_list.

Module AMD64Timing := AMD64Timing cpu Program_insert_in_sorted_list.
Module insert_in_sorted_listAuto := AMD64TimingAutomation AMD64Timing.
Import Program_insert_in_sorted_list insert_in_sorted_listAuto.

Definition optN_eqb (x y : option N) : bool :=
    match x, y with
    | Some x, Some y => N.eqb x y
    | _, _ => false
    end.

Definition time_of_insert_in_sorted_list 
    (base_mem : memory) (l value : addr) (pos : N) (len : nat) (t : trace) :=
  cycle_count_of_trace t <=
    test_r64_r64 + jz_addr +
    if (l =? NULL) then ret else (
        test_r64_r64 + jz_addr +
        if (value =? NULL) then ret else (
            xor_r32_r32 + test_r64_r64 + jnz_addr +
            if (pos =? 0) then (
                jmp_addr + mov_r64_r64 + mov_r64_m64 + mov_m64_r64 +
                mov_m64_r64 + ret
            ) else (
                mov_r64_r64 + mov_r64_m64 + test_r64_r64 +
                (* if (optN_eqb (list_node_next base_mem l) (Some NULL)) then (
                    jnz_addr + mov_m64_r64 + mov_m64_r64 + ret
                ) else (
                    
                ) *)
                 (1 + N.min pos (N.of_nat len)) * (
                        jnz_addr + add_r64_i + cmp_r64_r64 + jz_addr +
                        mov_r64_r64 + mov_r64_m64 + test_r64_r64
                    ) +
                    mov_m64_r64 + mov_m64_r64 + ret
            )
        )
    ).

Definition insert_in_sorted_list_timing_invs 
    (l value : addr) (pos : N) (len : nat) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
        s R_RDI = l /\ s R_RSI = value /\ s R_RDX = pos /\
        s V_MEM64 = base_mem /\
        node_distance (s V_MEM64) l NULL len /\
        cycle_count_of_trace t' = 0
    )
| 0x33 => Some (
        s R_RDX = pos /\
        s R_RAX < pos /\
        s R_RAX < N.of_nat len /\
        s R_ZF = (if s R_RDI =? 0 then 1 else 0) /\
        node_distance (s V_MEM64) l (s R_RDI) (N.to_nat (1 + s R_RAX)) /\
        node_distance (s V_MEM64) l NULL len /\
        (l =? NULL) = false /\
        (value =? NULL) = false /\
        (pos =? 0) = false /\
        (* optN_eqb (list_node_next base_mem l) (Some NULL) = false /\ *)
        cycle_count_of_trace t' <=
            test_r64_r64 + jz_addr +
            test_r64_r64 + jz_addr +
            xor_r32_r32 + test_r64_r64 + jnz_addr +
            mov_r64_r64 + mov_r64_m64 + test_r64_r64 +
            (s R_RAX) * (
                jnz_addr + add_r64_i + cmp_r64_r64 + jz_addr +
                mov_r64_r64 + mov_r64_m64 + test_r64_r64
            )
    )
| 0x3d | 0x4f => Some (
    time_of_insert_in_sorted_list base_mem l value pos len t
)
| _ => None end | _ => None end.

Theorem insert_in_sorted_list_timing:
  forall s t s' x' l value pos len base_mem
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (RDI: s R_RDI = l)
         (RSI: s R_RSI = value)
         (RDX: s R_RDX = pos)
         (MEM: s V_MEM64 = base_mem)
         (LEN: node_distance base_mem l NULL len),
  satisfies_all
    lifted_prog
    (insert_in_sorted_list_timing_invs l value pos len base_mem)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep x64_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto. rewrite MEM. assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.

    - destruct PRE as (RDI & RSI & RDX & MEM & Len & Cycles).
        repeat step. unfold NULL. hammer.
        unfold NULL. hammer. unfold NULL. hammer.
        split. reflexivity.
        split. rewrite N.lxor_nilpotent. lia.
        split. rewrite N.lxor_nilpotent.
            change (scast _ _ _ mod _) with 0.
            pose proof (node_distance_len_nonzero _ _ _ Len).
            rewrite Bool.negb_true_iff in H. specialize (H BC). lia.
        split. reflexivity.
        split. rewrite N.lxor_nilpotent.
            change (1 + scast 32 64 0 mod 2^32) with 1.
            change (N.to_nat 1) with 1%nat.
            apply node_distance_next_S_len with (dst := l).
                destruct l. discriminate. reflexivity.
                eapply distance_null_imp_well_formed.
                    rewrite <- MEM. eassumption. apply Dst0.
        split. rewrite <- MEM. assumption.
        repeat split; auto.
        rewrite N.lxor_nilpotent.
        hammer.
    - destruct PRE as (RDX & RAX & RAX_LEN & ZF &
            DstCurr & Len & BC0 & BC1 & BC2 & Cycles).
        repeat step.
            apply N.eqb_eq in BC. rewrite BC in *.
            pose proof (node_distance_uniq DstCurr Len).
            hammer.
        hammer.
            etransitivity. apply N.add_le_mono_l. eassumption.
            assert (s' R_RAX < N.min pos (N.of_nat len)) by lia.
            etransitivity. apply N.add_le_mono_l, N.add_le_mono_l.
            apply N.mul_le_mono_r, N.lt_le_incl, H. lia.
        hammer.
            assert (pos < 2^64). rewrite <- RDX.
                apply (models_var R_RDX MDL).
            assert (1 ⊕ s' R_RAX = 1 + s' R_RAX).
              rewrite (N.mod_small (1 + s' R_RAX)) by lia. reflexivity.
            repeat (reflexivity || assumption || lia || split).
        rewrite (N.mod_small (1 + s' R_RAX)) by lia.
        rewrite msub_nowrap in BC3 by lia.
        repeat rewrite N.mod_small in BC3 by lia.
        repeat split; auto; try lia.
        destruct (N.eq_dec (N.of_nat len) (1 + s' R_RAX)); [| lia].
            replace len with (N.to_nat (1 + s' R_RAX)) in Len by lia.
            pose proof (node_distance_uniq' DstCurr Len eq_refl).
            rewrite H1 in BC. discriminate.
        rewrite H0 in *.
        psimpl.
            replace (N.to_nat (2 + s' R_RAX)) with (S (N.to_nat (1 + s' R_RAX))) by lia.
            eapply node_distance_next_S_len; cycle 2.
                eassumption.
                destruct (s' R_RDI). discriminate. reflexivity.
                eapply distance_null_imp_well_formed. eassumption.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_insert_in_sorted_list := TimingProof i5_7300u.

Goal forall (base_mem : memory) (l value : addr) (pos : N) (len : nat) (t : trace),
    i5_7300u_insert_in_sorted_list.time_of_insert_in_sorted_list base_mem l value pos len t =
    (i5_7300u_insert_in_sorted_list.insert_in_sorted_listAuto.cycle_count_of_trace t <=
    if l =? 0
        then 37
        else
        22 +
        (if value =? 0
            then 26
            else
            if pos =? 0
            then 1052
            else 1043 + (1 + N.min pos (N.of_nat len)) * 1023)).
    intros.
    unfold i5_7300u_insert_in_sorted_list.time_of_insert_in_sorted_list. simpl.
    unfold i5_7300u.ret, i5_7300u.mov_m64_r64.
    psimpl. reflexivity.
Qed.
