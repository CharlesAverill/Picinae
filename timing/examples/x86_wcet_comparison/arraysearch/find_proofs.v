Require Import find.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module Program_find <: ProgramInformation.
    Definition entry_addr : N := 0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1e | 0x25 => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) :=
        match a with
        | 0x0  => movzx_r32_r16   (* movzx eax, si *)
        | 0x3  => test_r16_r16    (* test si, si *)
        | 0x6  => jz_addr         (* jz 0x1e *)
        | 0x8  => xor_r32_r32     (* xor ecx, ecx *)
        | 0xa  => jmp_addr        (* jmp 0x10 *)
        | 0x10 => add_r64_i       (* add rcx, 1 *)
        | 0x14 => cmp_r32_r32     (* cmp ecx, eax *)
        | 0x16 => jnc_addr        (* jnc 0x1e *)
        | 0x18 => cmp_r64_m64     (* cmp [rdi + rcx*8], rdx *)
        | 0x1c => jnz_addr        (* jnz 0x10 *)
        | 0x1e => ret
        | 0x20 => mov_r32_i     (* mov eax, 0xffffffff *)
        | 0x25 => ret             (* ret *)
        | _    => time_inf
        end.

    Definition lifted_prog := arraysearch_find_amd64.
End Program_find.

Module AMD64Timing := AMD64Timing cpu Program_find.
Module findAuto := AMD64TimingAutomation AMD64Timing.
Import Program_find findAuto.

Definition key_in_array (mem : memory) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓠ[arr + (i << 3)] = key.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint key_in_array_dec (mem : memory) (arr : addr) (key len : N)
        : {key_in_array mem arr key len} + {~ key_in_array mem arr key len}.
    induction len using N_peano_ind_Set.
    - right. intro. destruct H as (idx & Contra & _). lia.
    - destruct IHlen as [IN | NOT_IN].
        -- left. destruct IN as (idx & Lt & Eq). exists idx.
            split. lia. assumption.
        -- destruct (N.eq_dec (mem Ⓠ[arr + (len << 3)]) key).
            + left. exists len. split. lia. assumption.
            + right. intro. destruct H as (idx & Lt & Eq).
                assert (idx = len). {
                destruct (lt_impl_lt_or_eq idx len). lia.
                    subst. reflexivity.
                exfalso. apply NOT_IN. exists idx. now split.
                } subst. contradiction.
Qed.

Definition time_of_find (len : N) (found_idx : option N) (t : trace) :=
    cycle_count_of_trace t <=
        movzx_r32_r16 + test_r16_r16 + jz_addr +
        if len =? 0 then
             mov_r32_i + ret
        else
            xor_r32_r32 + jmp_addr +
            (match found_idx with None => 1 + len | Some idx => idx end) * (
                cmp_r64_m64 + jnz_addr + add_r64_i + cmp_r32_r32 + jnc_addr
            ) + cmp_r64_m64 + jnz_addr + jnc_addr + mov_r32_i + ret.

Definition timing_postcondition (mem : memory) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓠ[arr + (i << 3)] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓠ[arr + (j << 3)] <> key) /\
        time_of_find len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓠ[arr + (i << 3)] = key) /\
        time_of_find len None t).

Definition find_timing_invs (s : store) (base_mem : memory)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (s V_MEM64 = base_mem /\ 
               s R_RDI = arr /\ s R_RSI = len /\ s R_RDX = key /\
               len < 2^16 /\
               cycle_count_of_trace t' = 0)
| 0x18 => Some (
    s R_RDI = arr /\ s R_RSI = len /\ s R_RCX = len /\ s R_RDX = key /\
    s R_RAX < 2^32 /\
    0 < len < 2^16 /\
    (* preservation *)
    (forall i, i < len ->
        (s V_MEM64) Ⓠ[arr + (i << 3)] = base_mem Ⓠ[arr + (i << 3)]) /\
    (* haven't found a match yet *)
    (forall i, i < (s R_RAX) ->
        (s V_MEM64) Ⓠ[arr + (i << 3)] <> key) /\
    (s R_RAX) < len /\
    cycle_count_of_trace t' <=
        movzx_r32_r16 + test_r16_r16 + jz_addr + xor_r32_r32 +
        jmp_addr +
        s R_RAX * (
            cmp_r64_m64 + jnz_addr + add_r64_i + cmp_r32_r32 + jnc_addr
        )
    )
| 0x1e | 0x25 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Theorem find_timing:
  forall s (t : trace) s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (MEM: s V_MEM64 = base_mem)
         (A0: s R_RDI = arr)
         (A1: s R_RSI = len)
         (A2: s R_RDX = key)
         (LEN_RANGE: len < 2^16),
  satisfies_all 
    lifted_prog
    (find_timing_invs s base_mem sp arr key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep x64_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.

    (* 0x101b0 -> 0x101e0 *)
    destruct PRE as (Mem & A0 & A1 & A2 & LEN_VALID & Cycles).
    repeat step.
        replace len with 0 in * by lia. right.
        psimpl. rewrite N.shiftr_0_r. split.
        intro. destruct H, H. lia.
        unfold time_of_find. hammer.

    rewrite N.lxor_nilpotent. repeat rewrite N.shiftr_0_r.
    change (scast _ _ 0) with 0.
    repeat change (0 mod _) with 0. psimpl. rewrite N.eqb_refl.
    repeat split; auto. lia.
        (* preservation *) intros; now rewrite Mem.
        (* key not found yet *) intros; lia.
        (* idx <= len *) lia.
        (* cycles *) hammer.

    destruct PRE as (A0 & A1 & A2 & RDX & RAX & LEN_VALID & Preserved &
        NotFound & A5_LEN & Cycles).
    destruct (key_in_array_dec (s' V_MEM64) arr key len) as [IN | NOT_IN].
    (* There is a matching element in the array *) {
        step. repeat step.
        (* postcondition, match found *)
            left. exists (s' R_RAX). split.
                assumption.
            split.
                rewrite <- Preserved, N.shiftl_mul_pow2.
                apply N.eqb_eq in BC. apply BC.
                assumption.
            split.
                intros. rewrite <- Preserved by lia. now apply NotFound.
            unfold time_of_find.
            hammer. replace (len =? 0) with false by lia. lia.
        (* loop invariant after going around *)
            apply N.ltb_lt in BC0. apply N.eqb_neq in BC.
            repeat split; auto; try lia.
            (* key not found *)
            intros.
                apply lt_impl_lt_or_eq in H. destruct H.
                    subst. now rewrite N.shiftl_mul_pow2.
                    now apply NotFound.
            (* cycles *)
            rewrite (N.mod_small (1 + s' R_RAX)) by lia. hammer.
        (* iterated len times - contradiction *)
        assert (len < 1 + s' R_RAX \/ len = 1 + s' R_RAX) by lia. destruct H.
            lia. subst len. rewrite H in *; clear H.
        exfalso. destruct IN as (idx & IDX_LEN & IN).
        apply (NotFound idx).
        destruct (lt_impl_lt_or_eq _ _ IDX_LEN). subst. 
        rewrite N.shiftl_mul_pow2 in IN. change (2^3) with 8 in IN. lia. assumption.
        assumption.
    }

    (* There is not a matching element in the array *) {
        step.
        repeat step.
        (* contradiction - BC0 says a match has been found *)
            exfalso. apply NOT_IN. exists (s' R_RAX). 
            split. lia.
            apply N.eqb_eq in BC.
            rewrite N.shiftl_mul_pow2. apply BC.
        (* a match has not been found, continue *)
        (* postcondition, match found *)
            apply N.ltb_lt in BC0. apply N.eqb_neq in BC.
            repeat split; auto; try lia.
            (* key not found *)
            intros.
                apply lt_impl_lt_or_eq in H. destruct H.
                    subst. now rewrite N.shiftl_mul_pow2.
                    now apply NotFound.
            (* cycles *)
            hammer.
        (* a match has not been found, break and return *)
        right.
            split. intro. apply NOT_IN. destruct H as (idx & IDX_LEN & IN).
            exists idx. split. assumption. now rewrite Preserved.
            unfold time_of_find.
            hammer.
            replace (len =? 0) with false by lia.
            assert (s' R_RAX <= 1 + len) by lia.
            transitivity (ret + mov_r32_i + jnc_addr + cmp_r32_r32 + add_r64_i + jnz_addr + cmp_r64_m64 + movzx_r32_r16 +
                test_r16_r16 + jz_addr + xor_r32_r32 + jmp_addr +
                s' R_RAX * (cmp_r64_m64 + jnz_addr + add_r64_i + cmp_r32_r32 + jnc_addr)). lia.
            rewrite N.mul_add_distr_r. psimpl.
            assert (s' R_RAX < 1 + len \/ s' R_RAX = 1 + len) by lia. destruct H0.
                destruct (lt_impl_lt_or_eq _ _ H0). lia.
            etransitivity.
                apply N.add_le_mono_l.
                apply N.mul_le_mono_r. instantiate (1 := len). lia. lia.
            rewrite H0 in *; clear H0. lia.
    }
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_find := TimingProof i5_7300u.
Import i5_7300u.

Goal forall len found_idx t,
    i5_7300u_find.time_of_find len found_idx t =
    (i5_7300u_find.findAuto.cycle_count_of_trace t <=
        (if len =? 0
            then 39
            else 76 + match found_idx with
                        | Some idx => idx
                        | None => 1 + len
                        end * 28)).
    intros.
    unfold i5_7300u_find.time_of_find.
    unfold cmp_r64_m64, jnz_addr, jnc_addr, mov_r32_i, ret.
    simpl. psimpl.
    reflexivity.
Qed.

