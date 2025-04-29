Require Import Picinae_core.
Require Export Picinae_riscv.
Require Export NArith.
Require Export ZArith.
Require Import Lia.
Require Import List.
Import ListNotations.

(* Hours spent trying to write dependent-typing automation for no reason: 4 *)

Module riscvTiming.
    Definition store := store.
    Definition stmt := stmt.
    Definition empty_store : store := fun _ => 0.
End riscvTiming.
Export riscvTiming.

Open Scope N_scope.
Notation "x #<< y" := (N.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
Notation "x #>> y" := (N.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
Notation "x #& y" := (N.land x y) (at level 25, left associativity). (* logical and *)
Notation "x #^ y" := (N.lxor x y) (at level 25, left associativity). (* logical xor *)
Notation "x #| y" := (N.lor x y) (at level 25, left associativity). (* logical or *)

(* mask_bit_section 0bKJIHGFEDCBA 3 7 := 0bHGFED *)
Definition mask_bit_section (n low high : N) : N :=
    (n #>> low) #& (N.pow 2 (1 + high - low) - 1).

Fixpoint contains (l:list N) (a:N) : bool :=
    match l with
      | nil => false
      | b :: m => orb (b =? a) (contains m a)
    end.

(* https://www.cs.sfu.ca/~ashriram/Courses/CS295/assets/notebooks/RISCV/RISCV_CARD.pdf *)
(* 
     31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 09 08 07 06 05 04 03 02 01 00
    +------------------------------------------------------------------------------------------------+
    | funct7             | rs2          | rs1          | funct3 | rd           | opcode              | R-type
    | imm[11:0]                         | rs1          | funct3 | rd           | opcode              | I-type
    | imm[11:5]          | rs2          | rs1          | funct3 | imm[4:0]     | opcode              | S-type
    | imm[12|10:5]       | rs2          | rs1          | funct3 | imm[4:1|11]  | opcode              | B-type
    | imm[31:12]                                                | rd           | opcode              | U-type
    | imm[20|10:1|11|19:12]                                     | rd           | opcode              | J-type
    +------------------------------------------------------------------------------------------------+
*)

Definition decompose_Rtype (instr : N) : N * N * N * N * N * N :=
    (
        mask_bit_section instr 25 31 (* funct7*),
        mask_bit_section instr 20 24 (* rs2 *),
        mask_bit_section instr 15 19 (* rs1 *),
        mask_bit_section instr 12 14 (* funct3 *),
        mask_bit_section instr 7 11 (* rd *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition decompose_Itype (instr : N) : N * N * N * N * N :=
    (
        mask_bit_section instr 20 31 (* imm *),
        mask_bit_section instr 15 19 (* rs1 *),
        mask_bit_section instr 12 14 (* funct3 *),
        mask_bit_section instr 7 11 (* rd *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition shamt_Itype (imm : N) : N :=
    mask_bit_section imm 0 4.

Definition decompose_Stype (instr : N) : N * N * N * N * N * N :=
    (
        mask_bit_section instr 25 31 (* imm[11:5] *),
        mask_bit_section instr 20 24 (* rs2 *),
        mask_bit_section instr 15 19 (* rs1 *),
        mask_bit_section instr 12 14 (* funct3 *),
        mask_bit_section instr 7 11 (* imm[4:0] *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition imm_Stype (imm_11_5 imm_4_0 : N) : N :=
    (imm_11_5 #<< 4) #| imm_4_0.

Definition decompose_Btype (instr : N) : N * N * N * N * N * N :=
    (
        mask_bit_section instr 25 31 (* imm[12|10:5] *),
        mask_bit_section instr 20 24 (* rs2 *),
        mask_bit_section instr 15 19 (* rs1*),
        mask_bit_section instr 12 14 (* funct3 *),
        mask_bit_section instr 7 11 (* imm[4:1|11] *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition imm_Btype (imm_12_10_5 imm_4_1_11 : N) : N :=
    let '(imm_4_1, imm_11, imm_10_5, imm_12) := (
        mask_bit_section imm_4_1_11 1 4, 
        mask_bit_section imm_4_1_11 0 1, 
        mask_bit_section imm_12_10_5 0 5, 
        mask_bit_section imm_12_10_5 6 7) in
    (imm_12 #<< 11) #| (imm_11 #<< 10) #| (imm_10_5 #<< 4) #| imm_4_1.

Definition decompose_Utype (instr : N) : N * N * N :=
    (
        mask_bit_section instr 12 31 (* imm[31:12] *),
        mask_bit_section instr 7 11 (* rd *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition imm_Utype (imm : N) : N :=
    imm #<< 12.

Definition decompose_Jtype (instr : N) : N * N * N :=
    (
        mask_bit_section instr 12 31 (* imm[20|10:1|11|19:12] *),
        mask_bit_section instr 7 11 (* rd *),
        mask_bit_section instr 0 6 (* opcode *)
    ).

Definition imm_Jtype (imm : N) :=
    let '(imm_20, imm_10_1, imm_11, imm_19_12) := (
        mask_bit_section imm 19 20,
        mask_bit_section imm 10 19,
        mask_bit_section imm 8 9,
        mask_bit_section imm 0 7
    ) in
    (imm_20 #<< 19) #| (imm_19_12 #<< 11) #| (imm_11 #<< 10) #| (imm_10_1 #<< 1).

Definition decompose_CRtype (instr : N) : N * N * N * N :=
    (
        mask_bit_section instr 12 15 (* funct4 *),
        mask_bit_section instr 7 11 (* rd/rs1 *),
        mask_bit_section instr 2 6 (* rs2 *),
        mask_bit_section instr 0 1 (* op *)
    ).

Definition decompose_CItype (instr : N) : N * N * N * N * N :=
    (
        mask_bit_section instr 13 15 (* funct3 *),
        mask_bit_section instr 12 13 (* imm *),
        mask_bit_section instr 7 11 (* rd/rs1 *),
        mask_bit_section instr 2 6 (* imm *),
        mask_bit_section instr 0 1 (* opp *)
    ).

(* https://en.wikichip.org/wiki/risc-v/registers *)
(* Nvmd just use rv_varid *)
Definition riscvvar_of_Z (reg : N) : option var :=
    match reg with
    | 0x1  => Some R_RA
    | 0x2  => Some R_SP
    | 0x3  => Some R_GP
    | 0x4  => Some R_TP
    | 0x5  => Some R_T0
    | 0x6  => Some R_T1
    | 0x7  => Some R_T2
    | 0x8  => Some R_S0
    | 0x9  => Some R_S1
    | 0x10 => Some R_A0
    | 0x11 => Some R_A1
    | 0x12 => Some R_A2
    | 0x13 => Some R_A3
    | 0x14 => Some R_A4
    | 0x15 => Some R_A5
    | 0x16 => Some R_A6
    | 0x17 => Some R_A7
    | 0x18 => Some R_S2
    | 0x19 => Some R_S3
    | 0x20 => Some R_S4
    | 0x21 => Some R_S5
    | 0x22 => Some R_S6
    | 0x23 => Some R_S7
    | 0x24 => Some R_S8
    | 0x25 => Some R_S9
    | 0x26 => Some R_S10
    | 0x27 => Some R_S11
    | 0x28 => Some R_T3
    | 0x29 => Some R_T4
    | 0x30 => Some R_T5
    | 0x31 => Some R_T6
    | _ => None
    end.

Definition riscv_opcode (instr : N) : N :=
    (* mask_bit_section instr 0 6. *)
    instr #& 127.

(* Necessary for max bound computations with register inputs *)
Definition max32 : N := N.pow 2 32 - 1.

(* https://cdn.hackaday.io/files/1741677451560928/NEORV32.pdf Chapter 3.8 Instruction Timing *)
(* Returning N because upper bounds get really big, nat will make compiler hang *)
(*
    Inputs:
    - ML : Memory Latency of CPU
    - s : store representing CPU state
    - instr : instruction to decode and compute cycles for
*)

Definition neorv32_cycles_upper_bound (ML : N) (s : store) (instr : N) : option N :=
    (* This is if/else instead of match, because matching on an N will expand its binary repr,
       which clogs up the goal space a bunch *)
    (* Same with `contains` usage *)
    (* addi slti sltiu xori ori andi add sub slt sltu xor or and lui auipc : 2 *)
    let op := riscv_opcode instr in
    if op =? 51 then (* 0110011 : R-type *)
        let '(funct7, rs2, rs1, funct3, rd, opcode) := decompose_Rtype instr in
        if contains [0;2;3;4;6;7] funct3 then
            (* add sub xor or and slt sltu *)
            Some 2%N
        else
            (* sll srl sra : [ 3 + shamt/4 + shamt%4 ]*)
            (* shamt := rs2 *)
            (* Constant shift times are possible with FAST_SHIFT_EN or TINY_SHIFT_EN enabled *)
            Some (3 + ((s (rv_varid rs2)) / 4) + ((s (rv_varid rs2)) mod 4))%N
    else if op =? 19 then (* 0010011 : I-type *)
        let '(imm, rs1, funct3, rd, opcode) := decompose_Itype instr in
        (* Could also be clz - R-type *)
        let '(funct7, _, _, _, _, _) := decompose_Rtype instr in
        if contains [0;2;3;4;6;7] funct3 then
            (* addi xori ori andi slti sltiu *)
            Some 2%N
        else
            (* clz *)
            (* NOTE : There is a super cool reason why CLZ and the below
                shift instructions don't collide. They are I-type, which
                would imply that they have a user-provided immediate on
                the high bits of the instruction. Could this contain the
                funct7 of CLZ, causing a parsing collision? No! These shift
                instructions can only take five bits for their shamts, 
                and the highest bits (colliding with CLZ) are forced to be
                specific values that don't clash. Radical!
            *)
            if andb (funct3 =? 1) (funct7 =? 48) then
                let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
                Some (3 + clz r1 32)%N
            else
                (* slli srli srai : [ 3 + shamt/4 + shamt%4 ] *)
                (* shamt := imm[0:4] *)
                (* Constant shift times are possible with FAST_SHIFT_EN or TINY_SHIFT_EN enabled *)
                let shamt := shamt_Itype imm in
                Some (3 + (shamt / 4) + (shamt mod 4))%N
    else if op =? 3 then (* 0000011 : I-type *)
        let '(imm, rs1, funct3, rd, opcode) := decompose_Itype instr in
        (* lb lh lw lbu lhu : [ 5 + (ML - 2) ] *)
        Some (5 + (ML - 2))%N
    else if op =? 35 then (* 0100011 : S-type *)
        let '(imm_11_5, rs2, rs1, funct3, imm_4_0, opcode) := decompose_Stype instr in
        (* sb sh sw : [ 5 + (ML - 2) ] *)
        Some (5 + (ML - 2))%N
    else if op =? 99 then (* 1100011 : B-type *)
        let '(imm_12_10_5, rs2, rs1, funct3, imm_4_1_11, opcode) := decompose_Btype instr in
        (* beq bne blt bge bltu bgeu : if taken then [ 5 + (ML - 1) ] else [ 3 ] *)
        if funct3 =? 0x0 then (* beq *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if r1 =? r2 then
                    5 + (ML - 1)
                else
                    3)
        else if funct3 =? 0x1 then (* bne *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if negb (r1 =? r2) then
                    5 + (ML - 1)
                else
                    3)
        else if funct3 =? 0x4 then (* blt *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if Z.ltb (toZ 32 r1) (toZ 32 r2) then
                    5 + (ML - 1)
                else
                    3)
        else if funct3 =? 0x5 then (* bge *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if Z.geb (toZ 32 r1) (toZ 32 r2) then
                    5 + (ML - 1)
                else
                    3)
        else if funct3 =? 0x6 then (* bltu *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if r1 <? r2 then
                    5 + (ML - 1)
                else
                    3)
        else if funct3 =? 0x7 then (* bgeu *)
            let r1 := if rs1 =? 0 then 0 else s (rv_varid rs1) in
            let r2 := if rs2 =? 0 then 0 else s (rv_varid rs2) in
                Some (if negb (r1 <? r2)%N then
                    5 + (ML - 1)
                else
                    3)
        else None
    else if op =? 111 then (* 1101111 : J-type *)
        let '(immJ, rd, opcode) := decompose_Jtype instr in
        (* jal : [ 5 + (ML - 1) ] *)
        Some (5 + (ML - 1))%N
    else if op =? 103 then (* 1100111 : I-type *)
        let '(imm, rs1, funct3, rd, opcode) := decompose_Itype instr in
        (* jalr : [ 5 + (ML - 1) ] *)
        Some (5 + (ML - 1))%N
    else if orb (op =? 55) (op =? 23) then (* 0110111 : U-type *) (* 0010111 : U-type *) Some 2%N
    else if op =? 115 then (* 1110011 : I-type *) Some 3%N
    (* TODO : Handle RISC-V Extensions *)
    else if op =? 51 then (* 0110011 : R-type - RV32M Extension*)
        Some 36%N
    else None.

(* Machinery to automate lifting - TODO replace with existing stuff *)
Definition range (start stop : N) : list N :=
    let fix aux (n : nat) :=
        match n with
        | O => []
        | S n' => n :: aux n'
        end
    in List.rev (List.map (fun n => start + 4 * N.of_nat (n - 1)) (aux (N.to_nat (1 + (stop - start) / 4)))).

Definition rv_stmt' m a :=
    (* removed getmem here. why was it giving nops? *)
    rv2il a match a mod 4 with 0 => rv_decode (m a) | _ => R5_InvalidI end.

Definition il_list (prog : store -> addr -> N) (prog_start prog_end : N) :=
    List.map (fun a => (a, Some (4, rv_stmt' (prog (fun _ => 0)) a))) (range prog_start prog_end).

Definition update_prog old_prog (a : addr) newval : program :=
    fun s a' => if N.eqb a a' then newval else old_prog s a'.

Fixpoint program_of_list l :=
        match l with 
        | nil => fun _ _ => None    
        | h :: t => update_prog (program_of_list t) (fst h) (snd h)
        end.

Definition lift_via_list (f : store -> addr -> N) (prog_start prog_end : N) : program :=
    program_of_list (il_list f prog_start prog_end).

Definition lift_riscv (f : addr -> N) (s : store) (a : addr) :=
    Some (4, rv2il a (rv_decode (f a))).

Theorem lift_riscv_welltyped:
    forall p, welltyped_prog rvtypctx (lift_riscv p).
Proof.
    intros s a a0. unfold lift_riscv.
    exists rvtypctx. apply welltyped_rv2il.
Qed.

(* Timing machinery *)
Definition cycle_count_of_trace (time_of_addr : store -> addr -> N) (t : trace) : N :=
    List.fold_left N.add (List.map 
        (fun '(e, s) => match e with 
            | Addr a => time_of_addr s a
            | Raise n => max32
            end) t) 0.

Lemma fold_left_cons : forall {X : Type} (t : list X) (h : X) (f : X -> X -> X) (base : X) 
    (Comm : forall a b, f a b = f b a) (Assoc : forall a b c, f a (f b c) = f (f a b) c),
    List.fold_left f (h :: t) base = f h (List.fold_left f t base).
Proof.
    induction t; intros.
    - simpl. now rewrite Comm.
    - simpl in *. rewrite IHt, IHt, IHt,
        Assoc, Assoc, (Comm a h); auto.
Qed.

Lemma cycle_count_of_trace_single :
    forall (e : exit) (s : store) time_of_addr,
    cycle_count_of_trace time_of_addr [(e, s)] = 
        match e with 
        | Addr a => time_of_addr s a
        | Raise n => max32
        end.
Proof. reflexivity. Qed.

Lemma cycle_count_of_trace_cons :
    forall (t : trace) (e : exit) (s : store) time_of_addr,
    cycle_count_of_trace time_of_addr ((e, s) :: t) = cycle_count_of_trace time_of_addr [(e, s)] + cycle_count_of_trace time_of_addr t.
Proof.
    intros. unfold cycle_count_of_trace at 2. rewrite map_cons, fold_left_cons; try lia. simpl.
    unfold cycle_count_of_trace at 1. rewrite map_cons, fold_left_cons. rewrite N.add_0_r. reflexivity.
    lia. lia.
Qed.

Lemma fold_left_add_extract_base : forall l x,
    fold_left N.add l x = x + fold_left N.add l 0.
Proof.
    induction l; simpl; intros. lia.
    rewrite IHl, IHl with (x := a). lia.
Qed.

Lemma fold_left_add_nest : forall l1 l2 x,
    fold_left N.add l1 (fold_left N.add l2 x) = 
        x + (fold_left N.add l1 0) + (fold_left N.add l2 0).
Proof.
    induction l1.
    - induction l2; intros; simpl in *. lia.
      rewrite IHl2, (fold_left_add_extract_base _ a). lia.
    - induction l2; intros; simpl in *.
      rewrite fold_left_add_extract_base, (fold_left_add_extract_base _ a). 
        lia.
      rewrite fold_left_add_extract_base, fold_left_add_extract_base,
        (fold_left_add_extract_base _ a), (fold_left_add_extract_base _ a0).
      lia.
Qed.

Lemma cycle_count_of_trace_app :
    forall (t1 t2 : trace) (e : exit) (s : store) time_of_addr,
    cycle_count_of_trace time_of_addr (t1 ++ t2) = cycle_count_of_trace time_of_addr t1 + cycle_count_of_trace time_of_addr t2.
Proof.
    intros. unfold cycle_count_of_trace at 1.
    rewrite map_app, fold_left_app, fold_left_add_nest. simpl. 
    unfold cycle_count_of_trace. rewrite N.add_comm. reflexivity.
Qed.
