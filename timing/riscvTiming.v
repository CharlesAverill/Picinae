Require Import Picinae_core.
Require Export Picinae_timing.
Require Export Picinae_riscv.
Require Export NArith.
Require Export ZArith.

Require Import List.
Import ListNotations.

Module riscvTiming.
    Definition store := store.
    Definition stmt := stmt.
    Definition empty_store : store := fun _ => VaN 0 32.
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

(* Hours spent trying to write dependent-typing automation for no reason: 4 *)
(* Definition n_tuple (n : nat) (T : Type) : Type :=
    let fix aux x := match x with O => T | S n' => (T * aux n')%type end in
    aux n.

Lemma pred_n_tuple : forall n T, (1 <= n)%nat -> (T * n_tuple (n - 1) T)%type = n_tuple n T.
Proof.
    induction n; intros; simpl.
    - inversion H.
    - rewrite Nat.sub_0_r. reflexivity.  
Qed. 

Fixpoint pred_tuple {X : Type} {n : nat} (tup : n_tuple n X) {struct n} : n_tuple (n - 1) X.
    destruct n.
    - exact tup.
    - destruct n.
        -- destruct tup. exact x.
        -- destruct tup, n0. specialize (pred_tuple _ _ n0).
            remember (x, (x0, pred_tuple)). rewrite <- pred_n_tuple.
             simpl. rewrite <- pred_n_tuple. exact p.
            

Fixpoint decompose32 (instr low : N) (boundaries : list N) : n_tuple (length boundaries) N.
    destruct boundaries eqn:E.
    - exact (mask_bit_section instr low 31).
    - simpl. exact (mask_bit_section instr low z, decompose32 instr (1 + z) l).
Defined.

Compute decompose32 2147483647 0 [6; 31].

Fixpoint decompose_list (instr low : N) (boundaries : list N) : n_tuple (length boundaries) N :=
    match boundaries with
    | nil => mask_bit_section instr low 
    | high :: tl => (mask_bit_section instr low high, decompose_list instr (1 + high) tl)
    end.

Lemma decompose_len_eq : forall b i l, length (decompose_list i l b) = length b.
Proof.
    induction b; intros.
    - reflexivity.
    - simpl (length (a :: b)). rewrite <- (IHb i l). remember (length (decompose_list i l b)) as x.
      cbv [decompose_list]. fold decompose_list. destruct (_ :: _) eqn:E. inversion E. simpl.
      subst. inversion E. now rewrite IHb, IHb.
Qed.

Fixpoint decompose (instr low : N) (boundaries : list N) : n_tuple (length boundaries) N.
    destruct (decompose_list instr low boundaries) eqn:E.
    - rewrite <- (decompose_len_eq boundaries instr low), E. exact instr.
    - destruct l;
        rewrite <- (decompose_len_eq boundaries instr low), E.
        -- exact instr.
        -- simpl. exact (z, (z0, decompose instr (low + 1)))  

Compute mask_bit_section 63 3 4.
Compute decompose 63 0 [2; 6]. *)

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
    mask_bit_section instr 0 6.

(* Necessary for max bound computations with register inputs *)
Definition max32 : N := N.pow 2 32 - 1.

(* https://cdn.hackaday.io/files/1741677451560928/NEORV32.pdf Chapter 3.8 Instruction Timing *)
(* Returning N because upper bounds get really big, nat will make compiler hang *)
(*
    Inputs:
    - ML : Memory Latency of CPU
    - prog : list of instructions comprising program
    - s : store representing CPU state
    - addr : index into prog to decode
*)
Definition neorv32_cycles_upper_bound (ML : N) (s : store) (instr : N) : option N :=
    let reg_or_max (reg : N) : N := 
        match s (rv_varid reg) with
        | VaN x _ => x
        | VaM _ _ => max32
        end
    in
    (* This is if/else instead of match, because matching on an N will expand its binary repr,
       which clogs up the goal space a bunch *)
    (* addi slti sltiu xori ori andi add sub slt sltu xor or and lui auipc : 2 *)
    let op := riscv_opcode instr in
    if op =? 51 then (* 0110011 : R-type *)
        let '(funct7, rs2, rs1, funct3, rd, opcode) := decompose_Rtype instr in
        match funct3 with
        | 0 | 2 | 3 | 4 | 6 | 7 =>
            (* add sub xor or and slt sltu *)
            Some 2%N
        | _ => 
            (* sll srl sra : [ 3 + shamt/4 + shamt%4 ]*)
            (* shamt := rs2 *)
            (* Constant shift times are possible with FAST_SHIFT_EN or TINY_SHIFT_EN enabled *)
            Some (3 + (reg_or_max rs2 / 4) + ((reg_or_max rs2) mod 4))%N
        end
    else if op =? 19 then (* 0010011 : I-type *)
        let '(imm, rs1, funct3, rd, opcode) := decompose_Itype instr in
        match funct3 with
        | 0 | 2 | 3 | 4 | 6 | 7 =>
            (* addi xori ori andi slti sltiu *)
            Some 2%N
        | _ => 
            (* slli srli srai : [ 3 + shamt/4 + shamt%4 ] *)
            (* shamt := imm[0:4] *)
            (* Constant shift times are possible with FAST_SHIFT_EN or TINY_SHIFT_EN enabled *)
            let shamt := shamt_Itype imm in
            Some (3 + (shamt / 4) + (shamt mod 4))%N
        end
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
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if r1 =? r2 then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
        else if funct3 =? 0x1 then (* bne *)
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if negb (r1 =? r2) then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
        else if funct3 =? 0x4 then (* blt *)
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if Z.ltb (toZ 32 r1) (toZ 32 r2) then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
        else if funct3 =? 0x5 then (* bge *)
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if Z.geb (toZ 32 r1) (toZ 32 r2) then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
        else if funct3 =? 0x6 then (* bltu *)
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if r1 <? r2 then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
        else if funct3 =? 0x7 then (* bgeu *)
            match s (rv_varid rs1), s (rv_varid rs2) with
            | VaN r1 _, VaN r2 _ => Some
                (if negb (r1 <? r2)%N then
                    5 + (ML - 1)
                else
                    3)
            | _, _ => None
            end
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
    else None.

Definition add_loop_riscv_offset := 0xc.
Definition add_loop_riscv : list N := [
    0x00028863          	(* beqz	t0,1c <end> *);
    0x00130313          	(* addi	t1,t1,1 *);
    0x407282b3          	(* sub	t0,t0,t2 *);
    0xfe000ae3          	(* beqz	zero,c <add> *)
].
