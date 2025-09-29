Require Export Picinae_riscv.
Export RISCVNotations.
Require Export CPUTimingBehavior ProgramInformation.
Require Export TimingAutomation.
Require Export NArith.
Require Import ZArith.
Require Export Lia.
Require Import List.
Import ListNotations.

Definition lift_riscv (f : addr -> N) (s : store) (a : addr) :=
    Some (4, rv2il a (rv_decode (f a))).

Theorem lift_riscv_welltyped:
    forall p, welltyped_prog rvtypctx (lift_riscv p).
Proof.
    intros s a a0. unfold lift_riscv.
    exists rvtypctx. apply welltyped_rv2il.
Qed.

Module RISCVTiming (cpu : CPUTimingBehavior) (prog : ProgramInformation) <: TimingModule IL_RISCV.
    Export cpu prog.

    Definition time_inf : N := 2^32.

    Definition lifted_prog := lift_riscv binary.

    Definition cache : Type := cpu.cache.
    Definition cache_step := cpu.cache_step.

    Definition time_of_addr (s : store) (c : cache) (a : addr) : N :=
        let bop s time_inf rs1 rs2 op :=
            op (reg s rs1) (reg s rs2) in
        match rv_decode (binary a) with
        (* ==== I ISA Extension ==== *)
        (* ALU *)
        | R5_Add  _ _ _     => tadd
        | R5_Addi _ _ _     => taddi
        | R5_Slt  _ _ _     => tslt
        | R5_Slti _ _ _     => tslti
        | R5_Sltu _ _ _     => tsltu
        | R5_Sltiu _ _ _    => tsltiu
        | R5_Xor  _ _ _     => txor
        | R5_Xori _ _ _     => txori
        | R5_Or   _ _ _     => tor
        | R5_Ori  _ _ _     => tori
        | R5_And  _ _ _     => tand
        | R5_Andi _ _ _     => tandi
        | R5_Sub  _ _ _     => tsub
        | R5_Lui  _ _       => tlui
        | R5_Auipc _ _      => tauipc

        (* ALU Shifts *)
        | R5_Sll  rd _ _ =>
            let rd := reg s rd in 
            tsll rd
        | R5_Slli _ _ shamt => tslli shamt
        | R5_Srl  rd _ _ =>
            let rd := reg s rd in 
            tsrl rd
        | R5_Srli _ _ shamt => tsrli shamt
        | R5_Sra  rd _ _ =>
            let rd := reg s rd in 
            tsra rd
        | R5_Srai _ _ shamt => tsrai shamt

        (* Branches *)
        | R5_Beq rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if x =? y then ttbeq else tfbeq) c 
            (add_signed_offset a off)
        | R5_Bne rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if negb (x =? y) then ttbne else tfbne) c
            (add_signed_offset a off)
        | R5_Blt rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if Z.ltb (toZ 32 x) (toZ 32 y) then ttblt else tfblt) c
            (add_signed_offset a off)
        | R5_Bge rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if Z.geb (toZ 32 x) (toZ 32 y) then ttbge else tfbge) c
            (add_signed_offset a off)
        | R5_Bltu rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if x <? y then ttbltu else tfbltu) c
            (add_signed_offset a off)
        | R5_Bgeu rs1 rs2 off => bop s time_inf rs1 rs2
            (fun x y => if negb (x <? y) then ttbgeu else tfbgeu) c
            (add_signed_offset a off)

        (* Jump/call *)
        | R5_Jal  _ imm       => tjal c (add_signed_offset a imm)
        | R5_Jalr _ rs1 imm     => tjalr c (resolve_jalr_addr imm rs1)

        (* Load/store *)
        | R5_Lb  _ rs imm      => tlb c (add_signed_offset' rs imm)
        | R5_Lh  _ rs imm      => tlh c (add_signed_offset' rs imm)
        | R5_Lw  _ rs imm      => tlw c (add_signed_offset' rs imm)
        | R5_Lbu _ rs imm      => tlbu c (add_signed_offset' rs imm)
        | R5_Lhu _ rs imm      => tlhu c (add_signed_offset' rs imm)
        | R5_Sb  _ rs imm      => tsb c (add_signed_offset rs imm)
        | R5_Sh  _ rs imm      => tsh c (add_signed_offset rs imm)
        | R5_Sw  _ rs imm      => tsw c (add_signed_offset rs imm)

        (* Data fence *)
        | R5_Fence   _ _    => tfence c
        | R5_Fence_i        => tfencei c

        (* M extension *)

        (* ==== M ISA Extension ==== *)
        (* Multiplication *)
        | R5_Mul    _ _ _   => tmul
        | R5_Mulh   _ _ _   => tmulh
        | R5_Mulsu  _ _ _   => tmulhsu
        | R5_Mulu   _ _ _   => tmulhu

        (* Division *)
        | R5_Div    _ _ _   => tdiv
        | R5_Divu   _ _ _   => tdivu
        | R5_Rem    _ _ _   => trem
        | R5_Remu   _ _ _   => tremu

        (* ==== Zbb ISA Extension ==== *)
        | R5_Clz rd _       =>
            let rd := reg s rd in
            tclz rd

        (* ==== Zicsr ISA Extension ==== *)
        | R5_Csrrw _ _ _ =>
            tcsrrw
        | R5_Csrrwi _ _ _ =>
            tcsrrwi
        | R5_Csrrs _ _ _ =>
            tcsrrs
        | R5_Csrrsi _ _ _ =>
            tcsrrsi
        | R5_Csrrc _ _ _ =>
            tcsrrc
        | R5_Csrrci _ _ _ =>
            tcsrrci


        | _ => time_inf
        end.
End RISCVTiming.

(* Instantiate the Timing Automation module with RISC-V values *)
(* Provide CPUTimingBehavior and ProgramInformation *)
Module RISCVTimingAutomation := 
    TimingAutomation IL_RISCV Theory_RISCV Statics_RISCV FInterp_RISCV 
    PSimpl_RISCV_v1_1.
