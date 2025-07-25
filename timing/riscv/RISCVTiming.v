Require Export Picinae_riscv.
Export RISCVNotations.
Require Export CPUTimingBehavior.
Require Export TimingAutomation.
Require Export NArith.
Require Import ZArith.
Require Export Lia.
Require Import List.
Import ListNotations.

Module Type ProgramInformation.
    Parameter entry_addr : addr.
    Parameter exits : trace -> bool.
    (* Binary representation of the program to be decoded *)
    Parameter binary : addr -> N.
End ProgramInformation.

Module RISCVTiming (cpu : CPUTimingBehavior) (prog : ProgramInformation) <: TimingModule IL_RISCV.
    Export cpu prog.

    Definition time_inf : N := 2^32.

    Definition bop (s : store) (rs1 rs2 : N) (op : N -> N -> N) : N :=
        let rs1var := if rs1 =? 0 then Ⓓ0 else s (rv_varid rs1) in
        let rs2var := if rs2 =? 0 then Ⓓ0 else s (rv_varid rs2) in
        match rs1var, rs2var with
        | Ⓓr1, Ⓓr2 => op r1 r2
        | _, _ => time_inf
        end.

    Definition cycles_per_instruction_at_addr (s : store) (a : addr) : N :=
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
        | R5_Sll  _ _ shamt => tsll shamt
        | R5_Slli _ _ shamt => tslli shamt
        | R5_Srl  _ _ shamt => tsrl shamt
        | R5_Srli _ _ shamt => tsrli shamt
        | R5_Sra  _ _ shamt => tsra shamt
        | R5_Srai _ _ shamt => tsrai shamt

        (* Branches *)
        | R5_Beq rs1 rs2 off => bop s rs1 rs2
            (fun x y => if x =? y then ttbeq else tfbeq)
        | R5_Bne rs1 rs2 off => bop s rs1 rs2
            (fun x y => if negb (x =? y) then ttbeq else tfbeq)
        | R5_Blt rs1 rs2 off => bop s rs1 rs2
            (fun x y => if Z.ltb (toZ 32 x) (toZ 32 y) then ttbeq else tfbeq)
        | R5_Bge rs1 rs2 off => bop s rs1 rs2
            (fun x y => if Z.geb (toZ 32 x) (toZ 32 y) then ttbeq else tfbeq)
        | R5_Bltu rs1 rs2 off => bop s rs1 rs2
            (fun x y => if x <? y then ttbeq else tfbeq)
        | R5_Bgeu rs1 rs2 off => bop s rs1 rs2
            (fun x y => if negb (x <? y) then ttbeq else tfbeq)

        (* Jump/call *)
        | R5_Jal  _ _       => tjal
        | R5_Jalr _ _ _     => tjalr

        (* Load/store *)
        | R5_Lb  _ _ _      => tlb
        | R5_Lh  _ _ _      => tlh
        | R5_Lw  _ _ _      => tlw
        | R5_Lbu _ _ _      => tlbu
        | R5_Lhu _ _ _      => tlhu
        | R5_Sb  _ _ _      => tsb
        | R5_Sh  _ _ _      => tsh
        | R5_Sw  _ _ _      => tsw

        (* Data fence *)
        | R5_Fence   _ _    => tfence
        | R5_Fence_i        => tfence

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
        | R5_Clz r1 _       => tclz r1

        | _ => time_inf
        end.
End RISCVTiming.

Definition lift_riscv (f : addr -> N) (s : store) (a : addr) :=
    Some (4, rv2il a (rv_decode (f a))).

Theorem lift_riscv_welltyped:
    forall p, welltyped_prog rvtypctx (lift_riscv p).
Proof.
    intros s a a0. unfold lift_riscv.
    exists rvtypctx. apply welltyped_rv2il.
Qed.

(* Instantiate the Timing Automation module with RISC-V values *)
(* Provide CPUTimingBehavior and ProgramInformation *)
Module RISCVTimingAutomation := 
    TimingAutomation IL_RISCV Statics_RISCV FInterp_RISCV 
    PSimpl_RISCV_v1_1 Theory_RISCV.
