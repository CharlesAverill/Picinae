Require Export Picinae_riscv.
Export RISCVNotations.
Require Export CPUTimingBehavior.
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

Module Type ProgramInformation.
    Parameter entry_addr : addr.
    Parameter exits : trace -> bool.
    (* Binary representation of the program to be decoded *)
    Parameter binary : addr -> N.
End ProgramInformation.

Module RISCVTiming (cpu : CPUTimingBehavior) (prog : ProgramInformation) <: TimingModule IL_RISCV.
    Export cpu prog.

    Definition time_inf : N := 2^32.

    Definition lifted_prog := lift_riscv binary.

  Definition time_of_addr (s : store) (a : addr) : N :=
  let reg s r := if r =? 0 then 0 else s (rv_varid r) in
  let bop s time_inf rs1 rs2 op : N :=
    op (reg s rs1) (reg s rs2) in
  match rv_decode (binary a) with
  (* ==== I ISA Extension ==== *)
  (* ALU *)
  | R5_Add  rd rs1 rs2     => tadd (reg s rs1) (reg s rs2)
  | R5_Addi rd rs1 imm     => taddi (reg s rs1) imm
  | R5_Slt  rd rs1 rs2     => tslt (reg s rs1) (reg s rs2)
  | R5_Slti rd rs1 imm     => tslti (reg s rs1) imm
  | R5_Sltu rd rs1 rs2     => tsltu (reg s rs1) (reg s rs2)
  | R5_Sltiu rd rs1 imm    => tsltiu (reg s rs1) imm
  | R5_Xor  rd rs1 rs2     => txor (reg s rs1) (reg s rs2)
  | R5_Xori rd rs1 imm     => txori (reg s rs1) imm
  | R5_Or   rd rs1 rs2     => tor (reg s rs1) (reg s rs2)
  | R5_Ori  rd rs1 imm     => tori (reg s rs1) imm
  | R5_And  rd rs1 rs2     => tand (reg s rs1) (reg s rs2)
  | R5_Andi rd rs1 imm     => tandi (reg s rs1) imm
  | R5_Sub  rd rs1 rs2     => tsub (reg s rs1) (reg s rs2)
  | R5_Lui  rd imm         => tlui imm
  | R5_Auipc rd imm        => tauipc imm

  (* ALU Shifts *)
  | R5_Sll  rd rs1 rs2     => tsll (reg s rs1) (reg s rs2)
  | R5_Slli rd rs1 shamt   => tslli (reg s rs1) shamt
  | R5_Srl  rd rs1 rs2     => tsrl (reg s rs1) (reg s rs2)
  | R5_Srli rd rs1 shamt   => tsrli (reg s rs1) shamt
  | R5_Sra  rd rs1 rs2     => tsra (reg s rs1) (reg s rs2)
  | R5_Srai rd rs1 shamt   => tsrai (reg s rs1) shamt

  (* Branches *)
  | R5_Beq  rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if x =? y then ttbeq (reg s rs1) (reg s rs2) else tfbeq (reg s rs1) (reg s rs2))
  | R5_Bne  rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if negb (x =? y) then ttbne (reg s rs1) (reg s rs2) else tfbne (reg s rs1) (reg s rs2))
  | R5_Blt  rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if Z.ltb (toZ 32 x) (toZ 32 y) then ttblt (reg s rs1) (reg s rs2) else tfblt (reg s rs1) (reg s rs2))
  | R5_Bge  rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if Z.geb (toZ 32 x) (toZ 32 y) then ttbge (reg s rs1) (reg s rs2) else tfbge (reg s rs1) (reg s rs2))
  | R5_Bltu rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if x <? y then ttbltu (reg s rs1) (reg s rs2) else tfbltu (reg s rs1) (reg s rs2))
  | R5_Bgeu rs1 rs2 off => bop s time_inf rs1 rs2
      (fun x y => if negb (x <? y) then ttbgeu (reg s rs1) (reg s rs2) else tfbgeu (reg s rs1) (reg s rs2))

  (* Jump/call *)
  | R5_Jal  rd off         => tjal (ofZ 32 off)
  | R5_Jalr rd rs1 off     => tjalr (reg s rs1) (ofZ 32 off)

  (* Load/store *)
  | R5_Lb  rd rs1 off      => tlb (reg s rs1) off
  | R5_Lh  rd rs1 off      => tlh (reg s rs1) off
  | R5_Lw  rd rs1 off      => tlw (reg s rs1) off
  | R5_Lbu rd rs1 off      => tlbu (reg s rs1) off
  | R5_Lhu rd rs1 off      => tlhu (reg s rs1) off
  | R5_Sb  rs1 rs2 off     => tsb (reg s rs2) (ofZ 32 off)
  | R5_Sh  rs1 rs2 off     => tsh (reg s rs2) (ofZ 32 off)
  | R5_Sw  rs1 rs2 off     => tsw (reg s rs2) (ofZ 32 off)

  (* Data fence *)
  | R5_Fence _ _           => tfence
  | R5_Fence_i             => tfence

  (* ==== M ISA Extension ==== *)
  | R5_Mul    rd rs1 rs2   => tmul (reg s rs1) (reg s rs2)
  | R5_Mulh   rd rs1 rs2   => tmulh (reg s rs1) (reg s rs2)
  | R5_Mulsu  rd rs1 rs2   => tmulhsu (reg s rs1) (reg s rs2)
  | R5_Mulu   rd rs1 rs2   => tmulhu (reg s rs1) (reg s rs2)

  (* Division *)
  | R5_Div    rd rs1 rs2   => tdiv (reg s rs1) (reg s rs2)
  | R5_Divu   rd rs1 rs2   => tdivu (reg s rs1) (reg s rs2)
  | R5_Rem    rd rs1 rs2   => trem (reg s rs1) (reg s rs2)
  | R5_Remu   rd rs1 rs2   => tremu (reg s rs1) (reg s rs2)

  (* ==== Zbb ISA Extension ==== *)
  | R5_Clz rd rs            => tclz (reg s rs)

  (* ==== Zicsr ISA Extension ==== *)
  | R5_Csrrw  rd rs1 csr   => tcsrrw (reg s rs1) csr
  | R5_Csrrwi rd imm csr   => tcsrrwi imm csr
  | R5_Csrrs  rd rs1 csr   => tcsrrs (reg s rs1) csr
  | R5_Csrrsi rd imm csr   => tcsrrsi imm csr
  | R5_Csrrc  rd rs1 csr   => tcsrrc (reg s rs1) csr
  | R5_Csrrci rd imm csr   => tcsrrci imm csr

  | _ => time_inf
  end.
End RISCVTiming.

(* Instantiate the Timing Automation module with RISC-V values *)
(* Provide CPUTimingBehavior and ProgramInformation *)
Module RISCVTimingAutomation := 
    TimingAutomation IL_RISCV Theory_RISCV Statics_RISCV FInterp_RISCV 
    PSimpl_RISCV_v1_1.
