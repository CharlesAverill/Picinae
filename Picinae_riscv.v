(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2025 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Instantiation of Picinae for RISC-V ISA.            MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_statics                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_finterp                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_simplifier_*                                     MDMMMMMMMO.7MDM7M+
   * Picinae_ISA                                               ZMMMMMMMM.$MM8$MN
   Then compile this module with menu option                   $ZMMMMMMZ..MMMOMZ
   Compile->Compile_buffer.                                     ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from RISC-V native code: *)
Inductive riscvvar :=
  (* Main memory: *)
  | V_MEM32
  (* Return address, stack pointer, global poniter, thread pointer *)
  | R_RA | R_SP | R_GP | R_TP
  (* Temporary registers *)
  | R_T0 | R_T1 | R_T2 | R_T3 | R_T4 | R_T5 | R_T6
  (* Function arguments / return values *)
  | R_A0 | R_A1 | R_A2 | R_A3 | R_A4 | R_A5 | R_A6 | R_A7
  (* Saved registers *)
  | R_S0 | R_S1 | R_S2 | R_S3 | R_S4 | R_S5 | R_S6
  | R_S7 | R_S8 | R_S9 | R_S10 | R_S11
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE | A_EXEC
  (* Temporary variable *)
  | V_TMP.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition rvtypctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | A_WRITE | A_READ | A_EXEC => Some (2^32)
  | V_TMP => None
  | _ => Some 32
  end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniRISCVVarEq <: MiniDecidableType.
  Definition t := riscvvar.
  Definition eq_dec (v1 v2:riscvvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniRISCVVarEq.

Module RISCVArch <: Architecture.
  Module Var := Make_UDT MiniRISCVVarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := rvtypctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End RISCVArch.

(* Instantiate the Picinae modules with the RISC-V identifiers above. *)
Module IL_RISCV := PicinaeIL RISCVArch.
Export IL_RISCV.
Module Theory_RISCV := PicinaeTheory IL_RISCV.
Export Theory_RISCV.
Module Statics_RISCV := PicinaeStatics IL_RISCV Theory_RISCV.
Export Statics_RISCV.
Module FInterp_RISCV := PicinaeFInterp IL_RISCV Theory_RISCV Statics_RISCV.
Export FInterp_RISCV.
Module PSimpl_RISCV := Picinae_Simplifier_Base IL_RISCV.
Export PSimpl_RISCV.
Module PSimpl_RISCV_v1_1 := Picinae_Simplifier_v1_1 IL_RISCV Theory_RISCV Statics_RISCV FInterp_RISCV.
Ltac PSimplifier ::= PSimpl_RISCV_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_RISCV_v1_0 := Picinae_Simplifier_v1_0 IL_RISCV Theory_RISCV Statics_RISCV FInterp_RISCV.
Ltac PSimplifier ::= PSimpl_RISCV_v1_0.PSimplifier.
*)

Module ISA_RISCV := Picinae_ISA IL_RISCV PSimpl_RISCV Theory_RISCV Statics_RISCV FInterp_RISCV.
Export ISA_RISCV.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "r5_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "r5_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "r5_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "r5_psimpl" := psimpl_goal.
Ltac r5_step := ISA_step.

(* The following is needed when applying cframe theorems from Picinae_theory. *)
Theorem memacc_respects_rvtypctx: memacc_respects_typctx rvtypctx.
Proof.
  intros s1 s2 RV. rewrite <- RV. split; reflexivity.
Qed.

(* Simplify memory access propositions by observing that on RISC, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.

(* Simplify memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.


(* Assembly-level RISC-V instruction syntax: *)

Inductive rv_asm :=
| R5_Lb (r1 r2:N) (i:N)
| R5_Lh (r1 r2:N) (i:N)
| R5_Lw (r1 r2:N) (i:N)
| R5_Lbu (r1 r2:N) (i:N)
| R5_Lhu (r1 r2:N) (i:N)
| R5_Fence (i1 i2:N)
| R5_Fence_i
| R5_Addi (r1 r2:N) (i:N)
| R5_Slli (r1 r2:N) (i:N)
| R5_Slti (r1 r2:N) (i:N)
| R5_Sltiu (r1 r2:N) (i:N)
| R5_Xori (r1 r2:N) (i:N)
| R5_Ori (r1 r2:N) (i:N)
| R5_Andi (r1 r2:N) (i:N)
| R5_Srli (r1 r2:N) (i:N)
| R5_Srai (r1 r2:N) (i:N)
| R5_Auipc (r:N) (i:N)
| R5_Sb (r1 r2:N) (i:Z)
| R5_Sh (r1 r2:N) (i:Z)
| R5_Sw (r1 r2:N) (i:Z)
| R5_Add (r1 r2 r3:N)
| R5_Sub (r1 r2 r3:N)
| R5_Sll (r1 r2 r3:N)
| R5_Slt (r1 r2 r3:N)
| R5_Sltu (r1 r2 r3:N)
| R5_Xor (r1 r2 r3:N)
| R5_Srl (r1 r2 r3:N)
| R5_Sra (r1 r2 r3:N)
| R5_Or (r1 r2 r3:N)
| R5_And (r1 r2 r3:N)
| R5_Lui (r:N) (i:N)
| R5_Beq (r1 r2:N) (i:Z)
| R5_Bne (r1 r2:N) (i:Z)
| R5_Blt (r1 r2:N) (i:Z)
| R5_Bge (r1 r2:N) (i:Z)
| R5_Bltu (r1 r2:N) (i:Z)
| R5_Bgeu (r1 r2:N) (i:Z)
| R5_Jalr (r1 r2:N) (i:Z)
| R5_Jal (r:N) (i:Z)
| R5_InvalidI.

Definition rv_decode_load f :=
  match f with
  | 0 => R5_Lb | 1 => R5_Lh | 2 => R5_Lw | 4 => R5_Lbu | 5 => R5_Lhu
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_store f :=
  match f with
  | 0 => R5_Sb | 1 => R5_Sh | 2 => R5_Sw
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_binop f :=
  match f with
  | 0 => R5_Add | 256 => R5_Sub
  | 1 => R5_Sll | 2 => R5_Slt | 3 => R5_Sltu | 4 => R5_Xor
  | 5 => R5_Srl | 261 => R5_Sra
  | 6 => R5_Or | 7 => R5_And
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_branch f :=
  match f with 
  | 0 => R5_Beq | 1 => R5_Bne | 4 => R5_Blt | 5 => R5_Bge | 6 => R5_Bltu | 7 => R5_Bgeu
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_op_imm f n :=
  match f with
  | 0 => R5_Addi (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | 1 => match xbits n 25 32 with
         | 0 => R5_Slli (xbits n 7 12) (xbits n 15 20) (xbits n 20 25)
         | _ => R5_InvalidI
         end
  | 2 => R5_Slti (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | 3 => R5_Sltiu (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | 4 => R5_Xori (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | 5 => match xbits n 25 32 with
         | 0 => R5_Srli (xbits n 7 12) (xbits n 15 20) (xbits n 20 25)
         | 32 => R5_Srai (xbits n 7 12) (xbits n 15 20) (xbits n 20 25)
         | _ => R5_InvalidI
         end
  | 6 => R5_Ori (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | _ => R5_Andi (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  end.

Definition rv_decode_fence m n :=
  match m with
  | 32 => R5_Fence_i
  | _ => match N.ldiff m (N.shiftl (N.ones 8) 13) with
         | 0 => R5_Fence (xbits n 24 28) (xbits n 20 24)
         | _ => R5_InvalidI
         end
  end.

Definition rv_decode_op op n :=
  match op with
  | 3 => rv_decode_load (xbits n 12 15) (xbits n 7 12) (xbits n 15 20) (scast 12 32 (xbits n 20 32))
  | 15 => rv_decode_fence (N.shiftr n 7) n
  | 19 => rv_decode_op_imm (xbits n 12 15) n
  | 23 => R5_Auipc (xbits n 7 12) (N.land n (N.shiftl (N.ones 20) 12))
  | 35 => rv_decode_store (xbits n 12 15) (xbits n 15 20) (xbits n 20 25)
            (toZ 12 (N.lor (N.shiftl (xbits n 25 32) 5) (xbits n 7 12)))
  | 51 => rv_decode_binop (N.lor (xbits n 12 15) (N.shiftl (xbits n 25 32) 3))
                          (xbits n 7 12) (xbits n 15 20) (xbits n 20 25)
  | 55 => R5_Lui (xbits n 7 12) (xbits n 12 32)
  | 99 => rv_decode_branch (N.lor (xbits n 12 15) (N.land n 256)) (xbits n 15 20) (xbits n 20 25)
            (toZ 13 (N.lor (N.shiftl (xbits n 8 12) 1)
                      (N.lor (N.shiftl (xbits n 25 31) 5)
                        (N.lor (N.shiftl (xbits n 7 8) 11)
                          (N.shiftl (xbits n 31 32) 12)))))
  | 103 => match xbits n 12 15 with
           | 0 => R5_Jalr (xbits n 7 12) (xbits n 15 20) (toZ 12 (xbits n 20 32))
           | _ => R5_InvalidI
           end
  | 111 => match xbits n 21 22 with
           | 0 => R5_Jal (xbits n 7 12) (toZ 21 (N.lor (N.shiftl (xbits n 21 31) 1)
                                           (N.lor (N.shiftl (xbits n 20 21) 11)
                                             (N.lor (N.shiftl (xbits n 12 20) 12)
                                               (N.shiftl (xbits n 31 32) 20)))))
           | _ => R5_InvalidI
           end
  | _ => R5_InvalidI
  end.

Definition rv_decode n :=
  rv_decode_op (N.land n (N.ones 7)) n.

Definition rv_varid (n:N) :=
  match n with
  | 1 => R_RA | 2 => R_SP | 3 => R_GP | 4 => R_TP
  | 5 => R_T0 | 6 => R_T1 | 7 => R_T2
  | 8 => R_S0
  | 9 => R_S1
  | 10 => R_A0 | 11 => R_A1
  | 12 => R_A2 | 13 => R_A3 | 14 => R_A4 | 15 => R_A5 | 16 => R_A6 | 17 => R_A7
  | 18 => R_S2 | 19 => R_S3 | 20 => R_S4 | 21 => R_S5 | 22 => R_S6 | 23 => R_S7
  | 24 => R_S8 | 25 => R_S9 | 26 => R_S10 | 27 => R_S11
  | 28 => R_T3 | 29 => R_T4 | 30 => R_T5 | _ => R_T6
  end.

Definition r5var n :=
  match n with N0 => Word 0 32 | N.pos _ => Var (rv_varid n) end.

Definition r5mov n e :=
  match n with N0 => Nop | N.pos _ => Move (rv_varid n) e end.

Definition r5branch e a off :=
  If e (Jmp (Word ((Z.to_N (Z.of_N a + off)) mod 2^32) 32)) Nop.

Definition rv2il (a:addr) rvi :=
  match rvi with
  | R5_InvalidI => Exn 2
  | R5_Fence _ _ => Nop (* no effect on single-threaded machine *)
  | R5_Fence_i => Nop (* no effect on single-threaded machine *)

  (* Integer Computational Instructions *)
  | R5_Andi rd rs imm => r5mov rd (BinOp OP_AND (r5var rs) (Word imm 32))
  | R5_Xori rd rs imm => r5mov rd (BinOp OP_XOR (r5var rs) (Word imm 32))
  | R5_Ori rd rs imm => r5mov rd (BinOp OP_OR (r5var rs) (Word imm 32))
  | R5_Addi rd rs imm => r5mov rd (BinOp OP_PLUS (r5var rs) (Word imm 32))
  | R5_Sub rd rs1 rs2 => r5mov rd (BinOp OP_MINUS (r5var rs1) (r5var rs2))
  | R5_And rd rs1 rs2 => r5mov rd (BinOp OP_AND (r5var rs1) (r5var rs2))
  | R5_Xor rd rs1 rs2 => r5mov rd (BinOp OP_XOR (r5var rs1) (r5var rs2))
  | R5_Or rd rs1 rs2 => r5mov rd (BinOp OP_OR (r5var rs1) (r5var rs2))
  | R5_Add rd rs1 rs2 => r5mov rd (BinOp OP_PLUS (r5var rs1) (r5var rs2))
  | R5_Lui rd imm => r5mov rd (BinOp OP_LSHIFT (Word imm 32) (Word 12 32))
  | R5_Sll rd rs1 rs2 => r5mov rd (BinOp OP_LSHIFT (r5var rs1) (r5var rs2))
  | R5_Srl rd rs1 rs2 => r5mov rd (BinOp OP_RSHIFT (r5var rs1) (r5var rs2))
  | R5_Sra rd rs1 rs2 => r5mov rd (BinOp OP_ARSHIFT (r5var rs1) (r5var rs2))
  | R5_Slli rd rs1 shamt => r5mov rd (BinOp OP_LSHIFT (r5var rs1) (Word shamt 32))
  | R5_Slti rd rs1 imm => r5mov rd (Cast CAST_UNSIGNED 32 (BinOp OP_SLT (r5var rs1) (Word imm 32)))
  | R5_Sltiu rd rs1 imm => r5mov rd (Cast CAST_UNSIGNED 32 (BinOp OP_LT (r5var rs1) (Word imm 32)))
  | R5_Srli rd rs1 shamt => r5mov rd (BinOp OP_RSHIFT (r5var rs1) (Word shamt 32))
  | R5_Srai rd rs1 shamt => r5mov rd (BinOp OP_ARSHIFT (r5var rs1) (Word shamt 32))
  | R5_Sltu rd rs1 rs2 => r5mov rd (Cast CAST_UNSIGNED 32 (BinOp OP_LT (r5var rs1) (r5var rs2)))
  | R5_Slt rd rs1 rs2 => r5mov rd (Cast CAST_UNSIGNED 32 (BinOp OP_SLT (r5var rs1) (r5var rs2)))

  (* Conditional Transfer Instructions *)
  | R5_Bltu rs1 rs2 off => r5branch (BinOp OP_LT (r5var rs1) (r5var rs2)) a off
  | R5_Blt rs1 rs2 off => r5branch (BinOp OP_SLT (r5var rs1) (r5var rs2)) a off
  | R5_Bgeu rs1 rs2 off => r5branch (UnOp OP_NOT (BinOp OP_LT (r5var rs1) (r5var rs2))) a off
  | R5_Bge rs1 rs2 off => r5branch (UnOp OP_NOT (BinOp OP_SLT (r5var rs1) (r5var rs2))) a off
  | R5_Bne rs1 rs2 off => r5branch (BinOp OP_NEQ (r5var rs1) (r5var rs2)) a off
  | R5_Beq rs1 rs2 off => r5branch (BinOp OP_EQ (r5var rs1) (r5var rs2)) a off
  (* Unconditional jumps *)
  | R5_Jalr rd rs1 imm => Seq (Move V_TMP (BinOp OP_AND (BinOp OP_PLUS (r5var rs1) (Word (ofZ 32 imm) 32))
                                                        (Word (N.ones 32 - 1) 32)))
                              (Seq (r5mov rd (Word ((a+4) mod 2^32) 32))
                                   (Jmp (Var V_TMP)))
  | R5_Jal rd off => Seq (r5mov rd (Word ((a+4) mod 2^32) 32))
                         (Jmp (Word (N.land (Z.to_N (Z.of_N a + off)) (N.ones 32 - 1)) 32))
  | R5_Auipc rd off => r5mov rd (Word ((a + N.shiftl off 12) mod 2^32) 32)

  (* Load and Store Instructions *)
  | R5_Lb rd rs1 imm => r5mov rd (Cast CAST_SIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (r5var rs1) (Word imm 32)) LittleE 1))
  | R5_Lh rd rs1 imm => r5mov rd (Cast CAST_SIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (r5var rs1) (Word imm 32)) LittleE 2))
  | R5_Lbu rd rs1 imm => r5mov rd (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (r5var rs1) (Word imm 32)) LittleE 1))
  | R5_Lhu rd rs1 imm => r5mov rd (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) (BinOp OP_PLUS (r5var rs1) (Word imm 32)) LittleE 2))
  | R5_Lw rd rs1 imm => r5mov rd (Load (Var V_MEM32) (BinOp OP_PLUS (r5var rs1) (Word imm 32)) LittleE 4)
  | R5_Sb rb rs imm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (r5var rb) (Word (ofZ 32 imm) 32)) (Cast CAST_LOW 8 (r5var rs)) LittleE 1)
  | R5_Sh rb rs imm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (r5var rb) (Word (ofZ 32 imm) 32)) (Cast CAST_LOW 16 (r5var rs)) LittleE 2)
  | R5_Sw rb rs imm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (r5var rb) (Word (ofZ 32 imm) 32)) (r5var rs) LittleE 4)
  end.

Definition rv_stmt m a :=
  rv2il a match a mod 4 with 0 => rv_decode (getmem 32 LittleE 4 m a) | _ => R5_InvalidI end.

Definition rv_prog : program :=
  fun s a => if N.testbit (s A_EXEC) a then
               Some (4, rv_stmt (getmem 32 LittleE 1 (s V_MEM32) a) a)
             else None.

Lemma hastyp_r5mov:
  forall c0 c n e (TS: hastyp_stmt c0 c (Move (rv_varid n) e) c),
  hastyp_stmt c0 c (r5mov n e) c.
Proof.
  intros. destruct n. apply TNop. reflexivity. exact TS.
Qed.

Lemma hastyp_rvmov:
  forall n e (TE: hastyp_exp rvtypctx e 32),
  hastyp_stmt rvtypctx rvtypctx (Move (rv_varid n) e) rvtypctx.
Proof.
  intros. erewrite store_upd_eq at 3.
    eapply TMove.
      right. destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
      exact TE.
      reflexivity.
    destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
Qed.

Lemma hastyp_r5store:
  forall e (TE: hastyp_exp rvtypctx e (2^32*8)),
  hastyp_stmt rvtypctx rvtypctx (Move V_MEM32 e) rvtypctx.
Proof.
  intros. erewrite store_upd_eq at 3.
    eapply TMove.
      right. reflexivity.
      exact TE.
      reflexivity.
    reflexivity.
Qed.

Lemma hastyp_r5var:
  forall n, hastyp_exp rvtypctx (r5var n) 32.
Proof.
  intro. destruct n as [|n].
    apply TWord. reflexivity.
    apply TVar. repeat first [ reflexivity | destruct n as [n|n|] ].
Qed.

Theorem welltyped_rv2il:
  forall a n, hastyp_stmt rvtypctx rvtypctx (rv2il a (rv_decode n)) rvtypctx.
Proof.
  intros. unfold rv_decode, rv_decode_op, rv_decode_op_imm, rv_decode_fence,
                 rv_decode_load, rv_decode_store, rv_decode_binop, rv_decode_branch.

  repeat match goal with |- context [ match ?x with _ => _ end ] =>
    let op := fresh "op" in
    generalize x; intro op;
    first [ destruct op as [|op] | destruct op as [op|op|] ];
    try apply TExn
  end.

  all: try solve [ do 2 repeat first
  [ reflexivity
  | discriminate 1
  | apply hastyp_r5mov
  | apply hastyp_rvmov
  | apply hastyp_r5var
  | apply hastyp_r5store
  | apply TBinOp with (w:=32)
  | eapply N.lt_le_trans; [apply xbits_bound|]
  | apply ofZ_bound
  | apply N.mod_lt
  | econstructor ] ].

  econstructor.
    apply hastyp_r5mov, hastyp_rvmov. econstructor. apply N.mod_lt. discriminate 1.
    econstructor. econstructor.
      change (_-1) with (N.land (N.ones 32 - 1) (N.ones 32)). rewrite N.land_assoc, N.land_ones. apply N.mod_lt. discriminate 1.
      reflexivity.
    reflexivity.

  econstructor.
    econstructor.
      left. reflexivity.
      econstructor.
        econstructor. apply hastyp_r5var. econstructor. apply ofZ_bound.
        econstructor. reflexivity.
      reflexivity.
    econstructor.
      apply hastyp_r5mov. erewrite store_upd_eq.
        eapply TMove.
          right. destruct xbits as [|r]. reflexivity. repeat first [ reflexivity | destruct r as [r|r|] ].
          econstructor. apply N.mod_lt. discriminate 1.
          reflexivity.
        destruct xbits as [|r]. reflexivity. repeat first [ reflexivity | destruct r as [r|r|] ].
      econstructor.
        econstructor. apply update_updated.
        reflexivity.
      reflexivity.
    intros r t H. rewrite <- H. destruct r; apply update_frame; discriminate.
Qed.

Theorem welltyped_rvprog:
  welltyped_prog rvtypctx rv_prog.
Proof.
  intros s a. unfold rv_prog.
  destruct (N.testbit _ _); [|exact I].
  exists rvtypctx. unfold rv_stmt. destruct (a mod 4).
    apply welltyped_rv2il.
    apply TExn. reflexivity.
Qed.


(* Define ISA-specific notations: *)

Declare Scope r5_scope.
Delimit Scope r5_scope with risc5.
Bind Scope r5_scope with stmt exp trace.
Open Scope r5_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : r5_scope.

Module RISCVNotations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : r5_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : r5_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : r5_scope. (* read dword from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : r5_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : r5_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem 23 LittleE 4 m a v) (at level 50, left associativity) : r5_scope. (* write dword to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End RISCVNotations.
