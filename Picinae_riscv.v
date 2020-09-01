(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   * Picinae_finterp                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_slogic                                           MDMMMMMMMO.7MDM7M+
   Then compile this module with menu option                   ZMMMMMMMM.$MM8$MN
   Compile->Compile_buffer.                                    $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
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
Require Export Picinae_finterp.
Require Export Picinae_statics.
Require Export Picinae_slogic.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from RISC-V native code: *)
Inductive riscvvar :=
  (* Main memory: MemT 32 *)
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
  | A_READ | A_WRITE | A_EXEC.

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
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 32 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 32 /\ w a <> 0.
End RISCVArch.

(* Instantiate the Picinae modules with the RISC-V identifiers above. *)
Module IL_RISCV := PicinaeIL RISCVArch.
Export IL_RISCV.
Module Theory_RISCV := PicinaeTheory IL_RISCV.
Export Theory_RISCV.
Module Statics_RISCV := PicinaeStatics IL_RISCV.
Export Statics_RISCV.
Module FInterp_RISCV := PicinaeFInterp IL_RISCV Statics_RISCV.
Export FInterp_RISCV.
Module SLogic_RISCV := PicinaeSLogic IL_RISCV.
Export SLogic_RISCV.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition rvtypctx (v:riscvvar) :=
  match v with
  | V_MEM32 | A_WRITE | A_READ | A_EXEC => Some (MemT 32)
  | _ => Some (NumT 32)
  end.

Definition rv_wtm {s v m w} := @models_wtm v rvtypctx s m w.
Definition rv_regsize {s v n w} := @models_regsize v rvtypctx s n w.


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

Definition xbits n i j := N.land (N.shiftr n i) (N.ones (j - i)).

Definition rv_decode_load n :=
  match xbits n 12 15 with
  | 0 => R5_Lb | 1 => R5_Lh | 2 => R5_Lw | 4 => R5_Lbu | 5 => R5_Lhu
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_store n :=
  match xbits n 12 15 with
  | 0 => R5_Sb | 1 => R5_Sh | 2 => R5_Sw
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_binop n :=
  match N.lor (xbits n 12 15) (N.shiftl (xbits n 25 32) 3) with
  | 0 => R5_Add | 256 => R5_Sub
  | 1 => R5_Sll | 2 => R5_Slt | 3 => R5_Sltu | 4 => R5_Xor
  | 5 => R5_Srl | 261 => R5_Sra
  | 6 => R5_Or | 7 => R5_And
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_branch n :=
  match N.lor (xbits n 12 15) (N.land n 256) with
  | 0 => R5_Beq | 1 => R5_Bne | 4 => R5_Blt | 5 => R5_Bge | 6 => R5_Bltu | 7 => R5_Bgeu
  | _ => (fun _ _ _ => R5_InvalidI)
  end.

Definition rv_decode_op op n :=
  match op with
  | 3 => rv_decode_load n (xbits n 7 12) (xbits n 15 20) (xbits n 20 32)
  | 15 => (* Fence *)
    match N.shiftr n 7 with
    | 32 => R5_Fence_i
    | m => match N.ldiff m (N.shiftl (N.ones 8) 13) with
           | 0 => R5_Fence (xbits n 24 28) (xbits n 20 24)
           | _ => R5_InvalidI
           end
    end
  | 19 => (* Op_Imm *)
    match xbits n 12 15 with
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
    end
  | 23 => R5_Auipc (xbits n 7 12) (N.land n (N.shiftl (N.ones 20) 12))
  | 35 => rv_decode_store n (xbits n 15 20) (xbits n 20 25)
                          (toZ 12 (N.lor (N.shiftl (xbits n 25 32) 5) (xbits n 7 12)))
  | 51 => rv_decode_binop n (xbits n 7 12) (xbits n 15 20) (xbits n 20 25)
  | 55 => R5_Lui (xbits n 7 12) (N.land n (N.shiftl (N.ones 20) 12))
  | 99 => rv_decode_branch n (xbits n 15 20) (xbits n 20 25)
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
  | R5_InvalidI => Exn 6
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
  | R5_Lui rd imm => r5mov rd (BinOp OP_LSHIFT (Word imm 32) (Word 20 32))
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
  | R5_Jalr rd rs1 imm => Seq (r5mov rd (Word ((a+4) mod 2^32) 32))
                              (Jmp (BinOp OP_PLUS (r5var rs1) (Word (ofZ 32 imm) 32)))
  | R5_Jal rd off => Seq (r5mov rd (Word ((a+4) mod 2^32) 32))
                         (Jmp (Word ((Z.to_N (Z.of_N a + off)) mod 2^32) 32))
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

Definition rv_stmt m a := rv2il a (rv_decode (getmem LittleE 4 m a)).

Definition rv_prog : program :=
  fun s a => match s V_MEM32, s A_EXEC with
             | VaM m _, VaM e _ => match e a with
                                   | N0 => None
                                   | _ => Some (4, rv_stmt m a)
                                   end
             | _, _ => None
             end.

Lemma hastyp_r5mov:
  forall c0 c n e (TS: hastyp_stmt c0 c (Move (rv_varid n) e) c),
    hastyp_stmt c0 c (r5mov n e) c.
Proof.
  intros. destruct n. apply TNop. exact TS.
Qed.

Lemma hastyp_rvmov:
  forall n e (TE: hastyp_exp rvtypctx e (NumT 32)),
    hastyp_stmt rvtypctx rvtypctx (Move (rv_varid n) e) rvtypctx.
Proof.
  intros. erewrite store_upd_eq at 3.
  apply TMove.
  right. destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
  exact TE.
  destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
Qed.

Lemma hastyp_r5store:
  forall e (TE: hastyp_exp rvtypctx e (MemT 32)),
    hastyp_stmt rvtypctx rvtypctx (Move V_MEM32 e) rvtypctx.
Proof.
  intros. erewrite store_upd_eq at 3.
  apply TMove.
  right. reflexivity.
  exact TE.
  reflexivity.
Qed.

Lemma hastyp_r5var:
  forall n, hastyp_exp rvtypctx (r5var n) (NumT 32).
Proof.
  intro. destruct n as [|n].
  apply TWord. reflexivity.
  apply TVar. repeat first [ reflexivity | destruct n as [n|n|] ].
Qed.

Lemma xbits_bound:
  forall n i j w, j-i <= w -> xbits n i j < 2^w.
Proof.
  intros. unfold xbits. eapply N.lt_le_trans.
  rewrite N.land_ones. apply N.mod_upper_bound, N.pow_nonzero. discriminate 1.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Theorem welltyped_rv2il:
  forall a n, hastyp_stmt rvtypctx rvtypctx (rv2il a (rv_decode n)) rvtypctx.
Proof.
  intros. unfold rv_decode, rv_decode_op, rv_decode_load, rv_decode_store,
          rv_decode_binop, rv_decode_branch.

  repeat match goal with |- context [ match ?x with _ => _ end ] =>
                         let op := fresh "op" in
                         generalize x; intro op;
                           first [ destruct op as [|op] | destruct op as [op|op|] ];
                           try apply TExn
         end.

  all: repeat first
              [ reflexivity
              | discriminate 1
              | apply hastyp_r5mov
              | apply hastyp_rvmov
              | apply hastyp_r5var
              | apply hastyp_r5store
              | apply TBinOp with (w:=32)
              | apply xbits_bound
              | apply ofZ_bound
              | apply N.mod_lt
              | econstructor ].

  rewrite N.land_comm. eapply land_bound, N.lt_le_trans. apply shiftl_bound, ones_bound. reflexivity.
Qed.

Theorem welltyped_rvprog:
  welltyped_prog rvtypctx rv_prog.
Proof.
  intros s a. unfold rv_prog.
  destruct (s V_MEM32), (s A_EXEC); try exact I.
  destruct (m0 a).
  exact I.
  exists rvtypctx. apply welltyped_rv2il.
Qed.


(* Create some automated machinery for simplifying symbolic expressions. *)

Lemma memacc_read_frame:
  forall h s v u (NE: v <> A_READ),
    MemAcc mem_readable h (update s v u) = MemAcc mem_readable h s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall h s v u (NE: v <> A_WRITE),
    MemAcc mem_writable h (update s v u) = MemAcc mem_writable h s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall h s v u1 u2,
    MemAcc mem_readable h (update (update s v u2) A_READ u1) =
    MemAcc mem_readable h (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall h s v u1 u2,
    MemAcc mem_writable h (update (update s v u2) A_WRITE u1) =
    MemAcc mem_writable h (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.


(* Introduce automated machinery for verifying a RISC-V machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine.

   In order for this methodology to prove that a post-condition holds at
   subroutine exit, we must attach one of these invariants (the post-condition)
   to the return address of the subroutine.  This is a somewhat delicate
   process, since unlike most other code addresses, the exact value of the
   return address is an unknown (defined by the caller).  We therefore adopt
   the convention that subroutines "exit" whenever control flows to an address
   for which no IL code is defined at that address.  This allows proving
   correctness of a subroutine by lifting only the subroutine to IL code (or
   using the pmono theorems from Picinae_theory to isolate only the subroutine
   from a larger program), leaving the non-subroutine code undefined (None). *)

(* Simplify memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
                               rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
      end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
                               rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
      end.

(* Symbolically evaluate a RISC-V machine instruction for one step. *)
Ltac rv_step_and_simplify XS :=
  step_stmt XS;
  simpl_memaccs XS;
  destruct_memaccs XS.


(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).  This slow-down can
   be avoided by sequestering prevalent injections into lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
    Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Exit a. Proof eq_refl.
Remark exitof_some a x: exitof a (Some x) = x. Proof eq_refl.

(* Solve a goal of the form (p s a = None), which indicates that program p is
   exiting the subroutine.  For now, we automatically solve for three common
   cases: (A) address a is a constant, allowing function p to fully evaluate
   (reflexivity); (B) the goal is an assumption, or (C) the code is immutable,
   so there is an assumption of the form (H: forall s, p s a = None) for a
   particular return address a.  Cases other than these three forms will need
   to be solved manually by the user. *)
Ltac prove_prog_exits :=
  solve [ reflexivity | assumption |
          match goal with [ H: forall s, ?p s ?a = None |- ?p _ ?a = None ] => apply H end ].

(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac rv_invhere :=
  first [ eapply nextinv_here; [reflexivity|]
        | apply nextinv_exn
        | apply nextinv_ret; [ prove_prog_exits |] ];
  simpl_stores.

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac rv_invseek :=
  apply NIStep; [reflexivity|];
  let sz := fresh "sz" in let q := fresh "q" in let s := fresh "s" in let x := fresh "x" in
                                                                      let IL := fresh "IL" in let XS := fresh "XS" in
                                                                                              intros sz q s x IL XS;
                                                                                              apply inj_prog_stmt in IL; destruct IL; subst sz q;
                                                                                              rv_step_and_simplify XS;
                                                                                              repeat lazymatch type of XS with
                                                                                                     | s=_ /\ x=_ => destruct XS; subst s x
                                                                                                     | exec_stmt _ _ (if ?c then _ else _) _ _ =>
                                                                                                       let BC := fresh "BC" in destruct c eqn:BC;
                                                                                                                               rv_step_and_simplify XS
                                                                                                     | exec_stmt _ _ (N.iter _ _ _) _ _ => fail
                                                                                                     | _ => rv_step_and_simplify XS
                                                                                                     end;
                                                                                              repeat match goal with [ u:value |- _ ] => clear u
                                                                                                                | [ n:N |- _ ] => clear n
                                                                                                                | [ m:addr->N |- _ ] => clear m end;
                                                                                              try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
                                                                                              try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac rv_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ rv_invseek; try rv_invhere | rv_invhere ].


Module RISCVNotations.

  Notation "Ⓜ m" := (VaM m 32) (at level 20). (* memory value *)
  Notation "ⓑ u" := (VaN u 1) (at level 20). (* bit value *)
  Notation "Ⓑ u" := (VaN u 8) (at level 20). (* byte value *)
  Notation "Ⓦ u" := (VaN u 16) (at level 20). (* word value *)
  Notation "Ⓓ u" := (VaN u 32) (at level 20). (* dword value *)
  Notation "m Ⓑ[ a  ]" := (getmem LittleE 1 m a) (at level 10). (* read byte from memory *)
  Notation "m Ⓦ[ a  ]" := (getmem LittleE 2 m a) (at level 10). (* read word from memory *)
  Notation "m Ⓓ[ a  ]" := (getmem LittleE 4 m a) (at level 10). (* read dword from memory *)
  Notation "m [Ⓑ a := v  ]" := (setmem LittleE 1 m a v) (at level 50, left associativity). (* write byte to memory *)
  Notation "m [Ⓦ a := v  ]" := (setmem LittleE 2 m a v) (at level 50, left associativity). (* write word to memory *)
  Notation "m [Ⓓ a := v  ]" := (setmem LittleE 4 m a v) (at level 50, left associativity). (* write dword to memory *)
  Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
  Notation "x ⊖ y" := ((x-y) mod 2^32) (at level 50, left associativity). (* modular subtraction *)
  Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
  Notation "x << y" := (N.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
  Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
  Notation "x >>> y" := (ashiftr 32 x y) (at level 40, left associativity). (* arithmetic shift-right *)
  Notation "x .& y" := (N.land x y) (at level 25, left associativity). (* logical and *)
  Notation "x .^ y" := (N.lxor x y) (at level 25, left associativity). (* logical xor *)
  Notation "x .| y" := (N.lor x y) (at level 25, left associativity). (* logical or *)

End RISCVNotations.
