(* decoder/lifter for ARMv7 *)

Require Export Picinae_armv7.
Require Import NArith.
Require Import ZArith.
Open Scope N.

Inductive arm7_asm :=
  (* Data Processing *)
  | ARM_AND   (cond i s rn rd op2: N)
  | ARM_EOR   (cond i s rn rd op2: N)
  | ARM_SUB   (cond i s rn rd op2: N)
  | ARM_RSB   (cond i s rn rd op2: N)
  | ARM_ADD   (cond i s rn rd op2: N)
  | ARM_ADC   (cond i s rn rd op2: N)
  | ARM_SBC   (cond i s rn rd op2: N)
  | ARM_RSC   (cond i s rn rd op2: N)
  | ARM_TST   (cond i   rn    op2: N)
  | ARM_TEQ   (cond i   rn    op2: N)
  | ARM_CMP   (cond i   rn    op2: N)
  | ARM_CMN   (cond i   rn    op2: N)
  | ARM_ORR   (cond i s rn rd op2: N)
  | ARM_MOV   (cond i s    rd op2: N)
  | ARM_BIC   (cond i s rn rd op2: N)
  | ARM_MVN   (cond i s    rd op2: N)

  | ARM_MOVT  (cond imm4 rd imm12: N)
  | ARM_MOVW  (cond imm4 rd imm12: N)

  | ARM_POP   (cond regs: N)
  | ARM_PUSH  (cond regs: N)

  (* Load instructions *)
  | ARM_LDR   (cond A op1 rn B rt op2: N)
  | ARM_LDRB  (cond A op1 rn B rt op2: N)
  | ARM_LDRT  (cond A op1 rn B rt op2: N)
  | ARM_LDRBT (cond A op1 rn B rt op2: N)

  (* Extra load instuctions *)
  | ARM_LDRD  (cond  op1  rn   rt op2: N)
  | ARM_LDRH  (cond  op1  rn   rt op2: N)
  | ARM_LDRSB (cond  op1  rn   rt op2: N)

  (* Store instructions *)
  | ARM_STR   (cond A op1 rn B rt op2: N)
  | ARM_STRT  (cond A op1 rn B rt op2: N)
  | ARM_STRB  (cond A op1 rn B rt op2: N)
  | ARM_STRBT (cond A op1 rn B rt op2: N)

  (* Extra store instuctions *)
  | ARM_STRH  (cond  op1  rn   rt op2: N)

  (* Branch Instructions *)
  | ARM_B     (cond imm24: N)
  | ARM_BL    (cond imm24: N)
  | ARM_BLX   (cond rm: N)  (* BLX Register *)
  | ARM_BX    (cond rm: N)

  (* Nop *)
  | ARM_NOP   (cond : N)

  (* Syscall *)
  | ARM_SVC   (cond imm24: N)

  | ARM_InvalidI.

Definition arm_varid (n: N) :=
  match n with
  | 0 => R_R0 | 1 => R_R1 | 2 => R_R2 | 3 => R_R3
  | 4 => R_R4 | 5 => R_R5 | 6 => R_R6 | 7 => R_R7
  | 8 => R_R8 | 9 => R_R9 | 10 => R_R10 | 11 => R_R11
  | 12 => R_R12 | 13 => R_SP | 14 => R_LR | _ => R_PC
  end.

Definition arm_var n :=
  Var (arm_varid n).

(* ---------------------------- Opcode Definition ---------------------------- *)

Definition bitn n b := xbits n b (b + 1).

Definition arm_data_opcode opcode :=
  let no_dest := (fun F a b _ c _  => F a b c) in
  let unary := (fun F a b c _ => F a b c) in
  match opcode with
  | 0 => ARM_AND | 1 => ARM_EOR | 2 => ARM_SUB | 3 => ARM_RSB
  | 4 => ARM_ADD | 5 => ARM_ADC | 6 => ARM_SBC | 7 => ARM_RSC
  | 8 => no_dest ARM_TST | 9 => no_dest ARM_TEQ | 10 => no_dest ARM_CMP | 11 => no_dest ARM_CMN
  | 12 => ARM_ORR | 13 => unary ARM_MOV | 14 => ARM_BIC | 15 => unary ARM_MVN
  | _ => (fun _ _ _ _ _ _ => ARM_InvalidI)
  end.

Definition arm_decode_extra_load_store (n: N) := (* pg. a5-201,202 *)
  let op1 := xbits n 0 3 in
  let op2 := xbits n 5 7 in
  match op2 with
  | 1 => match op1 with
         | 0 | 2 | 4 | 6 => ARM_STRH (xbits n 28 32) (xbits n 20 25) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
         | 1 | 3 | 5 | 7 => ARM_LDRH (xbits n 28 32) (xbits n 20 25) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
         | _ => ARM_InvalidI
         end
  | 2 => match op1 with
         | 0 | 2 | 4 | 6 => ARM_LDRD (xbits n 28 32) (xbits n 20 25) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
         | 1 | 3 | 5 | 7 => ARM_LDRSB (xbits n 28 32) (xbits n 20 25) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
         | _ => ARM_InvalidI
         end
  | _ => ARM_InvalidI
  end.

Definition arm_decode_mul_and_sync (n: N) := (* pg. a5-200, a5-203 *)
  ARM_InvalidI.
Definition arm_decode_misc n := (* pg. a5-205 *)
  (* TODO: add rest of misc instructions *)
  ARM_BX (xbits n 28 32) (xbits n 0 4).

Definition arm_decode_data n := (* pg. a5-194 *)
  match bitn n 25, xbits n 20 25, xbits n 4 8 with (* op, op1, op2 *)
  | 0, _, 11 | 0, _, 13 | 0, _, 15   (* 0, _, 0b1011 0b11x1 *) => arm_decode_extra_load_store n
  | 0, _, 9                                 (* 0, _, 0b1001 *) => arm_decode_mul_and_sync n
  | 0, 16, _ | 0, 18, _ | 0, 20, _ | 0, 22, _ (* 0, 0b10xx0 *) => arm_decode_misc n
  | 1, 20, _ => ARM_MOVT (xbits n 28 32) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
  | 1, 16, _ => ARM_MOVW (xbits n 28 32) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
  | _, _, _ => arm_data_opcode (xbits n 21 25) (xbits n 28 32) (bitn n 25) (bitn n 20) (xbits n 16 20) (xbits n 12 16) (xbits n 0 12)
  end.

Definition arm_load_and_store_opcode op1 := (* pg. a5-206 *)
  match xbits op1 0 3, xbits op1 3 5 with
  | 0, _ => ARM_STR
  | 1, _ => ARM_LDR
  | 2, 0 | 2, 1 => ARM_STRT
  | 2, _ => ARM_STR
  | 3, 0 | 3, 1 => ARM_LDRT
  | 3, _ => ARM_LDR
  | 4, _ => ARM_STRB
  | 5, _ => ARM_LDRB
  | 6, 0 | 6, 1 => ARM_STRBT
  | 6, _ => ARM_STRB
  | 7, 0 | 7, 1 => ARM_LDRBT
  | 7, _ => ARM_LDRB
  | _, _ => (fun _ _ _ _ _ _ _ => ARM_InvalidI)
  end.

Definition arm_decode_media (n: N) := (* pg. a5-207 *)
  ARM_InvalidI.

Definition arm_decode_load_and_store n :=
  match bitn n 25, bitn n 4 with
  | 1, 1 => arm_decode_media n
  | _, _ => arm_load_and_store_opcode (xbits n 20 25) (xbits n 28 32) (bitn n 25) (xbits n 20 25) (xbits n 16 20) (bitn n 5) (xbits n 12 16) (xbits n 0 12)
  end.

Definition arm_decode_branch n := (* pg. a5-212 *)
  let cond := xbits n 28 32 in
  match xbits n 24 26, xbits n 20 24, xbits n 16 20 with
  | 0, 0, _ | 0, 2, _  => ARM_InvalidI (* stmda stmed *)
  | 0, 1, _ | 0, 3, _  => ARM_InvalidI (* ldmda ldmfa *)
  | 0, 8, _ | 0, 10, _ => ARM_InvalidI (* stm stmia stmea *)
  | 0, 11, 13          => ARM_POP cond (xbits n 0 16)
  | 0, 9, _ | 0, 11, _ => ARM_InvalidI (* ldm ldmia ldmfd *)
  | 1, 2, 13           => ARM_PUSH cond (xbits n 0 16)
  | 1, 2, 15           => ARM_BLX cond (xbits n 0 4) 
  | 1, 0, _ | 1, 2, _  => ARM_InvalidI (* stmdb stmfd *)
  | 1, 1, _ | 1, 3, _  => ARM_InvalidI (* ldmdb ldmea *)
  | 1, 8, _ | 1, 10, _ => ARM_InvalidI (* stmib stmfa *)
  | 1, 9, _ | 1, 11, _ => ARM_InvalidI (* ldmib ldmed *)
  | 2, _, _            => ARM_B cond (xbits n 0 24)
  | 3, _, _            => ARM_BL cond (xbits n 0 24)
  | _, _, _ => match bitn n 20 with
               | 0 => ARM_InvalidI (* stm *)
               | _ => ARM_InvalidI (* ldm *)
               end
  end.

(*
Definition arm_decode_unconditional n :=
  (* TODO: add unconditional instructions *)
  match xbits n 25 28 with
  | 5 => ARM_BLX_IMM (bitn n 24) (xbits n 0 24) (* il not modeled, since no thumb support *)
  | _ => ARM_InvalidI
  end.

*)
Definition arm_decode n :=
  match xbits n 28 32 with
  (*| 15 => arm_decode_unconditional n (* unconditional *)*)
  | _ => match (xbits n 26 28) with
    | 0 => arm_decode_data n (* data processing *)
    | 1 => arm_decode_load_and_store n (* load/store word *)
    | 2 => arm_decode_branch n (* branch *)
    | _ => ARM_InvalidI (* coprocessor *)
    end
  end.

(* ----------------------------- Intermediate Language Translation -----------------------------*)

(* Make stmt conditional, where n is the value of the cond field *)
Definition arm_cond n stmt :=
  match n with
  (* EQ, NE *)
  | 0 => If (Var R_ZF) stmt Nop
  | 1 => If (Var R_ZF) Nop stmt
  (* CS, CC *)
  | 2 => If (Var R_CF) stmt Nop
  | 3 => If (Var R_CF) Nop stmt
  (* MI, PL *)
  | 4 => If (Var R_NF) stmt Nop
  | 5 => If (Var R_NF) Nop stmt
  (* VS, VC *)
  | 6 => If (Var R_VF) stmt Nop
  | 7 => If (Var R_VF) Nop stmt
  (* HI, LS *)
  | 8 => If (BinOp OP_AND (Var R_CF) (UnOp OP_NOT (Var R_CF))) stmt Nop
  | 9 => If (BinOp OP_AND (Var R_CF) (UnOp OP_NOT (Var R_CF))) Nop stmt
  (* GE, LT *)
  | 10 => If (BinOp OP_EQ (Var R_NF) (Var R_VF)) stmt Nop
  | 11 => If (BinOp OP_EQ (Var R_NF) (Var R_VF)) Nop stmt
  (* GT, LE *)
  | 12 => If (BinOp OP_AND (UnOp OP_NOT (Var R_ZF)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) stmt Nop
  | 13 => If (BinOp OP_AND (UnOp OP_NOT (Var R_ZF)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) Nop stmt
  (* AL *)
  | 14 | 15 => stmt
  | _ => Exn 6
  end.

(* Covert the second operand of data-processing and load/store instructions into an IL expression,
   where i is the bit indicating if it is an immediate or register operand and op2 is the 12-bit field *)
Definition arm_op2 i op2 :=
  match i with
  (* register / register-shifted register *)
  (* the first 4 bits hold a register id *)
  (* bits 5,6 indicate the type of rotation (left, right, arithmetic right, rotate right) *)
  (* bit 4 indicates if the shift amount is an immediate or register *)
  (* the last 5 bits hold an immediate value or a register id *)
  | 0 => let reg := Var (arm_varid (xbits op2 0 4)) in
         let type := xbits op2 5 7 in
         let shift := match (bitn op2 4) with
                      | 0 => Word (xbits op2 7 12) 32 (* register *)
                      | _ => BinOp OP_AND (Var (arm_varid (xbits op2 8 12))) (Word 255 32) (* register-shifted register *)
                      end in
         match type with (* TODO: edge cases like LSR #0 *)
         | 0 => BinOp OP_LSHIFT reg shift
         | 1 => BinOp OP_RSHIFT reg shift
         | 2 => BinOp OP_ARSHIFT reg shift
         | _ => BinOp OP_OR (BinOp OP_RSHIFT reg shift) (BinOp OP_LSHIFT reg (BinOp OP_MINUS (Word 32 32) shift))
         end
  (* immediate *)
  (* the first 8 bits hold an immediate value *)
  (* the last 4 bits hold the rotation value *)
  (* the operand = imm rotated right by 2*rot *)
  | _ => let imm := xbits op2 0 8 in
         let rot := xbits op2 8 12 in
         Word (N.land (N.shiftr (cbits imm 32 imm) (rot + rot)) (N.ones 32)) 32
  end.

(* Like arm_op2, but return the carry value *)
Definition arm_op2_carry i op2 :=
  match i with
  (* register / register-shifted register *)
  | 0 => let reg := Var (arm_varid (xbits op2 0 4)) in
         let type := xbits op2 5 7 in
         let shift := match (bitn op2 4) with
                      | 0 => Word ((xbits op2 7 12) - 1) 32 (* register *)
                      | _ => BinOp OP_MINUS (BinOp OP_AND (Var (arm_varid (xbits op2 8 12))) (Word 255 32)) (Word 1 32) (* register-shifted register *)
                      end in
         match type with (* TODO: edge cases like LSR #0 *)
         | 0 => Cast CAST_LOW 1 (BinOp OP_LSHIFT reg shift)
         | _ => Cast CAST_LOW 1 (BinOp OP_RSHIFT reg shift)
         end
  (* immediate *)
  | _ => let imm := xbits op2 0 8 in
         let rot := xbits op2 8 12 in
         (* TODO: this is well defined in the manual, but the pcode lifter just says its unknown so i will leave it like this *)
         Unknown 1
  end.

(* Get the offset address in a load/store instruction *)
Definition arm_load_store_offset_addr A op1 rn op2 :=
  let offset := match A with
                | 0 => Word (xbits op2 0 12) 32
                | _ => arm_op2 A op2
                end in
  match bitn op1 3 with
  | 0 => BinOp OP_MINUS (arm_var rn) offset
  | _ => BinOp OP_PLUS (arm_var rn) offset
  end.

(* Get the IL stmt that updates the register for load instructions / updates memory for store instructions *)
Definition arm_load_store_move_il type byte rt address :=
  match type, byte with
  | 0, 0 => Move (arm_varid rt) (Load (Var V_MEM32) address LittleE 4)
  | 0, _ => Move (arm_varid rt) (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) address LittleE 1))
  | _, 0 => Move V_MEM32 (Store (Var V_MEM32) address (arm_var rt) LittleE 4)
  | _, _ => Move V_MEM32 (Store (Var V_MEM32) address (Cast CAST_LOW 8 (arm_var rt)) LittleE 1)
  end.

(* Get the offset address in a load/store instruction *)
Definition arm_load_store_halfword_addr op1 rn op2 :=
  match op1 with
  | 4| 5 | 6 | 7 => arm_load_store_offset_addr 0 op1 rn op2
  | _ => arm_load_store_offset_addr 1 op1 rn op2
  end.

(* Get the il for loading halfwords *)
Definition arm_load_h_il cond op1 rn rt op2 bytes :=
  let offset_addr := arm_load_store_halfword_addr op1 rn op2 in
  let addr := match bitn op1 4 with
              | 0 => arm_var rn
              | _ => offset_addr
              end in
  let data := Load (Var V_MEM32) addr LittleE bytes in
  let wback := match bitn op1 4 with 
               | 0 => 1
               | _ => bitn op1 1
               end in
  match wback with
  | 1 => arm_cond cond (Seq (Move (arm_varid rt) data) (Move (arm_varid rn) offset_addr))
  | _ => arm_cond cond ((Move (arm_varid rt) data))
  end.

(*TODO: ldrt il traditionally has nullchecking for thumb but since we are not encoding thumb that will be a todo*)
Definition arm_load_store_il type byte cond A op1 rn rt op2 :=
  let offset_addr := arm_load_store_offset_addr A op1 rn op2 in
  let address := match bitn op1 4 with
                 | 0 => arm_var rn
                 | _ => offset_addr
                 end in
  let move_il := arm_load_store_move_il type byte rt address in
  match bitn op1 1, bitn op1 4 with
  | 0, 1 => arm_cond cond move_il
  | _, _ => arm_cond cond (Seq move_il (Move (arm_varid rn) offset_addr))
  end.

(* IL for data-processing instructions that have an equivalent IL binop, excluding flag setting *)
(* Save the result of the operation to V_TEMP 0 first,
   since if the destination is the same as one of the operands,
   it can mess up the flag computation. *)
Definition arm_data_binop binop i rn op2 :=
  (Move (V_TEMP 0) (BinOp binop (Var (arm_varid rn)) (arm_op2 i op2))).

(* IL for data-processing instructions that do not have an equivalent IL binop, excluding flag setting *)
Definition arm_data f i rn op2 :=
  (Move (V_TEMP 0) (f (Var (arm_varid rn)) (arm_op2 i op2))).

(* After flags have been set, the destination register can be updated *)
Definition arm_data_commit rd :=
  Move (arm_varid rd) (Var (V_TEMP 0)).

(* IL for setting flags *)
Definition arm_setzf :=
  Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0 32)).
Definition arm_setnf :=
  Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 0))).
Definition arm_setcf e1 e2 :=
  Move R_CF (BinOp OP_LT e2 e1).
Definition signof expr :=
  Cast CAST_HIGH 1 expr.
Definition samesign e1 e2 :=
  BinOp OP_EQ (signof e1) (signof e2).
Definition diffsign e1 e2 :=
  BinOp OP_NEQ (signof e1) (signof e2).
Definition overflow e1 e2 e3 :=
  BinOp OP_AND (samesign e1 e2) (diffsign e1 e3).
Definition arm_setvf e1 e2 e3 :=
  Move R_VF (overflow e1 e2 e3).

(* Sets the flags for an instruction using the ShiftC() pseudofunction *)
Definition arm_shiftc_flag i op2 :=
  Seq (arm_setzf) (Seq (arm_setnf) (Move R_CF (arm_op2_carry i op2))).
(* Sets the flags for an instruction using the AddWithCarry() pseudofunction *)
Definition arm_addwcarry_flag x y_plus_carryin :=
  Seq (arm_setzf) (Seq (arm_setnf) (Seq (arm_setcf x (Var (V_TEMP 0))) (arm_setvf x y_plus_carryin (Var (V_TEMP 0))))).

(* Turns a (data processing) instruction into the IL specifically for setting flags *)
Definition arm2flagil inst :=
  match inst with
  | ARM_AND cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_EOR cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_SUB cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_RSB cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_ADD cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (arm_op2 i op2)
  | ARM_ADC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (arm_op2 i op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_SBC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (UnOp OP_NOT (arm_op2 i op2)) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_RSC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (UnOp OP_NOT (arm_op2 i op2)) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_TST cond i   rn    op2 => arm_shiftc_flag i op2
  | ARM_TEQ cond i   rn    op2 => arm_shiftc_flag i op2
  | ARM_CMP cond i   rn    op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_CMN cond i   rn    op2 => arm_addwcarry_flag (arm_var rn) (arm_op2 i op2)
  | ARM_ORR cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_MOV cond i 1    rd op2 => arm_shiftc_flag i op2
  | ARM_BIC cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_MVN cond i 1    rd op2 => arm_shiftc_flag i op2
  | _ => Nop
  end.

Fixpoint arm_pushil (n : N) (i : nat) :=
  let sp := Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 4 32)) in
  let store := Move V_MEM32 (Store (Var V_MEM32) (Var R_SP) (arm_var (N.of_nat i)) LittleE 4) in
  match i, bitn n (N.of_nat i) with
  | O, 0 => Nop
  | O, _ => Seq sp store
  | S i', 0 => arm_pushil n i'
  | S i', _ => Seq sp (Seq store (arm_pushil n i'))
  end.
Fixpoint arm_popil (n : N) (i : nat) :=
  let sp := Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 4 32)) in
  let load := Move (arm_varid (15 - N.of_nat i)) (Load (Var V_MEM32) (Var R_SP) LittleE 4) in
  match i, bitn n (15 - N.of_nat i) with
  | O, 0 => Nop
  | O, _ => Seq load (Seq sp (Jmp (Var R_PC)))
  | S i', 0 => arm_popil n i'
  | S i', _ => Seq load (Seq sp (arm_popil n i'))
  end.

Definition arm2il (a:addr) inst :=
  match inst with
  | ARM_AND cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_AND i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_EOR cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_XOR i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_SUB cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_MINUS i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_RSB cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS op2 rn)) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_ADD cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_PLUS i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_ADC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_PLUS (BinOp OP_PLUS rn op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_SBC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS (BinOp OP_MINUS rn op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_RSC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS (BinOp OP_MINUS op2 rn) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_TST cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_AND i rn op2)
                                                  (arm2flagil inst))
  | ARM_TEQ cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_XOR i rn op2)
                                                  (arm2flagil inst))
  | ARM_CMP cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_MINUS i rn op2)
                                                  (arm2flagil inst))
  | ARM_CMN cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_PLUS i rn op2)
                                                  (arm2flagil inst))
  | ARM_ORR cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_OR i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_MOV cond i s    rd op2 => arm_cond cond (Seq (Move (V_TEMP 0) (arm_op2 i op2))
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_BIC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => BinOp OP_AND rn (UnOp OP_NOT op2)) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_MVN cond i s    rd op2 => arm_cond cond (Seq (Move (V_TEMP 0) (UnOp OP_NEG (arm_op2 i op2)))
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))

  | ARM_MOVT cond imm4 rd imm12 => arm_cond cond (Move (arm_varid rd) (BinOp OP_OR
                                                   (BinOp OP_AND (arm_var rd) (Word 0xffff 32))
                                                   (Word (N.shiftl (cbits imm4 12 imm12) 16) 32)))
  | ARM_MOVW cond imm4 rd imm12 => arm_cond cond (Move (arm_varid rd) (Word (cbits imm4 12 imm12) 32))

  | ARM_LDR cond A op1 rn B rt op2 => arm_load_store_il 0 0 cond A op1 rn rt op2
  | ARM_LDRT cond A op1 rn B rt op2 => arm_load_store_il 0 0 cond A op1 rn rt op2
  | ARM_LDRB cond A op1 rn B rt op2 => arm_load_store_il 0 1 cond A op1 rn rt op2
  | ARM_LDRBT cond A op1 rn B rt op2 => arm_load_store_il 0 1 cond A op1 rn rt op2

  | ARM_STR cond A op1 rn B rt op2 => arm_load_store_il 1 0 cond A op1 rn rt op2
  | ARM_STRT cond A op1 rn B rt op2 => arm_load_store_il 1 0 cond A op1 rn rt op2
  | ARM_STRB cond A op1 rn B rt op2 => arm_load_store_il 1 1 cond A op1 rn rt op2
  | ARM_STRBT cond A op1 rn B rt op2 => arm_load_store_il 1 1 cond A op1 rn rt op2

  | ARM_B cond imm24 => arm_cond cond (Jmp (Word (sbop1 Z.add 32 (a + 8) (scast 26 32 (N.shiftl imm24 2))) 32))
  | ARM_BL cond imm24 => arm_cond cond (Seq (Move R_LR (BinOp OP_MINUS (Var R_PC) (Word 4 32)))
                                           (Jmp (Word (sbop1 Z.add 32 (a + 8) (scast 26 32 (N.shiftl imm24 2))) 32)))
  | ARM_BLX cond rm => arm_cond cond (Seq (Move R_LR (BinOp OP_MINUS (Var R_PC) (Word 4 32))) (Jmp (arm_var rm))) 
  | ARM_BX cond rm => arm_cond cond (Jmp (arm_var rm))

  | ARM_POP cond regs => arm_cond cond (arm_popil regs 16)
  | ARM_PUSH cond regs => arm_cond cond (arm_pushil regs 16)
  
  | ARM_NOP cond => arm_cond cond Nop

  | ARM_SVC cond imm24 => arm_cond cond (Exn (imm24 mod 2^16))
  
  | _ => Exn 6
  end.

Definition arm_stmt m a :=
  arm2il a match a mod 4 with 0 => arm_decode (getmem 32 LittleE 4 m a) | _ => ARM_InvalidI end.

Definition arm_prog : program :=
  fun s a => Some (4, arm_stmt (getmem 32 LittleE 1 (s V_MEM32) a) a).

(* Well-typedness proof *)

(* The only temp variable used is V_TEMP 0, and it is always a NumT 32 *)
Definition arm7tempctx := arm7typctx[V_TEMP 0 := Some 32].

Ltac destruct_match :=
  repeat match goal with |- context [ match ?x with _ => _ end ] =>
    destruct x
  end.

Lemma has_type_xbits:
  forall n i j w c, 2 ^ (j - i) < 2 ^ w -> arm7typctx ⊆ c -> hastyp_exp c (Word (xbits n i j) w) (w).
Proof.
  intros. apply TWord. transitivity (2 ^ (j - i)). apply xbits_bound. assumption.
Qed.

Lemma update_some:
  forall x y (c c': typctx), c x = Some y -> c ⊆ c' -> c ⊆ c'[x := Some y].
Proof.
  intros. rewrite <- store_upd_eq. assumption. apply H0. assumption.
Qed.

Lemma arm7tempctx_subset:
  arm7typctx ⊆ arm7tempctx.
Proof.
  unfold pfsub. intros. unfold arm7tempctx. unfold update. destruct iseq. subst. discriminate. assumption.
Qed.

Lemma has_type_arm_cond:
  forall n stmt, hastyp_stmt arm7typctx arm7typctx stmt arm7typctx ->
    hastyp_stmt arm7typctx arm7typctx (arm_cond n stmt) arm7typctx.
Proof.
  intros. unfold arm_cond. destruct_match.
    all: repeat first
      [ apply TBinOp with (w := 1)
      | econstructor
      | reflexivity
      | apply H ].
Qed.

Lemma varid_type:
  forall n c, arm7typctx ⊆ c -> c (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. destruct_match; apply H; reflexivity.
Qed.

Lemma has_type_varid:
  forall n c, arm7typctx ⊆ c -> hastyp_exp c (Var (arm_varid n)) 32.
Proof.
  intros. apply TVar. apply varid_type. assumption.
Qed.

Lemma has_type_op2:
  forall i n c, arm7typctx ⊆ c -> hastyp_exp c (arm_op2 i n) 32.
Proof.
  intros. unfold arm_op2. destruct_match.
  13: apply TWord; rewrite N.land_comm; apply land_bound; reflexivity.
  all: repeat first
    [ apply TBinOp with (w := 32)
    | apply has_type_varid
    | apply has_type_xbits
    | constructor
    | reflexivity
    | destruct (xbits _ 4 5)
    | assumption ].
Qed.

Lemma has_type_setzf:
  hastyp_stmt arm7typctx arm7tempctx arm_setzf arm7tempctx.
Proof.
  unfold arm_setzf. eapply TMove.
    right. reflexivity.
    apply TBinOp with (w := 32).
      apply TVar; reflexivity.
      apply TWord; reflexivity.
    apply update_some; reflexivity.
Qed.

Lemma has_type_setnf:
  hastyp_stmt arm7typctx arm7tempctx arm_setnf arm7tempctx.
Proof.
  unfold arm_setnf. eapply TMove.
    right; reflexivity.
    apply TCast with (w:=32).
      apply TVar; reflexivity.
      apply N.lt_le_incl; reflexivity.
    apply update_some; reflexivity.
Qed.

Lemma has_type_data_binop:
  forall bop n1 n2 n3, hastyp_stmt arm7typctx arm7typctx (arm_data_binop bop n1 n2 n3)
                         (arm7typctx[V_TEMP 0 := Some (widthof_binop bop 32)]).
Proof.
  intros. unfold arm_data_binop. eapply TMove.
    left; reflexivity.
    apply TBinOp.
      apply has_type_varid; reflexivity.
      apply has_type_op2; reflexivity.
    reflexivity.
Qed.

Lemma lt_sub:
  forall x y z, x < y -> x - z < y.
Proof.
  intros. assert (x - z <= x). apply N.le_sub_l.
  rewrite N.le_lteq in H0. destruct H0.
    transitivity x; assumption.
    rewrite H0; assumption.
Qed.

Lemma has_type_shiftc:
  forall i op2, hastyp_stmt arm7typctx arm7tempctx (arm_shiftc_flag i op2) arm7tempctx.
Proof.
  intros. unfold arm_shiftc_flag. eapply TSeq. 3: reflexivity.
    apply has_type_setzf.
    eapply TSeq. 3: reflexivity.
      apply has_type_setnf.
      eapply TMove. 3: apply update_some; reflexivity.
        right; reflexivity.
        unfold arm_op2_carry. destruct_match.
          all: repeat first 
            [ apply TBinOp with (w := 32)
            | econstructor
            | apply N.lt_le_incl
            | apply varid_type
            | apply arm7tempctx_subset
            | reflexivity ].
          all: apply lt_sub; transitivity (2 ^ 5); solve [ apply xbits_bound | reflexivity ].
Qed.

Lemma has_type_data_commit:
  forall n, hastyp_stmt arm7typctx arm7tempctx (arm_data_commit n) arm7typctx.
Proof.
  intros. unfold arm_data_commit. apply TMove with (w := 32).
    right; apply varid_type; reflexivity.
    apply TVar; reflexivity.
    apply update_some.
      apply varid_type; reflexivity.
      apply arm7tempctx_subset.
Qed.

Lemma has_type_signof:
  forall e, hastyp_exp arm7tempctx e 32 -> hastyp_exp arm7tempctx (signof e) 1.
Proof.
  intros. unfold signof. apply TCast with (w := 32).
    assumption.
    apply N.lt_le_incl; reflexivity.
Qed.

Lemma has_type_addwcarry_flag:
  forall n e, hastyp_exp arm7tempctx e 32 -> hastyp_stmt arm7typctx arm7tempctx
    (arm_addwcarry_flag (arm_var n) e)
    arm7tempctx.
Proof.
  intros. unfold arm_addwcarry_flag. eapply TSeq with (c2 := arm7tempctx).
    apply has_type_setzf. 2: reflexivity.
  eapply TSeq with (c2 := arm7tempctx).
    apply has_type_setnf. 2: reflexivity.
  eapply TSeq with (c1 := arm7tempctx) (c2 := arm7tempctx).
    unfold arm_setcf. eapply TMove.
      right; reflexivity.
      apply TBinOp with (w := 32).
        eapply TVar; reflexivity.
        apply has_type_varid; apply arm7tempctx_subset.
      apply update_some; reflexivity.
    unfold arm_setvf. eapply TMove.
      right; reflexivity.
      unfold overflow. apply TBinOp with (w := 1).
        unfold samesign. apply TBinOp with (w := 1).
          apply has_type_signof. apply has_type_varid. apply arm7tempctx_subset.
          apply has_type_signof. apply H.
        unfold diffsign. apply TBinOp with (w := 1).
          apply has_type_signof. apply has_type_varid. apply arm7tempctx_subset.
          apply has_type_signof. apply TVar. reflexivity.
      apply update_some. all: reflexivity.
Qed.

Lemma has_type_flagil:
  forall i, hastyp_stmt arm7typctx arm7tempctx (arm2flagil i) arm7tempctx.
Proof.
  intros. unfold arm2flagil. destruct_match.
    all: repeat first
      [ apply has_type_shiftc
      | apply has_type_addwcarry_flag
      | apply has_type_op2
      | apply TBinOp with (w := 32)
      | apply N.lt_le_incl
      | econstructor
      | reflexivity
      | apply arm7tempctx_subset ].
Qed.

Lemma has_type_data_op:
  forall a n1 n2 n3 n4 n5 n6 n7,
    hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_data_opcode n1 n2 n3 n4 n5 n6 n7)) arm7typctx.
Proof.
  intros. unfold arm_data_opcode. destruct_match.
    all: unfold arm2il.
    all: repeat first
      [ apply has_type_arm_cond
      | apply has_type_flagil
      | apply has_type_data_commit
      | reflexivity
      | constructor
      | apply arm7tempctx_subset
      | eapply TSeq ].
    all: try apply has_type_data_binop. all: unfold arm_data.
    all: repeat first
      [ econstructor
      | apply has_type_op2
      | apply varid_type
      | reflexivity
      | apply N.lt_le_incl ].
Qed.

Lemma has_type_extra_load_store:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_extra_load_store n)) arm7typctx.
Proof.
  intros. unfold arm_decode_extra_load_store. destruct_match.
    all: unfold arm2il; constructor; reflexivity.
Qed.
Lemma has_type_mul_and_sync:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_mul_and_sync n)) arm7typctx.
Proof.
  intros. unfold arm_decode_mul_and_sync. constructor. reflexivity.
Qed.

Lemma has_type_data:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_data n)) arm7typctx.
Proof.
  intros. unfold arm_decode_data, arm_decode_misc. destruct_match.
    all: try solve [ apply has_type_data_op | apply has_type_extra_load_store | apply has_type_mul_and_sync ] .
    all: unfold arm2il; apply has_type_arm_cond.
    all: try eapply TJmp; try apply has_type_varid; try reflexivity.
    apply TMove with (w := 32).
      right; apply varid_type; reflexivity.
      repeat apply TBinOp with (w := 32).
        apply has_type_varid; reflexivity.
        apply TWord; reflexivity.
        apply TWord. unfold cbits. rewrite N.shiftl_lor. apply lor_bound.
          rewrite N.shiftl_shiftl. apply (shiftl_bound 4 _ 28). apply xbits_bound.
          transitivity (2 ^ 28). apply (shiftl_bound 12 _ 16). apply xbits_bound. reflexivity.
      apply update_some. apply varid_type. 1, 2: reflexivity.
    apply TMove with (w := 32).
      right; apply varid_type; reflexivity.
      apply TWord. unfold cbits. apply lor_bound.
        transitivity (2 ^ 16). apply (shiftl_bound 4 _ 12). apply xbits_bound. reflexivity.
        transitivity (2 ^ 12). apply xbits_bound. reflexivity.
      apply update_some. apply varid_type. all: reflexivity.
Qed.

Lemma has_type_load_store_offset_addr:
  forall n1 n2 n3 n4, hastyp_exp arm7typctx
    (arm_load_store_offset_addr n1 n2 n3 n4) 32.
Proof.
  intros. unfold arm_load_store_offset_addr. destruct_match.
    all: apply TBinOp with (w := 32);
      first [ apply has_type_xbits | apply has_type_varid | apply has_type_op2 ];
      reflexivity.
Qed.

Lemma has_type_load_store_move_il:
  forall n1 n2 n3 e, hastyp_exp arm7typctx e 32 -> hastyp_stmt arm7typctx arm7typctx
    (arm_load_store_move_il n1 n2 n3 e) arm7typctx.
Proof.
  intros. unfold arm_load_store_move_il. destruct_match.
    all: repeat first
        [ right
        | eapply TMove
        | eapply TStore with (w := 32)
        | eapply TLoad with (w := 32)
        | apply varid_type
        | apply update_some
        | reflexivity
        | assumption ].
    3: apply TCast with (w := 8).
    3: apply TLoad with (w := 32).
    12: apply TCast with (w := 32).
    all: repeat first [ apply N.lt_le_incl | constructor | apply varid_type | reflexivity | assumption ].
Qed.

Lemma has_type_load_store_il:
  forall n1 n2 n3 n4 n5 n6 n7 n8, hastyp_stmt arm7typctx arm7typctx
    (arm_load_store_il n1 n2 n3 n4 n5 n6 n7 n8) arm7typctx.
Proof.
  intros. unfold arm_load_store_il. destruct_match.
    all: repeat first
        [ apply has_type_arm_cond
        | apply has_type_load_store_move_il
        | apply has_type_load_store_offset_addr
        | apply varid_type
        | right
        | econstructor
        | reflexivity ].
    all: apply update_some; try apply varid_type; reflexivity.
Qed.

Theorem has_type_load_store:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_load_and_store n)) arm7typctx.
Proof.
  intros. unfold arm_decode_load_and_store. unfold arm_load_and_store_opcode. destruct_match.
  all: try apply has_type_load_store_il.
  all: unfold arm2il; constructor; reflexivity.
Qed.

Lemma has_type_pop:
  forall n i, hastyp_stmt arm7typctx arm7typctx (arm_popil n i) arm7typctx.
Proof.
  induction i.
    unfold arm_popil. destruct_match.
      constructor; reflexivity.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ]; reflexivity.
    unfold arm_popil; fold arm_popil. destruct_match.
      assumption.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
      3: rewrite <- store_upd_eq; try apply varid_type. 1-4: reflexivity.
      repeat rewrite <- store_upd_eq. assumption. 1, 3: apply varid_type. all: reflexivity.
Qed.

Lemma has_type_push:
  forall n i, hastyp_stmt arm7typctx arm7typctx (arm_pushil n i) arm7typctx.
Proof.
  induction i.
    unfold arm_pushil. destruct_match.
      constructor; reflexivity.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | eapply TStore with (w := 32)
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
    unfold arm_pushil; fold arm_pushil. destruct_match.
      assumption.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | eapply TStore with (w := 32)
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
       repeat rewrite <- store_upd_eq. assumption. all: reflexivity.
Qed.

Lemma has_type_branch:
  forall a n, hastyp_stmt arm7typctx arm7typctx
    (arm2il a (arm_decode_branch n)) arm7typctx.
Proof.
  intros. unfold arm_decode_branch. destruct_match.
    all: unfold arm2il; try constructor; try reflexivity.
    all: apply has_type_arm_cond.
    all: repeat first
      [ apply TBinOp with (w := 32)
      | right
      | econstructor
      | reflexivity
      | apply update_some
      | apply varid_type ].
    all: solve [ apply ofZ_bound | apply has_type_pop | apply has_type_push ].
Qed.

(*
Lemma has_type_unconditional:
  forall a n, hastyp_stmt arm7typctx arm7typctx
    (arm2il a (arm_decode_unconditional n)) arm7typctx.
Proof.
  intros. unfold arm_decode_unconditional. destruct_match.
    all: constructor; reflexivity.
Qed.

 *)
Theorem welltyped_arm2il:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode n)) arm7typctx.
Proof.
  intros. unfold arm_decode. destruct_match.
    all: try constructor; try reflexivity.
    all: solve  (* this seems to spin forever if a and n are not given *)
      [ apply (has_type_load_store a n)
      | apply (has_type_data a n)
      | apply (has_type_branch a n)
      | apply (has_type_unconditional a n) ].
Qed.

Theorem welltyped_arm_prog:
  welltyped_prog arm7typctx arm_prog.
Proof.
  intros s a. unfold arm_prog. 
    exists arm7typctx. unfold arm_stmt. destruct (a mod 4).
      apply welltyped_arm2il.
      constructor. reflexivity.
Qed.
