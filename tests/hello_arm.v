Add LoadPath "H:\coq\CoqBAP-test\CoqBAP-test".
Require Import Bap_ARM_32.
Import Bap_ARM_32.
Require Import NArith.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x10315: svcmi #0xb00f0 *)
| 66325%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_NF) (NumT 1))) (Word 1%N 1)) (
      CpuExn 721136
    ) (* else *) (
      Nop
    )
  )

(* 0x10319: andeq r0, lr, #240 *)
| 66329%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_ZF) (NumT 1))) (Word 1%N 1)) (
      Move (Va (R_R0) (NumT 32)) (BinOp OP_AND (Var (Va (R_LR) (NumT 32))) (Word 240%N 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x1031d: strbeq r6, [r6], #-2748 *)
| 66333%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_ZF) (NumT 1))) (Word 1%N 1)) ( 
      Move (Va (V_TEMP (0%N) (* v29 *)) (NumT 8)) (Cast CAST_LOW 8 (Var (Va (R_R6) (NumT 32)))) $;
      Move (Va (V_MEM32) (MemT 32)) (Store (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_R6) (NumT 32))) (Var (Va (V_TEMP (0%N) (* v29 *)) (NumT 8))) LittleE 1) $;
      Move (Va (R_R6) (NumT 32)) (BinOp OP_PLUS (Var (Va (R_R6) (NumT 32))) (Word 4294964548%N 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x10321: svcle #0xb401b4 *)
| 66337%N => Some (4,
    If (BinOp OP_OR (BinOp OP_EQ (Var (Va (R_ZF) (NumT 1))) (Word 1%N 1)) (BinOp OP_NEQ (Var (Va (R_NF) (NumT 1))) (Var (Va (R_VF) (NumT 1))))) (
      CpuExn 11796916
    ) (* else *) (
      Nop
    )
  )

(* 0x103f4: svcge #0xb580 *)
| 66548%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_NF) (NumT 1))) (Var (Va (R_VF) (NumT 1)))) (
      CpuExn 46464
    ) (* else *) (
      Nop
    )
  )

(* 0x103f8: subsmi pc, r8, r0, asr #4 *)
| 66552%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_NF) (NumT 1))) (Word 1%N 1)) ( 
      Move (Va (V_TEMP (1%N) (* v32 *)) (NumT 32)) (Var (Va (R_R0) (NumT 32))) $;
      Move (Va (V_TEMP (2%N) (* v33 *)) (NumT 32)) (Var (Va (R_R8) (NumT 32))) $;
      Move (Va (V_TEMP (3%N) (* v34 *)) (NumT 32)) (BinOp OP_ARSHIFT (Var (Va (V_TEMP (1%N) (* v32 *)) (NumT 32))) (Word 4%N 32)) $;
      Jmp (BinOp OP_MINUS (Var (Va (R_R8) (NumT 32))) (BinOp OP_ARSHIFT (Var (Va (V_TEMP (1%N) (* v32 *)) (NumT 32))) (Word 4%N 32))) $;
      Move (Va (R_CF) (NumT 1)) (BinOp OP_LE (Var (Va (V_TEMP (3%N) (* v34 *)) (NumT 32))) (Var (Va (V_TEMP (2%N) (* v33 *)) (NumT 32)))) $;
      Move (Va (R_VF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (2%N) (* v33 *)) (NumT 32))) (Var (Va (V_TEMP (3%N) (* v34 *)) (NumT 32)))) (BinOp OP_XOR (Var (Va (V_TEMP (2%N) (* v33 *)) (NumT 32))) (Word 66560%N 32)))) $;
      Move (Va (R_NF) (NumT 1)) (Word 0%N 1) $;
      Move (Va (R_ZF) (NumT 1)) (Word 0%N 1)
    ) (* else *) (
      Nop
    )
  )

(* 0x103fc: andeq pc, r1, r0, asr #5 *)
| 66556%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_ZF) (NumT 1))) (Word 1%N 1)) ( 
      Move (Va (V_TEMP (4%N) (* v24 *)) (NumT 32)) (Var (Va (R_R0) (NumT 32))) $;
      Jmp (BinOp OP_AND (Var (Va (R_R1) (NumT 32))) (BinOp OP_ARSHIFT (Var (Va (V_TEMP (4%N) (* v24 *)) (NumT 32))) (Word 5%N 32)))
    ) (* else *) (
      Nop
    )
  )

(* 0x10400: svc #0x70f7ff *)
| 66560%N => Some (4,
    CpuExn 7403519
  )

(* 0x10404: ldrmi r2, [r8], -r0, lsl #6 *)
| 66564%N => Some (4,
    If (BinOp OP_EQ (Var (Va (R_NF) (NumT 1))) (Word 1%N 1)) ( 
      Move (Va (R_R2) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_R8) (NumT 32))) LittleE 4) $;
      Move (Va (R_R8) (NumT 32)) (BinOp OP_PLUS (Var (Va (R_R8) (NumT 32))) (BinOp OP_TIMES (Word 4294967295%N 32) (BinOp OP_LSHIFT (Var (Va (R_R0) (NumT 32))) (Word 6%N 32))))
    ) (* else *) (
      Nop
    )
  )

(* 0x10408: svclt #0xbd80 *)
| 66568%N => Some (4,
    If (BinOp OP_NEQ (Var (Va (R_NF) (NumT 1))) (Var (Va (R_VF) (NumT 1)))) (
      CpuExn 48512
    ) (* else *) (
      Nop
    )
  )

(* 0x10448: svclt #0x4770 *)
| 66632%N => Some (4,
    If (BinOp OP_NEQ (Var (Va (R_NF) (NumT 1))) (Var (Va (R_VF) (NumT 1)))) (
      CpuExn 18288
    ) (* else *) (
      Nop
    )
  )

(* 0x1044c: push {r3, lr} *)
| 66636%N => Some (4, 
    Move (Va (V_TEMP (5%N) (* v40 *)) (NumT 32)) (Var (Va (R_SP) (NumT 32))) $;
    Move (Va (V_MEM32) (MemT 32)) (Store (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Var (Va (V_TEMP (5%N) (* v40 *)) (NumT 32))) (Word 4294967292%N 32)) (Var (Va (R_LR) (NumT 32))) LittleE 4) $;
    Move (Va (V_MEM32) (MemT 32)) (Store (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Var (Va (V_TEMP (5%N) (* v40 *)) (NumT 32))) (Word 4294967288%N 32)) (Var (Va (R_R3) (NumT 32))) LittleE 4) $;
    Move (Va (R_SP) (NumT 32)) (BinOp OP_MINUS (Var (Va (R_SP) (NumT 32))) (Word 8%N 32))
  )

(* 0x10450: pop {r3, pc} *)
| 66640%N => Some (4, 
    Move (Va (V_TEMP (6%N) (* v42 *)) (NumT 32)) (Var (Va (R_SP) (NumT 32))) $;
    Move (Va (R_R3) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (V_TEMP (6%N) (* v42 *)) (NumT 32))) LittleE 4) $;
    Move (Va (R_SP) (NumT 32)) (BinOp OP_PLUS (Var (Va (R_SP) (NumT 32))) (Word 8%N 32)) $;
    Jmp (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Var (Va (V_TEMP (6%N) (* v42 *)) (NumT 32))) (Word 4%N 32)) LittleE 4)
  )

| _ => None
end.
