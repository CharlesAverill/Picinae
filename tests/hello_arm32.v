Add LoadPath "..".
Require Import Picinae_armv7.
Import PArch_armv7.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x10315: svcmi #0xb00f0 *)
| 66325 => Some (4,
    If (BinOp OP_EQ (Var R_NF) (Word 1 1)) (
      CpuExn 721136
    ) (* else *) (
      Nop
    )
  )

(* 0x10319: andeq r0, lr, #240 *)
| 66329 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Move R_R0 (BinOp OP_AND (Var R_LR) (Word 240 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x1031d: strbeq r6, [r6], #-2748 *)
| 66333 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) ( 
      Move (V_TEMP 0 (* v29 *)) (Cast CAST_LOW 8 (Var R_R6)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R6) (Var (V_TEMP 0 (* v29 *))) LittleE 1) $;
      Move R_R6 (BinOp OP_PLUS (Var R_R6) (Word 4294964548 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x10321: svcle #0xb401b4 *)
| 66337 => Some (4,
    If (BinOp OP_OR (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (BinOp OP_NEQ (Var R_NF) (Var R_VF))) (
      CpuExn 11796916
    ) (* else *) (
      Nop
    )
  )

(* 0x103f4: svcge #0xb580 *)
| 66548 => Some (4,
    If (BinOp OP_EQ (Var R_NF) (Var R_VF)) (
      CpuExn 46464
    ) (* else *) (
      Nop
    )
  )

(* 0x103f8: subsmi pc, r8, r0, asr #4 *)
| 66552 => Some (4,
    If (BinOp OP_EQ (Var R_NF) (Word 1 1)) ( 
      Move (V_TEMP 1 (* v32 *)) (Var R_R0) $;
      Move (V_TEMP 2 (* v33 *)) (Var R_R8) $;
      Move (V_TEMP 3 (* v34 *)) (BinOp OP_ARSHIFT (Var (V_TEMP 1 (* v32 *))) (Word 4 32)) $;
      Jmp (BinOp OP_MINUS (Var R_R8) (BinOp OP_ARSHIFT (Var (V_TEMP 1 (* v32 *))) (Word 4 32))) $;
      Move R_CF (BinOp OP_LE (Var (V_TEMP 3 (* v34 *))) (Var (V_TEMP 2 (* v33 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 2 (* v33 *))) (Var (V_TEMP 3 (* v34 *)))) (BinOp OP_XOR (Var (V_TEMP 2 (* v33 *))) (Word 66560 32)))) $;
      Move R_NF (Word 0 1) $;
      Move R_ZF (Word 0 1)
    ) (* else *) (
      Nop
    )
  )

(* 0x103fc: andeq pc, r1, r0, asr #5 *)
| 66556 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) ( 
      Move (V_TEMP 4 (* v24 *)) (Var R_R0) $;
      Jmp (BinOp OP_AND (Var R_R1) (BinOp OP_ARSHIFT (Var (V_TEMP 4 (* v24 *))) (Word 5 32)))
    ) (* else *) (
      Nop
    )
  )

(* 0x10400: svc #0x70f7ff *)
| 66560 => Some (4,
    CpuExn 7403519
  )

(* 0x10404: ldrmi r2, [r8], -r0, lsl #6 *)
| 66564 => Some (4,
    If (BinOp OP_EQ (Var R_NF) (Word 1 1)) ( 
      Move R_R2 (Load (Var V_MEM32) (Var R_R8) LittleE 4) $;
      Move R_R8 (BinOp OP_PLUS (Var R_R8) (BinOp OP_TIMES (Word 4294967295 32) (BinOp OP_LSHIFT (Var R_R0) (Word 6 32))))
    ) (* else *) (
      Nop
    )
  )

(* 0x10408: svclt #0xbd80 *)
| 66568 => Some (4,
    If (BinOp OP_NEQ (Var R_NF) (Var R_VF)) (
      CpuExn 48512
    ) (* else *) (
      Nop
    )
  )

(* 0x10448: svclt #0x4770 *)
| 66632 => Some (4,
    If (BinOp OP_NEQ (Var R_NF) (Var R_VF)) (
      CpuExn 18288
    ) (* else *) (
      Nop
    )
  )

(* 0x1044c: push {r3, lr} *)
| 66636 => Some (4, 
    Move (V_TEMP 5 (* v40 *)) (Var R_SP) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 5 (* v40 *))) (Word 4294967292 32)) (Var R_LR) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 5 (* v40 *))) (Word 4294967288 32)) (Var R_R3) LittleE 4) $;
    Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 8 32))
  )

(* 0x10450: pop {r3, pc} *)
| 66640 => Some (4, 
    Move (V_TEMP 6 (* v42 *)) (Var R_SP) $;
    Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP 6 (* v42 *))) LittleE 4) $;
    Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 8 32)) $;
    Jmp (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 6 (* v42 *))) (Word 4 32)) LittleE 4)
  )

| _ => None
end.
