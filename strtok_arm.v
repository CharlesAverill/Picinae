Require Import Picinae_armv7.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition strtok_arm : program := fun _ a => match a with

(* 0xc0000034: push {r4, r5, r6, lr} *)
| 0 => Some (4, 
    Move (V_TEMP 0 (* v66 *)) (Var R_SP) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 0 (* v66 *))) (Word 4294967292 32)) (Var R_LR) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 0 (* v66 *))) (Word 4294967288 32)) (Var R_R6) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 0 (* v66 *))) (Word 4294967284 32)) (Var R_R5) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 0 (* v66 *))) (Word 4294967280 32)) (Var R_R4) LittleE 4) $;
    Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 16 32))
  )

(* 0xc0000038: ldr r6, [pc, #0x60] *)
| 4 => Some (4,
    Move R_R6 (Load (Var V_MEM32) (Word 3221225632 32) LittleE 4)
  )

(* 0xc000003c: subs r4, r0, #0 *)
| 8 => Some (4, 
    Move (V_TEMP 1 (* v69 *)) (Var R_R0) $;
    Move R_R4 (Var R_R0) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 1 (* v69 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 1 (* v69 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 1 (* v69 *))) (Var R_R4)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R4)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R4) (Word 0 32))
  )

(* 0xc0000040: ldreq r4, [r6] *)
| 12 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Move R_R4 (Load (Var V_MEM32) (Var R_R6) LittleE 4)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000044: mov r5, r1 *)
| 16 => Some (4,
    Move R_R5 (Var R_R1)
  )

(* 0xc0000048: mov r0, r4 *)
| 20 => Some (4,
    Move R_R0 (Var R_R4)
  )

(* 0xc000004c: bl #-0x8 *)
| 24 => Some (4, 
    Move R_LR (Word 3221225552 32) $;
    Jmp (Word 24 32)
  )

(* 0xc0000050: ldrb r3, [r4, r0] *)
| 28 => Some (4, 
    Move (V_TEMP 2 (* v75 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_R4) (Var R_R0)) LittleE 1) $;
    Move R_R3 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2 (* v75 *))))
  )

(* 0xc0000054: add r4, r4, r0 *)
| 32 => Some (4,
    Move R_R4 (BinOp OP_PLUS (Var R_R4) (Var R_R0))
  )

(* 0xc0000058: cmp r3, #0 *)
| 36 => Some (4, 
    Move (V_TEMP 3 (* v81 *)) (Var R_R3) $;
    Move (V_TEMP 4 (* v79 *)) (Var R_R3) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 3 (* v81 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 3 (* v81 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 3 (* v81 *))) (Var (V_TEMP 4 (* v79 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v79 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 4 (* v79 *))) (Word 0 32))
  )

(* 0xc000005c: streq r4, [r6] *)
| 40 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R6) (Var R_R4) LittleE 4)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000060: moveq r4, r3 *)
| 44 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Move R_R4 (Var R_R3)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000064: beq #0x1c *)
| 48 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 84 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000068: mov r1, r5 *)
| 52 => Some (4,
    Move R_R1 (Var R_R5)
  )

(* 0xc000006c: mov r0, r4 *)
| 56 => Some (4,
    Move R_R0 (Var R_R4)
  )

(* 0xc0000070: bl #-0x8 *)
| 60 => Some (4, 
    Move R_LR (Word 3221225588 32) $;
    Jmp (Word 60 32)
  )

(* 0xc0000074: subs r1, r0, #0 *)
| 64 => Some (4, 
    Move (V_TEMP 5 (* v88 *)) (Var R_R0) $;
    Move R_R1 (Var R_R0) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 5 (* v88 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 5 (* v88 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 5 (* v88 *))) (Var R_R1)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R1)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R1) (Word 0 32))
  )

(* 0xc0000078: movne r3, #0 *)
| 68 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Move R_R3 (Word 0 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007c: strbne r3, [r1], #1 *)
| 72 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 6 (* v92 *)) (Cast CAST_LOW 8 (Var R_R3)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R1) (Var (V_TEMP 6 (* v92 *))) LittleE 1) $;
      Move R_R1 (BinOp OP_PLUS (Var R_R1) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000080: strne r1, [r6] *)
| 76 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R6) (Var R_R1) LittleE 4)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000084: beq #0x4 *)
| 80 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 92 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000088: mov r0, r4 *)
| 84 => Some (4,
    Move R_R0 (Var R_R4)
  )

(* 0xc000008c: pop {r4, r5, r6, pc} *)
| 88 => Some (4, 
    Move (V_TEMP 7 (* v65 *)) (Var R_SP) $;
    Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP 7 (* v65 *))) LittleE 4) $;
    Move R_R5 (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 7 (* v65 *))) (Word 4 32)) LittleE 4) $;
    Move R_R6 (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 7 (* v65 *))) (Word 8 32)) LittleE 4) $;
    Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 16 32)) $;
    Jmp (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 7 (* v65 *))) (Word 12 32)) LittleE 4)
  )

(* 0xc0000090: mov r0, r4 *)
| 92 => Some (4,
    Move R_R0 (Var R_R4)
  )

(* 0xc0000094: bl #-0x8 *)
| 96 => Some (4, 
    Move R_LR (Word 3221225624 32) $;
    Jmp (Word 96 32)
  )

(* 0xc0000098: str r0, [r6] *)
| 100 => Some (4,
    Move V_MEM32 (Store (Var V_MEM32) (Var R_R6) (Var R_R0) LittleE 4)
  )

(* 0xc000009c: b #-0x1c *)
| 104 => Some (4,
    Jmp (Word 84 32)
  )

| _ => None
end.
