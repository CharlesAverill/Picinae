Require Import Picinae_armv7.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition strspn_arm : program := fun _ a => match a with

(* 0xc0000034: ldrb r12, [r0] *)
| 0 => Some (4, 
    Move (V_TEMP 0 (* v91 *)) (Load (Var V_MEM32) (Var R_R0) LittleE 1) $;
    Move R_R12 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0 (* v91 *))))
  )

(* 0xc0000038: cmp r12, #0 *)
| 4 => Some (4, 
    Move (V_TEMP 1 (* v94 *)) (Var R_R12) $;
    Move (V_TEMP 2 (* v92 *)) (Var R_R12) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 1 (* v94 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 1 (* v94 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 1 (* v94 *))) (Var (V_TEMP 2 (* v92 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v92 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2 (* v92 *))) (Word 0 32))
  )

(* 0xc000003c: beq #0x50 *)
| 8 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 96 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000040: push {r4, lr} *)
| 12 => Some (4, 
    Move (V_TEMP 3 (* v85 *)) (Var R_SP) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 3 (* v85 *))) (Word 4294967292 32)) (Var R_LR) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 3 (* v85 *))) (Word 4294967288 32)) (Var R_R4) LittleE 4) $;
    Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 8 32))
  )

(* 0xc0000044: mov lr, r0 *)
| 16 => Some (4,
    Move R_LR (Var R_R0)
  )

(* 0xc0000048: mov r0, #0 *)
| 20 => Some (4,
    Move R_R0 (Word 0 32)
  )

(* 0xc000004c: ldrb r4, [r1] *)
| 24 => Some (4, 
    Move (V_TEMP 4 (* v89 *)) (Load (Var V_MEM32) (Var R_R1) LittleE 1) $;
    Move R_R4 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4 (* v89 *))))
  )

(* 0xc0000050: cmp r4, #0 *)
| 28 => Some (4, 
    Move (V_TEMP 5 (* v109 *)) (Var R_R4) $;
    Move (V_TEMP 6 (* v107 *)) (Var R_R4) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 5 (* v109 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 5 (* v109 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 5 (* v109 *))) (Var (V_TEMP 6 (* v107 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v107 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 6 (* v107 *))) (Word 0 32))
  )

(* 0xc0000054: popeq {r4, pc} *)
| 32 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) ( 
      Move (V_TEMP 7 (* v111 *)) (Var R_SP) $;
      Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP 7 (* v111 *))) LittleE 4) $;
      Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 8 32)) $;
      Jmp (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 7 (* v111 *))) (Word 4 32)) LittleE 4)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000058: cmp r4, r12 *)
| 36 => Some (4, 
    Move (V_TEMP 8 (* v98 *)) (Var R_R4) $;
    Move (V_TEMP 9 (* v99 *)) (Var R_R12) $;
    Move (V_TEMP 10 (* v96 *)) (BinOp OP_MINUS (Var R_R4) (Var R_R12)) $;
    Move R_CF (BinOp OP_LE (Var (V_TEMP 9 (* v99 *))) (Var (V_TEMP 8 (* v98 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 8 (* v98 *))) (Var (V_TEMP 9 (* v99 *)))) (BinOp OP_XOR (Var (V_TEMP 8 (* v98 *))) (Var (V_TEMP 10 (* v96 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v96 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 10 (* v96 *))) (Word 0 32))
  )

(* 0xc000005c: beq #0x1c *)
| 40 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 76 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000060: mov r2, r1 *)
| 44 => Some (4,
    Move R_R2 (Var R_R1)
  )

(* 0xc0000064: b #0x4 *)
| 48 => Some (4,
    Jmp (Word 60 32)
  )

(* 0xc0000068: cmp r3, r12 *)
| 52 => Some (4, 
    Move (V_TEMP 11 (* v114 *)) (Var R_R3) $;
    Move (V_TEMP 12 (* v115 *)) (Var R_R12) $;
    Move (V_TEMP 13 (* v112 *)) (BinOp OP_MINUS (Var R_R3) (Var R_R12)) $;
    Move R_CF (BinOp OP_LE (Var (V_TEMP 12 (* v115 *))) (Var (V_TEMP 11 (* v114 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 11 (* v114 *))) (Var (V_TEMP 12 (* v115 *)))) (BinOp OP_XOR (Var (V_TEMP 11 (* v114 *))) (Var (V_TEMP 13 (* v112 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 13 (* v112 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 13 (* v112 *))) (Word 0 32))
  )

(* 0xc000006c: beq #0xc *)
| 56 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 76 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000070: ldrb r3, [r2, #0x1]! *)
| 60 => Some (4, 
    Move (V_TEMP 14 (* v101 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_R2) (Word 1 32)) LittleE 1) $;
    Move R_R3 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 14 (* v101 *)))) $;
    Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 1 32))
  )

(* 0xc0000074: cmp r3, #0 *)
| 64 => Some (4, 
    Move (V_TEMP 15 (* v104 *)) (Var R_R3) $;
    Move (V_TEMP 16 (* v102 *)) (Var R_R3) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 15 (* v104 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 15 (* v104 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 15 (* v104 *))) (Var (V_TEMP 16 (* v102 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v102 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 16 (* v102 *))) (Word 0 32))
  )

(* 0xc0000078: bne #-0x18 *)
| 68 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Jmp (Word 52 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007c: pop {r4, pc} *)
| 72 => Some (4, 
    Move (V_TEMP 17 (* v106 *)) (Var R_SP) $;
    Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP 17 (* v106 *))) LittleE 4) $;
    Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 8 32)) $;
    Jmp (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 17 (* v106 *))) (Word 4 32)) LittleE 4)
  )

(* 0xc0000080: ldrb r12, [lr, #0x1]! *)
| 76 => Some (4, 
    Move (V_TEMP 18 (* v117 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_LR) (Word 1 32)) LittleE 1) $;
    Move R_R12 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 18 (* v117 *)))) $;
    Move R_LR (BinOp OP_PLUS (Var R_LR) (Word 1 32))
  )

(* 0xc0000084: add r0, r0, #1 *)
| 80 => Some (4,
    Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 1 32))
  )

(* 0xc0000088: cmp r12, #0 *)
| 84 => Some (4, 
    Move (V_TEMP 19 (* v123 *)) (Var R_R12) $;
    Move (V_TEMP 20 (* v121 *)) (Var R_R12) $;
    Move R_CF (BinOp OP_LE (Word 0 32) (Var (V_TEMP 19 (* v123 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 19 (* v123 *))) (Word 0 32)) (BinOp OP_XOR (Var (V_TEMP 19 (* v123 *))) (Var (V_TEMP 20 (* v121 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 20 (* v121 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 20 (* v121 *))) (Word 0 32))
  )

(* 0xc000008c: bne #-0x44 *)
| 88 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Jmp (Word 28 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000090: pop {r4, pc} *)
| 92 => Some (4, 
    Move (V_TEMP 21 (* v126 *)) (Var R_SP) $;
    Move R_R4 (Load (Var V_MEM32) (Var (V_TEMP 21 (* v126 *))) LittleE 4) $;
    Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 8 32)) $;
    Jmp (Load (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 21 (* v126 *))) (Word 4 32)) LittleE 4)
  )

(* 0xc0000094: mov r0, r12 *)
| 96 => Some (4,
    Move R_R0 (Var R_R12)
  )

(* 0xc0000098: bx lr *)
| 100 => Some (4,
    Jmp (Var R_LR)
  )

| _ => None
end.
