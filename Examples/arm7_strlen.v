Require Import Picinae_armv7.
Require Import NArith.
Open Scope N.

Definition strlen_arm : program := fun _ a => match a with

(* 0xc0000040: bic r1, r0, #3 *)
| 0 => Some (4,
    Move R_R1 (BinOp OP_AND (Var R_R0) (UnOp OP_NOT (Word 3 32)))
  )

(* 0xc0000044: ldr r2, [r1], #4 *)
| 4 => Some (4, 
    Move R_R2 (Load (Var V_MEM32) (Var R_R1) LittleE 4) $;
    Move R_R1 (BinOp OP_PLUS (Var R_R1) (Word 4 32))
  )

(* 0xc0000048: ands r3, r0, #3 *)
| 8 => Some (4, 
    Move R_R3 (BinOp OP_AND (Var R_R0) (Word 3 32)) $;
    Move R_CF (Unknown 1) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R3)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R3) (Word 0 32))
  )

(* 0xc000004c: rsb r0, r3, #0 *)
| 12 => Some (4, 
    Move (V_TEMP 0 (* v134 *)) (Var R_R3) $;
    Move (V_TEMP 1 (* v135 *)) (Word 0 32) $;
    Move R_R0 (UnOp OP_NEG (Var R_R3))
  )

(* 0xc0000050: beq #0x10 *)
| 16 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 1 1)) (
      Jmp (Word 40 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000054: orr r2, r2, #255 *)
| 20 => Some (4,
    Move R_R2 (BinOp OP_OR (Var R_R2) (Word 255 32))
  )

(* 0xc0000058: subs r3, r3, #1 *)
| 24 => Some (4, 
    Move (V_TEMP 2 (* v166 *)) (Var R_R3) $;
    Move (V_TEMP 3 (* v167 *)) (Word 1 32) $;
    Move R_R3 (BinOp OP_MINUS (Var R_R3) (Word 1 32)) $;
    Move R_CF (BinOp OP_LE (Var (V_TEMP 3 (* v167 *))) (Var (V_TEMP 2 (* v166 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 2 (* v166 *))) (Var (V_TEMP 3 (* v167 *)))) (BinOp OP_XOR (Var (V_TEMP 2 (* v166 *))) (Var R_R3)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R3)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R3) (Word 0 32))
  )
(* TODO: BUG: lifted 65280 as 3327 *)
(* 0xc000005c: orrgt r2, r2, #65280 *)
| 28 => Some (4,
    If (BinOp OP_AND (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) (
      Move R_R2 (BinOp OP_OR (Var R_R2) (Word 65280 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000060: subs r3, r3, #1 *)
| 32 => Some (4, 
    Move (V_TEMP 4 (* v174 *)) (Var R_R3) $;
    Move (V_TEMP 5 (* v175 *)) (Word 1 32) $;
    Move R_R3 (BinOp OP_MINUS (Var R_R3) (Word 1 32)) $;
    Move R_CF (BinOp OP_LE (Var (V_TEMP 5 (* v175 *))) (Var (V_TEMP 4 (* v174 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 4 (* v174 *))) (Var (V_TEMP 5 (* v175 *)))) (BinOp OP_XOR (Var (V_TEMP 4 (* v174 *))) (Var R_R3)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R3)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R3) (Word 0 32))
  )

(* TODO: BUG: lifted 16711680 as 2303 *)
(* 0xc0000064: orrgt r2, r2, #16711680 *)
| 36 => Some (4,
    If (BinOp OP_AND (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) (
      Move R_R2 (BinOp OP_OR (Var R_R2) (Word 16711680 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000068: tst r2, #255 *)
| 40 => Some (4, 
    Move (V_TEMP 6 (* v139 *)) (BinOp OP_AND (Var R_R2) (Word 255 32)) $;
    Move R_CF (Unknown 1) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v139 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 6 (* v139 *))) (Word 0 32))
  )

(* 0xc000006c: tstne r2, #65280 *)
| 44 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 7 (* v143 *)) (BinOp OP_AND (Var R_R2) (Word 65280 32)) $;
      Move R_CF (Word 0 1) $;
      Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 7 (* v143 *)))) $;
      Move R_ZF (BinOp OP_EQ (Var (V_TEMP 7 (* v143 *))) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000070: tstne r2, #16711680 *)
| 48 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 8 (* v147 *)) (BinOp OP_AND (Var R_R2) (Word 16711680 32)) $;
      Move R_CF (Word 0 1) $;
      Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 8 (* v147 *)))) $;
      Move R_ZF (BinOp OP_EQ (Var (V_TEMP 8 (* v147 *))) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000074: tstne r2, #-16777216 *)
| 52 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 9 (* v151 *)) (BinOp OP_AND (Var R_R2) (Word 4278190080 32)) $;
      Move R_CF (Word 0 1) $;
      Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 9 (* v151 *)))) $;
      Move R_ZF (BinOp OP_EQ (Var (V_TEMP 9 (* v151 *))) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000078: addne r0, r0, #4 *)
| 56 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 10 (* v156 *)) (Var R_R0) $;
      Move (V_TEMP 11 (* v157 *)) (Word 4 32) $;
      Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 4 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007c: ldrne r2, [r1], #4 *)
| 60 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move R_R2 (Load (Var V_MEM32) (Var R_R1) LittleE 4) $;
      Move R_R1 (BinOp OP_PLUS (Var R_R1) (Word 4 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000080: bne #-0x20 *)
| 64 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Jmp (Word 40 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000084: tst r2, #255 *)
| 68 => Some (4, 
    Move (V_TEMP 12 (* v181 *)) (BinOp OP_AND (Var R_R2) (Word 255 32)) $;
    Move R_CF (Unknown 1) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v181 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 12 (* v181 *))) (Word 0 32))
  )

(* 0xc0000088: addne r0, r0, #1 *)
| 72 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 13 (* v186 *)) (Var R_R0) $;
      Move (V_TEMP 14 (* v187 *)) (Word 1 32) $;
      Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000008c: tstne r2, #65280 *)
| 76 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 15 (* v191 *)) (BinOp OP_AND (Var R_R2) (Word 65280 32)) $;
      Move R_CF (Word 0 1) $;
      Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 15 (* v191 *)))) $;
      Move R_ZF (BinOp OP_EQ (Var (V_TEMP 15 (* v191 *))) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000090: addne r0, r0, #1 *)
| 80 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 16 (* v196 *)) (Var R_R0) $;
      Move (V_TEMP 17 (* v197 *)) (Word 1 32) $;
      Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000094: tstne r2, #16711680 *)
| 84 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 18 (* v201 *)) (BinOp OP_AND (Var R_R2) (Word 16711680 32)) $;
      Move R_CF (Word 0 1) $;
      Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* v201 *)))) $;
      Move R_ZF (BinOp OP_EQ (Var (V_TEMP 18 (* v201 *))) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000098: addne r0, r0, #1 *)
| 88 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 19 (* v206 *)) (Var R_R0) $;
      Move (V_TEMP 20 (* v207 *)) (Word 1 32) $;
      Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009c: bx lr *)
| 92 => Some (4,
    Jmp (Var R_LR)
  )

| _ => None
end.
