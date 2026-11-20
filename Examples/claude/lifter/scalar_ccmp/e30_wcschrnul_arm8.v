(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: wcschrnul; entry: 0x19e4c0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e30_wcschrnul_arm8 : program := fun _ a => match a with
(* 0x19e4c0: ldr w2,[x0] *)
| 0x19e4c0 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19e4c4: cmp w2,#0x0 *)
| 0x19e4c4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Word 0x0 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x0 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19e4c8: ccmp w1,w2,#0x4,ne *)
| 0x19e4c8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x4 8) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x8 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x4 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x2 8))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 6)) (Word 0x1 8))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 1)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 7))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (Extract 31 0 (Var R_X2)))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))))))) $;
	Move (V_TEMP 8) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19e4cc: b.eq 0x0019e4e0 *)
| 0x19e4cc => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x19e4e0 64)) (Nop)
)
(* 0x19e4d0: ldr w2,[x0, #0x4]! *)
| 0x19e4d0 => Some (4,
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x4 64)) $;
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_X0) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x19e4d4: cmp w2,#0x0 *)
| 0x19e4d4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Word 0x0 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x0 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19e4d8: ccmp w2,w1,#0x4,ne *)
| 0x19e4d8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x4 8) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x8 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x4 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x2 8))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 6)) (Word 0x1 8))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 1)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 7))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Extract 31 0 (Var R_X1)))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))))))) $;
	Move (V_TEMP 8) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19e4dc: b.ne 0x0019e4d0 *)
| 0x19e4dc => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19e4d0 64)) (Nop)
)
(* 0x19e4e0: ret *)
| 0x19e4e0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e30_wcschrnul_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
