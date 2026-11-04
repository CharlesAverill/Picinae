(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: inet_makeaddr; entry: 0x1f9d40; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e29_inet_makeaddr_arm8 : program := fun _ a => match a with
(* 0x1f9d40: cmp w0,#0x7f *)
| 0x1f9d40 => Some (4,
	Move (V_TEMP 0) (Word 0x7f 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x7f 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (Word 0x7f 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x7f 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x1f9d44: b.hi 0x001f9d54 *)
| 0x1f9d44 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x1f9d54 64)) (Nop)
)
(* 0x1f9d48: bfm w1,w0,#0x8,#0x7 *)
| 0x1f9d48 => Some (4,
	Move (V_TEMP 0) (Word 0xff000000 32) $;
	Move (V_TEMP 1) (Word 0xffffffff 32) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x8 32)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x20 32) (Word 0x8 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 15) (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 15)))
)
(* 0x1f9d4c: rev w0,w1 *)
| 0x1f9d4c => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 0x8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 6) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 6))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1f9d50: ret *)
| 0x1f9d50 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x1f9d54: mov w2,#0xffff *)
| 0x1f9d54 => Some (4,
	Move R_X2 (Word 0xffff 64)
)
(* 0x1f9d58: cmp w0,w2 *)
| 0x1f9d58 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (Extract 31 0 (Var R_X2)))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X2))))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x1f9d5c: b.hi 0x001f9d6c *)
| 0x1f9d5c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x1f9d6c 64)) (Nop)
)
(* 0x1f9d60: bfm w1,w0,#0x10,#0xf *)
| 0x1f9d60 => Some (4,
	Move (V_TEMP 0) (Word 0xffff0000 32) $;
	Move (V_TEMP 1) (Word 0xffffffff 32) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x10 32)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 15) (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 15)))
)
(* 0x1f9d64: rev w0,w1 *)
| 0x1f9d64 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 0x8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 6) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 6))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1f9d68: ret *)
| 0x1f9d68 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x1f9d6c: mov w2,w1 *)
| 0x1f9d6c => Some (4,
	Move R_X2 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X1)))
)
(* 0x1f9d70: mov w3,#0xffffff *)
| 0x1f9d70 => Some (4,
	Move R_X3 (Word 0xffffff 64)
)
(* 0x1f9d74: bfm w2,w0,#0x18,#0x17 *)
| 0x1f9d74 => Some (4,
	Move (V_TEMP 0) (Word 0xffffff00 32) $;
	Move (V_TEMP 1) (Word 0xffffffff 32) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X2)) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x18 32)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x20 32) (Word 0x18 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 15) (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 15)))
)
(* 0x1f9d78: cmp w0,w3 *)
| 0x1f9d78 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (Extract 31 0 (Var R_X3)))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x1f9d7c: orr w0,w0,w1 *)
| 0x1f9d7c => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1f9d80: csel w1,w0,w2,hi *)
| 0x1f9d80 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Nop) (Move (V_TEMP 2) (Extract 31 0 (Var R_X2))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)
(* 0x1f9d84: rev w0,w1 *)
| 0x1f9d84 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 0x8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 6) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 6))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1f9d88: ret *)
| 0x1f9d88 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e29_inet_makeaddr_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
