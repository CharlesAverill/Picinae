(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: rand_r; entry: 0x13e280; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e29_rand_r_arm8 : program := fun _ a => match a with
(* 0x13e280: ldr w1,[x0] *)
| 0x13e280 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e284: mov w5,#0x4e6d *)
| 0x13e284 => Some (4,
	Move R_X5 (Word 0x4e6d 64)
)
(* 0x13e288: movk w5,#0x41c6, LSL #16 *)
| 0x13e288 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X5)) (Word 0xffff 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x41c60000 32)) $;
	Move R_X5 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e28c: mov w4,#0x3039 *)
| 0x13e28c => Some (4,
	Move R_X4 (Word 0x3039 64)
)
(* 0x13e290: madd w1,w1,w5,w4 *)
| 0x13e290 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X5))) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e294: lsr w3,w1,#0x10 *)
| 0x13e294 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x10 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e298: madd w1,w1,w5,w4 *)
| 0x13e298 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X5))) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e29c: ubfiz w3,w3,#0xa,#0xb *)
| 0x13e29c => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x16 32)) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x20 32) (Word 0x16 32)) $;
	Move (V_TEMP 3) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1ffc00 32)) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 5)) (Word 0x1fffff 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 6)))
)
(* 0x13e2a0: ubfx x2,x1,#0x10,#0xa *)
| 0x13e2a0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x10 64)) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x40 64) (Word 0x10 64)) $;
	Move (V_TEMP 3) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xffff0000000003ff 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 5)) (Word 0x3ff 64))
)
(* 0x13e2a4: madd w1,w1,w5,w4 *)
| 0x13e2a4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X5))) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X4))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e2a8: orr w2,w2,w3 *)
| 0x13e2a8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e2ac: str w1,[x0] *)
| 0x13e2ac => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X1)) LittleE 4)
)
(* 0x13e2b0: ubfx x1,x1,#0x10,#0xa *)
| 0x13e2b0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 0x10 64)) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x40 64) (Word 0x10 64)) $;
	Move (V_TEMP 3) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xffff0000000003ff 64)) $;
	Move R_X1 (BinOp OP_AND (Var (V_TEMP 5)) (Word 0x3ff 64))
)
(* 0x13e2b4: orr w0,w1,w2, LSL #0xa *)
| 0x13e2b4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X2)) (Word 0xa 32)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e2b8: ret *)
| 0x13e2b8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e29_rand_r_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
