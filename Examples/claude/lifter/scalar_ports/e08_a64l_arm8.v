(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: a64l; entry: 0x1477f0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_a64l_arm8 : program := fun _ a => match a with
(* 0x1477f0: adrp x4,0x249000 *)
| 0x1477f0 => Some (4,
	Move R_X4 (Word 0x249000 64)
)
(* 0x1477f4: add x4,x4,#0x4c8 *)
| 0x1477f4 => Some (4,
	Move (V_TEMP 0) (Word 0x4c8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X4)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X4)) (Extract 63 63 (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 1))
)
(* 0x1477f8: mov x3,x0 *)
| 0x1477f8 => Some (4,
	Move R_X3 (Var R_X0)
)
(* 0x1477fc: mov w2,#0x0 *)
| 0x1477fc => Some (4,
	Move R_X2 (Word 0x0 64)
)
(* 0x147800: mov x0,#0x0 *)
| 0x147800 => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x147804: ldrb w1,[x3] *)
| 0x147804 => Some (4,
	Move (V_TEMP 0) (Var R_X3) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x147808: add x3,x3,#0x1 *)
| 0x147808 => Some (4,
	Move (V_TEMP 0) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X3)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X3)) (Extract 63 63 (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 1))
)
(* 0x14780c: sub w1,w1,#0x2e *)
| 0x14780c => Some (4,
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2e 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x147810: cmp w1,#0x4c *)
| 0x147810 => Some (4,
	Move (V_TEMP 0) (Word 0x4c 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x4c 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (Word 0x4c 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x4c 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x147814: b.hi 0x00147838 *)
| 0x147814 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x147838 64)) (Nop)
)
(* 0x147818: ldrb w1,[x4, w1, UXTW ] *)
| 0x147818 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X1))) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)
(* 0x14781c: cmp w1,#0x40 *)
| 0x14781c => Some (4,
	Move (V_TEMP 0) (Word 0x40 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x40 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (Word 0x40 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X1))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x40 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x147820: b.eq 0x00147838 *)
| 0x147820 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x147838 64)) (Nop)
)
(* 0x147824: lsl w1,w1,w2 *)
| 0x147824 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Word 0x1f 32)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Ite (BinOp OP_LT (Var (V_TEMP 1)) (Word 0x20 64)) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Cast CAST_LOW 32 (Var (V_TEMP 1)))) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Word 0x20 32))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)
(* 0x147828: add w2,w2,#0x6 *)
| 0x147828 => Some (4,
	Move (V_TEMP 0) (Word 0x6 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x14782c: orr x0,x0,x1 *)
| 0x14782c => Some (4,
	Move R_X0 (BinOp OP_OR (Var R_X0) (Var R_X1))
)
(* 0x147830: cmp w2,#0x24 *)
| 0x147830 => Some (4,
	Move (V_TEMP 0) (Word 0x24 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x24 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Word 0x24 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x24 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x147834: b.ne 0x00147804 *)
| 0x147834 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x147804 64)) (Nop)
)
(* 0x147838: ret *)
| 0x147838 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_a64l_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
