(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: sigabbrev_np; entry: 0x19aaf0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_sigabbrev_np_arm8 : program := fun _ a => match a with
(* 0x19aaf0: cmp w0,#0x40 *)
| 0x19aaf0 => Some (4,
	Move (V_TEMP 0) (Word 0x40 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x40 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (Word 0x40 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X0))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x40 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19aaf4: b.hi 0x0019ab08 *)
| 0x19aaf4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ab08 64)) (Nop)
)
(* 0x19aaf8: adrp x1,0x2a0000 *)
| 0x19aaf8 => Some (4,
	Move R_X1 (Word 0x2a0000 64)
)
(* 0x19aafc: add x1,x1,#0x60 *)
| 0x19aafc => Some (4,
	Move (V_TEMP 0) (Word 0x60 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 1))
)
(* 0x19ab00: ldr x0,[x1, w0, SXTW #0x3] *)
| 0x19ab00 => Some (4,
	Move (V_TEMP 0) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X0))) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x3 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 1))) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8)
)
(* 0x19ab04: ret *)
| 0x19ab04 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19ab08: mov x0,#0x0 *)
| 0x19ab08 => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x19ab0c: ret *)
| 0x19ab0c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_sigabbrev_np_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
