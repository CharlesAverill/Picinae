(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: seed48; entry: 0x13e540; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_seed48_arm8 : program := fun _ a => match a with
(* 0x13e540: stp x29,x30,[sp, #-0x10]! *)
| 0x13e540 => Some (4,
	Move (V_TEMP 0) (Var R_X29) $;
	Move (V_TEMP 1) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x13e544: adrp x1,0x2a3000 *)
| 0x13e544 => Some (4,
	Move R_X1 (Word 0x2a3000 64)
)
(* 0x13e548: add x1,x1,#0x4d8 *)
| 0x13e548 => Some (4,
	Move (V_TEMP 0) (Word 0x4d8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 1))
)
(* 0x13e54c: mov x29,sp *)
| 0x13e54c => Some (4,
	Move R_X29 (Var R_SP)
)
(* 0x13e550: bl 0x0013e710 *)
| 0x13e550 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x13e550 64) (Word 0x4 64)) $;
	Jmp (Word 0x13e710 64)
)
(* 0x13e554: ldp x29,x30,[sp], #0x10 *)
| 0x13e554 => Some (4,
	Move (V_TEMP 0) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 1)) $;
	Move R_X30 (Var (V_TEMP 3))
)
(* 0x13e558: adrp x0,0x2a3000 *)
| 0x13e558 => Some (4,
	Move R_X0 (Word 0x2a3000 64)
)
(* 0x13e55c: add x0,x0,#0x4de *)
| 0x13e55c => Some (4,
	Move (V_TEMP 0) (Word 0x4de 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 1))
)
(* 0x13e560: ret *)
| 0x13e560 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x13e710: mov x3,x1 *)
| 0x13e710 => Some (4,
	Move R_X3 (Var R_X1)
)
(* 0x13e714: mov x2,x0 *)
| 0x13e714 => Some (4,
	Move R_X2 (Var R_X0)
)
(* 0x13e718: ldrh w6,[x1, #0x4] *)
| 0x13e718 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e71c: mov x4,#0xe66d *)
| 0x13e71c => Some (4,
	Move R_X4 (Word 0xe66d 64)
)
(* 0x13e720: mov w5,#0xb *)
| 0x13e720 => Some (4,
	Move R_X5 (Word 0xb 64)
)
(* 0x13e724: movk x4,#0xdeec, LSL #16 *)
| 0x13e724 => Some (4,
	Move R_X4 (BinOp OP_AND (Var R_X4) (Word 0xffffffff0000ffff 64)) $;
	Move R_X4 (BinOp OP_OR (Var R_X4) (Word 0xdeec0000 64))
)
(* 0x13e728: ldr w7,[x3], #0x6 *)
| 0x13e728 => Some (4,
	Move (V_TEMP 0) (Var R_X3) $;
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x6 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X7 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e72c: movk w5,#0x1, LSL #16 *)
| 0x13e72c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X5)) (Word 0xffff 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x10000 32)) $;
	Move R_X5 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e730: stur w7,[x1, #0x6] *)
| 0x13e730 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X7)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Word 0x6 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 4)
)
(* 0x13e734: movk x4,#0x5, LSL #32 *)
| 0x13e734 => Some (4,
	Move R_X4 (BinOp OP_AND (Var R_X4) (Word 0xffff0000ffffffff 64)) $;
	Move R_X4 (BinOp OP_OR (Var R_X4) (Word 0x500000000 64))
)
(* 0x13e738: strh w6,[x3, #0x4] *)
| 0x13e738 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X3) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X6))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e73c: mov w0,#0x0 *)
| 0x13e73c => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x13e740: ldrh w3,[x2, #0x4] *)
| 0x13e740 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e744: strh w3,[x1, #0x4] *)
| 0x13e744 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X3))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e748: ldrh w3,[x2, #0x2] *)
| 0x13e748 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x2 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e74c: strh w3,[x1, #0x2] *)
| 0x13e74c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x2 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X3))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e750: ldrh w2,[x2] *)
| 0x13e750 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e754: strh w2,[x1] *)
| 0x13e754 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X2))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e758: str w5,[x1, #0xc] *)
| 0x13e758 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X5)) LittleE 4)
)
(* 0x13e75c: str x4,[x1, #0x10] *)
| 0x13e75c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X4) LittleE 8)
)
(* 0x13e760: ret *)
| 0x13e760 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_seed48_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
