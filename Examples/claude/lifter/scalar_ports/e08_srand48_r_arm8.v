(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: srand48_r; entry: 0x13e6d0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_srand48_r_arm8 : program := fun _ a => match a with
(* 0x13e6d0: mov x2,#0xe66d *)
| 0x13e6d0 => Some (4,
	Move R_X2 (Word 0xe66d 64)
)
(* 0x13e6d4: mov w3,#0xb *)
| 0x13e6d4 => Some (4,
	Move R_X3 (Word 0xb 64)
)
(* 0x13e6d8: movk x2,#0xdeec, LSL #16 *)
| 0x13e6d8 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffffffff0000ffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0xdeec0000 64))
)
(* 0x13e6dc: mov x4,x0 *)
| 0x13e6dc => Some (4,
	Move R_X4 (Var R_X0)
)
(* 0x13e6e0: mov w5,#0x330e *)
| 0x13e6e0 => Some (4,
	Move R_X5 (Word 0x330e 64)
)
(* 0x13e6e4: movk w3,#0x1, LSL #16 *)
| 0x13e6e4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X3)) (Word 0xffff 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x10000 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e6e8: movk x2,#0x5, LSL #32 *)
| 0x13e6e8 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffff0000ffffffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0x500000000 64))
)
(* 0x13e6ec: mov w0,#0x0 *)
| 0x13e6ec => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x13e6f0: strh w5,[x1] *)
| 0x13e6f0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X5))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e6f4: stur w4,[x1, #0x2] *)
| 0x13e6f4 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Word 0x2 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 4)
)
(* 0x13e6f8: str w3,[x1, #0xc] *)
| 0x13e6f8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X3)) LittleE 4)
)
(* 0x13e6fc: str x2,[x1, #0x10] *)
| 0x13e6fc => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X2) LittleE 8)
)
(* 0x13e700: ret *)
| 0x13e700 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_srand48_r_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
