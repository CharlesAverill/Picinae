(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: lcong48_r; entry: 0x13e770; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_lcong48_r_arm8 : program := fun _ a => match a with
(* 0x13e770: mov x2,x0 *)
| 0x13e770 => Some (4,
	Move R_X2 (Var R_X0)
)
(* 0x13e774: mov w5,#0x1 *)
| 0x13e774 => Some (4,
	Move R_X5 (Word 0x1 64)
)
(* 0x13e778: mov w0,#0x0 *)
| 0x13e778 => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x13e77c: ldr w3,[x2] *)
| 0x13e77c => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e780: str w3,[x1] *)
| 0x13e780 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X3)) LittleE 4)
)
(* 0x13e784: ldrh w3,[x2, #0x4] *)
| 0x13e784 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e788: strh w3,[x1, #0x4] *)
| 0x13e788 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X3))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e78c: ldrh w3,[x2, #0xa] *)
| 0x13e78c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0xa 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e790: ldrh w4,[x2, #0x8] *)
| 0x13e790 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x8 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e794: ldrh w7,[x2, #0x6] *)
| 0x13e794 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x6 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X7 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e798: ldrh w6,[x2, #0xc] *)
| 0x13e798 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0xc 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e79c: strh w6,[x1, #0xc] *)
| 0x13e79c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xc 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X6))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e7a0: orr x2,x7,x3, LSL #0x20 *)
| 0x13e7a0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Var R_X3) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X2 (BinOp OP_OR (Var R_X7) (Var (V_TEMP 0)))
)
(* 0x13e7a4: lsl w3,w4,#0x10 *)
| 0x13e7a4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X4)) (Word 0x10 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e7a8: orr x2,x2,x3 *)
| 0x13e7a8 => Some (4,
	Move R_X2 (BinOp OP_OR (Var R_X2) (Var R_X3))
)
(* 0x13e7ac: strh w5,[x1, #0xe] *)
| 0x13e7ac => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xe 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X5))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e7b0: str x2,[x1, #0x10] *)
| 0x13e7b0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X2) LittleE 8)
)
(* 0x13e7b4: ret *)
| 0x13e7b4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_lcong48_r_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
