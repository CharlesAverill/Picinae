(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: __drand48_iterate; entry: 0x13e7c0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08___drand48_iterate_arm8 : program := fun _ a => match a with
(* 0x13e7c0: mov x2,x0 *)
| 0x13e7c0 => Some (4,
	Move R_X2 (Var R_X0)
)
(* 0x13e7c4: ldrh w0,[x1, #0xe] *)
| 0x13e7c4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xe 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e7c8: cbz w0,0x0013e804 *)
| 0x13e7c8 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x13e804 64)) (Nop)
)
(* 0x13e7cc: ldrh w4,[x1, #0xc] *)
| 0x13e7cc => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xc 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e7d0: ldr x5,[x1, #0x10] *)
| 0x13e7d0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move R_X5 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x13e7d4: mov w0,#0x0 *)
| 0x13e7d4 => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x13e7d8: ldrh w1,[x2, #0x4] *)
| 0x13e7d8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e7dc: ldrh w6,[x2] *)
| 0x13e7dc => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e7e0: ldrh w3,[x2, #0x2] *)
| 0x13e7e0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x2 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x13e7e4: orr x1,x6,x1, LSL #0x20 *)
| 0x13e7e4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Var R_X1) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X1 (BinOp OP_OR (Var R_X6) (Var (V_TEMP 0)))
)
(* 0x13e7e8: lsl w3,w3,#0x10 *)
| 0x13e7e8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X3)) (Word 0x10 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e7ec: orr x1,x1,x3 *)
| 0x13e7ec => Some (4,
	Move R_X1 (BinOp OP_OR (Var R_X1) (Var R_X3))
)
(* 0x13e7f0: madd x1,x1,x5,x4 *)
| 0x13e7f0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_X1) (Var R_X5)) $;
	Move R_X1 (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0)))
)
(* 0x13e7f4: str w1,[x2] *)
| 0x13e7f4 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X1)) LittleE 4)
)
(* 0x13e7f8: lsr x1,x1,#0x20 *)
| 0x13e7f8 => Some (4,
	Move R_X1 (BinOp OP_RSHIFT (Var R_X1) (Word 0x20 64))
)
(* 0x13e7fc: strh w1,[x2, #0x4] *)
| 0x13e7fc => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x4 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X1))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x13e800: ret *)
| 0x13e800 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x13e804: mov x0,#0xe66d *)
| 0x13e804 => Some (4,
	Move R_X0 (Word 0xe66d 64)
)
(* 0x13e808: mov w3,#0xb *)
| 0x13e808 => Some (4,
	Move R_X3 (Word 0xb 64)
)
(* 0x13e80c: movk x0,#0xdeec, LSL #16 *)
| 0x13e80c => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Word 0xffffffff0000ffff 64)) $;
	Move R_X0 (BinOp OP_OR (Var R_X0) (Word 0xdeec0000 64))
)
(* 0x13e810: movk w3,#0x1, LSL #16 *)
| 0x13e810 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X3)) (Word 0xffff 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x10000 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x13e814: movk x0,#0x5, LSL #32 *)
| 0x13e814 => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Word 0xffff0000ffffffff 64)) $;
	Move R_X0 (BinOp OP_OR (Var R_X0) (Word 0x500000000 64))
)
(* 0x13e818: mov x4,#0xb *)
| 0x13e818 => Some (4,
	Move R_X4 (Word 0xb 64)
)
(* 0x13e81c: mov x5,x0 *)
| 0x13e81c => Some (4,
	Move R_X5 (Var R_X0)
)
(* 0x13e820: str w3,[x1, #0xc] *)
| 0x13e820 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0xc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X3)) LittleE 4)
)
(* 0x13e824: str x0,[x1, #0x10] *)
| 0x13e824 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X0) LittleE 8)
)
(* 0x13e828: b 0x0013e7d4 *)
| 0x13e828 => Some (4,
	Jmp (Word 0x13e7d4 64)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08___drand48_iterate_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
