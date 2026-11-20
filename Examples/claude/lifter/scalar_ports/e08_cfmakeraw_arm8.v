(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: cfmakeraw; entry: 0x1e1500; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_cfmakeraw_arm8 : program := fun _ a => match a with
(* 0x1e1500: mov w1,#0x100 *)
| 0x1e1500 => Some (4,
	Move R_X1 (Word 0x100 64)
)
(* 0x1e1504: strh w1,[x0, #0x16] *)
| 0x1e1504 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X0) (Word 0x16 64)) $;
	Move (V_TEMP 1) (Extract 15 0 (Extract 31 0 (Var R_X1))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 2)
)
(* 0x1e1508: ldp w1,w2,[x0, #0x8] *)
| 0x1e1508 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x4 64)) $;
	Move (V_TEMP 4) (Load (Var V_MEM64) (Var (V_TEMP 3)) LittleE 4) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 4))) $;
	Move R_X1 (Var (V_TEMP 2)) $;
	Move R_X2 (Var (V_TEMP 5))
)
(* 0x1e150c: mov w5,#0xfffffecf *)
| 0x1e150c => Some (4,
	Move R_X5 (Word 0xfffffecf 64)
)
(* 0x1e1510: ldr x3,[x0] *)
| 0x1e1510 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x1e1514: and w1,w1,w5 *)
| 0x1e1514 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X5))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1e1518: mov x6,#-0x5ec *)
| 0x1e1518 => Some (4,
	Move R_X6 (Word 0xfffffffffffffa14 64)
)
(* 0x1e151c: orr w1,w1,#0x30 *)
| 0x1e151c => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Word 0x30 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1e1520: movk x6,#0xfffe, LSL #32 *)
| 0x1e1520 => Some (4,
	Move R_X6 (BinOp OP_AND (Var R_X6) (Word 0xffff0000ffffffff 64)) $;
	Move R_X6 (BinOp OP_OR (Var R_X6) (Word 0xfffe00000000 64))
)
(* 0x1e1524: mov w4,#0xffff7fb4 *)
| 0x1e1524 => Some (4,
	Move R_X4 (Word 0xffff7fb4 64)
)
(* 0x1e1528: and x3,x3,x6 *)
| 0x1e1528 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X3) (Var R_X6))
)
(* 0x1e152c: and w2,w2,w4 *)
| 0x1e152c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X4))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x1e1530: str x3,[x0] *)
| 0x1e1530 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X3) LittleE 8)
)
(* 0x1e1534: stp w1,w2,[x0, #0x8] *)
| 0x1e1534 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_X2)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 4) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x4 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 4)
)
(* 0x1e1538: ret *)
| 0x1e1538 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_cfmakeraw_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
