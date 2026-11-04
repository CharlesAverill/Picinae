(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: remque; entry: 0x1e4600; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_remque_arm8 : program := fun _ a => match a with
(* 0x1e4600: ldp x1,x0,[x0] *)
| 0x1e4600 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X1 (Var (V_TEMP 1)) $;
	Move R_X0 (Var (V_TEMP 3))
)
(* 0x1e4604: cbz x1,0x001e460c *)
| 0x1e4604 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X1) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x1e460c 64)) (Nop)
)
(* 0x1e4608: str x0,[x1, #0x8] *)
| 0x1e4608 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X0) LittleE 8)
)
(* 0x1e460c: cbz x0,0x001e4614 *)
| 0x1e460c => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X0) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x1e4614 64)) (Nop)
)
(* 0x1e4610: str x1,[x0] *)
| 0x1e4610 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X1) LittleE 8)
)
(* 0x1e4614: ret *)
| 0x1e4614 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_remque_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
