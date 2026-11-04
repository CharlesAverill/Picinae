(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: insque; entry: 0x1e45e0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08_insque_arm8 : program := fun _ a => match a with
(* 0x1e45e0: mov x2,#0x0 *)
| 0x1e45e0 => Some (4,
	Move R_X2 (Word 0x0 64)
)
(* 0x1e45e4: cbz x1,0x001e45f8 *)
| 0x1e45e4 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X1) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x1e45f8 64)) (Nop)
)
(* 0x1e45e8: ldr x2,[x1] *)
| 0x1e45e8 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x1e45ec: str x0,[x1] *)
| 0x1e45ec => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X0) LittleE 8)
)
(* 0x1e45f0: cbz x2,0x001e45f8 *)
| 0x1e45f0 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X2) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x1e45f8 64)) (Nop)
)
(* 0x1e45f4: str x0,[x2, #0x8] *)
| 0x1e45f4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X2) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X0) LittleE 8)
)
(* 0x1e45f8: stp x2,x1,[x0] *)
| 0x1e45f8 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x1e45fc: ret *)
| 0x1e45fc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08_insque_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
