(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: ldiv; entry: 0x13d860; addressing: relative
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e11_ldiv_arm8 : program := fun _ a => match a with
(* 0x13d860: mov x2,x0 *)
| 0x0 => Some (4,
	Move R_X2 (Var R_X0)
)
(* 0x13d864: sdiv x0,x0,x1 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X1) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Nop) (Move (V_TEMP 0) (BinOp OP_SDIVIDE (Var R_X0) (Var R_X1))) $;
	Move R_X0 (Var (V_TEMP 0))
)
(* 0x13d868: msub x1,x0,x1,x2 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_X0) (Var R_X1)) $;
	Move R_X1 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0)))
)
(* 0x13d86c: ret *)
| 0xc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e11_ldiv_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
