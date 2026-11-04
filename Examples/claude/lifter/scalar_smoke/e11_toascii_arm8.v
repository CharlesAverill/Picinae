(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: toascii; entry: 0x134460; addressing: relative
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e11_toascii_arm8 : program := fun _ a => match a with
(* 0x134460: and w0,w0,#0x7f *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7f 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)
(* 0x134464: ret *)
| 0x4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e11_toascii_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
