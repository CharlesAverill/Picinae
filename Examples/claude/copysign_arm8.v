(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: copysign
entry: 0x139f40 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition copysign_arm8 : program := fun _ a => match a with

(* 0x00139f40: mov x0,#-0x8000000000000000 *)
(*          0: mov x0,#-0x8000000000000000 *)
| 0x0 => Some (4,
	Move R_X0 (Word 0x8000000000000000 64)
)

(* 0x00139f44: fmov d2,x0 *)
(*          4: fmov d2,x0 *)
| 0x4 => Some (4,
	Move R_Z2 (Concat (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Word 0x0 64)) (Var R_X0))
)

(* 0x00139f48: bit v0.8B,v1.8B,v2.8B *)
(*          8: bit v0.8B,v1.8B,v2.8B *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 63 0 (Var R_Z0)) (Extract 63 0 (Var R_Z1))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Extract 63 0 (Var R_Z2))) $;
	Move R_Z0 (Concat (Extract 255 64 (Var R_Z0)) (BinOp OP_XOR (Extract 63 0 (Var R_Z0)) (Var (V_TEMP 1))))
)

(* 0x00139f4c: ret *)
(*         12: ret *)
| 0xc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx copysign_arm8.
Proof. Picinae_typecheck. Qed.

