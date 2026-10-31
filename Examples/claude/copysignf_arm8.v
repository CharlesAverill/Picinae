(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: copysignf
entry: 0x13a250 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition copysignf_arm8 : program := fun _ a => match a with

(* 0x0013a250: movi v2.2S,#0x80, LSL #24 *)
(*          0: movi v2.2S,#0x80, LSL #24 *)
| 0x0 => Some (4,
	Move R_Z2 (Concat (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Word 0x0 64)) (Word 0x8000000080000000 64))
)

(* 0x0013a254: bit v0.8B,v1.8B,v2.8B *)
(*          4: bit v0.8B,v1.8B,v2.8B *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 63 0 (Var R_Z0)) (Extract 63 0 (Var R_Z1))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Extract 63 0 (Var R_Z2))) $;
	Move R_Z0 (Concat (Extract 255 64 (Var R_Z0)) (BinOp OP_XOR (Extract 63 0 (Var R_Z0)) (Var (V_TEMP 1))))
)

(* 0x0013a258: ret *)
(*          8: ret *)
| 0x8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx copysignf_arm8.
Proof. Picinae_typecheck. Qed.

