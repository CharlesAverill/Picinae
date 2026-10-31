(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: isinff
entry: 0x13a1e0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition isinff_arm8 : program := fun _ a => match a with

(* 0x0013a1e0: fmov w0,s0 *)
(*          0: fmov w0,s0 *)
| 0x0 => Some (4,
	Move R_X0 (Concat (Word 0x0 32) (Extract 31 0 (Var R_Z0)))
)

(* 0x0013a1e4: and w2,w0,#0x7fffffff *)
(*          4: and w2,w0,#0x7fffffff *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7fffffff 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1e8: asr w0,w0,#0x1e *)
(*          8: asr w0,w0,#0x1e *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_X0)) (Word 30 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1ec: eor w2,w2,#0x7f800000 *)
(*         12: eor w2,w2,#0x7f800000 *)
| 0xc => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 31 0 (Var R_X2)) (Word 0x7f800000 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1f0: neg w1,w2 *)
(*         16: neg w1,w2 *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Extract 31 0 (Var R_X2))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1f4: orr w1,w1,w2 *)
(*         20: orr w1,w1,w2 *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1f8: asr w1,w1,#0x1f *)
(*         24: asr w1,w1,#0x1f *)
| 0x18 => Some (4,
	Move (V_TEMP 0) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a1fc: bic w0,w0,w1 *)
(*         28: bic w0,w0,w1 *)
| 0x1c => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Var (V_TEMP 1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)

(* 0x0013a200: ret *)
(*         32: ret *)
| 0x20 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx isinff_arm8.
Proof. Picinae_typecheck. Qed.

