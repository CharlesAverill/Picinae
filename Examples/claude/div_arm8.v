(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: div
entry: 0x13d840 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition div_arm8 : program := fun _ a => match a with

(* 0x0013d840: mov w2,w0 *)
(*          0: mov w2,w0 *)
| 0x0 => Some (4,
	Move R_X2 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0013d844: mov x0,#0x0 *)
(*          4: mov x0,#0x0 *)
| 0x4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0013d848: sdiv w3,w2,w1 *)
(*          8: sdiv w3,w2,w1 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
	) (* else *) (
		Move (V_TEMP 0) (BinOp OP_SDIVIDE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
		Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
	)
)

(* 0x0013d84c: msub w1,w3,w1,w2 *)
(*         12: msub w1,w3,w1,w2 *)
| 0xc => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X1))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x0013d850: bfxil x0,x3,#0x0,#0x20 *)
(*         16: bfxil x0,x3,#0x0,#0x20 *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_MINUS (Word 0x40 64) (Word 0x20 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Word 0xffffffffffffffff 64) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_X3) (Word 0 64)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var R_X0) (Var (V_TEMP 4))) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 3)))
)

(* 0x0013d854: bfm x0,x1,#0x20,#0x1f *)
(*         20: bfm x0,x1,#0x20,#0x1f *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (Word 0xffffffff00000000 64) $;
	Move (V_TEMP 1) (Word 0xffffffffffffffff 64) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move (V_TEMP 3) (Var R_X1) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 32 64)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x40 64) (Word 0x20 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))
)

(* 0x0013d858: ret *)
(*         24: ret *)
| 0x18 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx div_arm8.
Proof. Picinae_typecheck. Qed.

