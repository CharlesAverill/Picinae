(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: inet_lnaof
entry: 0x1f9d10 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition inet_lnaof_arm8 : program := fun _ a => match a with

(* 0x001f9d10: rev w0,w0 *)
(*          0: rev w0,w0 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 6) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 6))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d14: tbz w0,#0x1f,0x001f9d34 *)
(*          4: tbz w0,#0x1f,0x001f9d34 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (
		Jmp (Word 0x24 64)
	) (* else *) (
		Nop
	)
)

(* 0x001f9d18: and w3,w0,#0xc0000000 *)
(*          8: and w3,w0,#0xc0000000 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xc0000000 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d1c: and w1,w0,#0xffff *)
(*         12: and w1,w0,#0xffff *)
| 0xc => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffff 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d20: mov w2,#0x80000000 *)
(*         16: mov w2,#0x80000000 *)
| 0x10 => Some (4,
	Move R_X2 (Word 0x80000000 64)
)

(* 0x001f9d24: and w0,w0,#0xff *)
(*         20: and w0,w0,#0xff *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d28: cmp w3,w2 *)
(*         24: cmp w3,w2 *)
| 0x18 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001f9d2c: csel w0,w0,w1,ne *)
(*         28: csel w0,w0,w1,ne *)
| 0x1c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	) (* else *) (
		Move (V_TEMP 1) (Extract 31 0 (Var R_X1)) $;
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	)
)

(* 0x001f9d30: ret *)
(*         32: ret *)
| 0x20 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001f9d34: and w0,w0,#0xffffff *)
(*         36: and w0,w0,#0xffffff *)
| 0x24 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d38: ret *)
(*         40: ret *)
| 0x28 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx inet_lnaof_arm8.
Proof. Picinae_typecheck. Qed.

