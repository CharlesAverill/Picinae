(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: ffsll
entry: 0x194b10 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition ffsl_arm8 : program := fun _ a => match a with

(* 0x00194b10: mov x1,x0 *)
(*          0: mov x1,x0 *)
| 0x0 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x00194b14: neg x0,x0 *)
(*          4: neg x0,x0 *)
| 0x4 => Some (4,
	Move R_X0 (UnOp OP_NEG (Var R_X0))
)

(* 0x00194b18: and x0,x0,x1 *)
(*          8: and x0,x0,x1 *)
| 0x8 => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Var R_X1))
)

(* 0x00194b1c: orr x2,xzr,#0xffffffff *)
(*         12: orr x2,xzr,#0xffffffff *)
| 0xc => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move R_X2 (BinOp OP_OR (Var (V_TEMP 0)) (Word 0xffffffff 64))
)

(* 0x00194b20: cmp x0,x2 *)
(*         16: cmp x0,x2 *)
| 0x10 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Var R_X0) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194b24: b.hi 0x00194b3c *)
(*         20: b.hi 0x00194b3c *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x2c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00194b28: rbit w0,w1 *)
(*         24: rbit w0,w1 *)
| 0x18 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xaaaaaaaa 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x55555555 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xcccccccc 32)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Word 2 32)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x33333333 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf0f0f0f0 32)) $;
	Move (V_TEMP 10) (BinOp OP_RSHIFT (Var (V_TEMP 9)) (Word 4 32)) $;
	Move (V_TEMP 11) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf0f0f0f 32)) $;
	Move (V_TEMP 12) (BinOp OP_LSHIFT (Var (V_TEMP 11)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 10)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 14) (BinOp OP_RSHIFT (Var (V_TEMP 13)) (Word 8 32)) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 16) (BinOp OP_LSHIFT (Var (V_TEMP 15)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 14)) (Var (V_TEMP 16))) $;
	Move (V_TEMP 17) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 18) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 17)) (Var (V_TEMP 18))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00194b2c: cmp w1,#0x0 *)
(*         28: cmp w1,#0x0 *)
| 0x1c => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194b30: clz w0,w0 *)
(*         32: clz w0,w0 *)
| 0x20 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Extract 31 0 (Var R_X0)))))
)

(* 0x00194b34: csinc w0,wzr,w0,eq *)
(*         36: csinc w0,wzr,w0,eq *)
| 0x24 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	) (* else *) (
		Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	)
)

(* 0x00194b38: ret *)
(*         40: ret *)
| 0x28 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00194b3c: asr x1,x1,#0x20 *)
(*         44: asr x1,x1,#0x20 *)
| 0x2c => Some (4,
	Move R_X1 (BinOp OP_ARSHIFT (Var R_X1) (Word 32 64))
)

(* 0x00194b40: rbit w0,w1 *)
(*         48: rbit w0,w1 *)
| 0x30 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xaaaaaaaa 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x55555555 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xcccccccc 32)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Word 2 32)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x33333333 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf0f0f0f0 32)) $;
	Move (V_TEMP 10) (BinOp OP_RSHIFT (Var (V_TEMP 9)) (Word 4 32)) $;
	Move (V_TEMP 11) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf0f0f0f 32)) $;
	Move (V_TEMP 12) (BinOp OP_LSHIFT (Var (V_TEMP 11)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 10)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 14) (BinOp OP_RSHIFT (Var (V_TEMP 13)) (Word 8 32)) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 16) (BinOp OP_LSHIFT (Var (V_TEMP 15)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 14)) (Var (V_TEMP 16))) $;
	Move (V_TEMP 17) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 18) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 17)) (Var (V_TEMP 18))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00194b44: cmp w1,#0x0 *)
(*         52: cmp w1,#0x0 *)
| 0x34 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194b48: clz w0,w0 *)
(*         56: clz w0,w0 *)
| 0x38 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Extract 31 0 (Var R_X0)))))
)

(* 0x00194b4c: csinc w0,wzr,w0,eq *)
(*         60: csinc w0,wzr,w0,eq *)
| 0x3c => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	) (* else *) (
		Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	)
)

(* 0x00194b50: add w0,w0,#0x20 *)
(*         64: add w0,w0,#0x20 *)
| 0x40 => Some (4,
	Move (V_TEMP 0) (Word 0x20 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x00194b54: ret *)
(*         68: ret *)
| 0x44 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ffsl_arm8.
Proof. Picinae_typecheck. Qed.

