(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: ffs
entry: 0x194aa0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition ffs_arm8 : program := fun _ a => match a with

(* 0x00194aa0: neg w1,w0 *)
(*          0: neg w1,w0 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Extract 31 0 (Var R_X0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00194aa4: mov w2,#0xffff *)
(*          4: mov w2,#0xffff *)
| 0x4 => Some (4,
	Move R_X2 (Word 0xffff 64)
)

(* 0x00194aa8: and w1,w1,w0 *)
(*          8: and w1,w1,w0 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00194aac: cmp w1,w2 *)
(*         12: cmp w1,w2 *)
| 0xc => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194ab0: b.hi 0x00194ad8 *)
(*         16: b.hi 0x00194ad8 *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x38 64)
	) (* else *) (
		Nop
	)
)

(* 0x00194ab4: cmp w1,#0xff *)
(*         20: cmp w1,#0xff *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (Word 0xff 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xff 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194ab8: adrp x2,0x24e000 *)
(*         24: adrp x2,0x24e000 *)
| 0x18 => Some (4,
	Move R_X2 (Word 0x24e000 64)
)

(* 0x00194abc: cset w0,hi *)
(*         28: cset w0,hi *)
| 0x1c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x00194ac0: add x2,x2,#0x738 *)
(*         32: add x2,x2,#0x738 *)
| 0x20 => Some (4,
	Move (V_TEMP 0) (Word 0x738 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1))
)

(* 0x00194ac4: lsl w0,w0,#0x3 *)
(*         36: lsl w0,w0,#0x3 *)
| 0x24 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 3 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00194ac8: lsr w1,w1,w0 *)
(*         40: lsr w1,w1,w0 *)
| 0x28 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Ite (BinOp OP_LT (Var (V_TEMP 1)) (Word 32 64)) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Cast CAST_LOW 32 (Var (V_TEMP 1)))) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 32 32))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)

(* 0x00194acc: ldrb w1,[x2, w1, UXTW ] *)
(*         44: ldrb w1,[x2, w1, UXTW ] *)
| 0x2c => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X1))) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)

(* 0x00194ad0: add w0,w1,w0 *)
(*         48: add w0,w1,w0 *)
| 0x30 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X0)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x00194ad4: ret *)
(*         52: ret *)
| 0x34 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00194ad8: mov w0,#0xffffff *)
(*         56: mov w0,#0xffffff *)
| 0x38 => Some (4,
	Move R_X0 (Word 0xffffff 64)
)

(* 0x00194adc: cmp w1,w0 *)
(*         60: cmp w1,w0 *)
| 0x3c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00194ae0: mov w2,#0x18 *)
(*         64: mov w2,#0x18 *)
| 0x40 => Some (4,
	Move R_X2 (Word 0x18 64)
)

(* 0x00194ae4: mov w0,#0x10 *)
(*         68: mov w0,#0x10 *)
| 0x44 => Some (4,
	Move R_X0 (Word 0x10 64)
)

(* 0x00194ae8: csel w0,w0,w2,ls *)
(*         72: csel w0,w0,w2,ls *)
| 0x48 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 0)) (Var R_ZR)) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
	) (* else *) (
		Move (V_TEMP 2) (Extract 31 0 (Var R_X2)) $;
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
	)
)

(* 0x00194aec: adrp x2,0x24e000 *)
(*         76: adrp x2,0x24e000 *)
| 0x4c => Some (4,
	Move R_X2 (Word 0x24e000 64)
)

(* 0x00194af0: add x2,x2,#0x738 *)
(*         80: add x2,x2,#0x738 *)
| 0x50 => Some (4,
	Move (V_TEMP 0) (Word 0x738 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1))
)

(* 0x00194af4: lsr w1,w1,w0 *)
(*         84: lsr w1,w1,w0 *)
| 0x54 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Ite (BinOp OP_LT (Var (V_TEMP 1)) (Word 32 64)) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Cast CAST_LOW 32 (Var (V_TEMP 1)))) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 32 32))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)

(* 0x00194af8: ldrb w1,[x2, w1, UXTW ] *)
(*         88: ldrb w1,[x2, w1, UXTW ] *)
| 0x58 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X1))) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)

(* 0x00194afc: add w0,w1,w0 *)
(*         92: add w0,w1,w0 *)
| 0x5c => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X0)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x00194b00: ret *)
(*         96: ret *)
| 0x60 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ffs_arm8.
Proof. Picinae_typecheck. Qed.

