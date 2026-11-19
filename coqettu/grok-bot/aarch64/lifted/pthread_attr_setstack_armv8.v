(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setstack
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setstack_armv8 : program := fun _ a => match a with

(* 0x001611d0: sub x4,x2,#0x800 *)
(*    1446352: sub x4,x2,#0x800 *)
| 0x1611d0 => Some (4,
	Move R_X4 (BinOp OP_MINUS (Var R_X2) (Word 0x800 64))
)

(* 0x001611d4: mov x3,#0x3fffffffffffffff *)
(*    1446356: mov x3,#0x3fffffffffffffff *)
| 0x1611d4 => Some (4,
	Move R_X3 (Word 0x3fffffffffffffff 64)
)

(* 0x001611d8: cmp x4,x3 *)
(*    1446360: cmp x4,x3 *)
| 0x1611d8 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X4) (Var R_X3)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X4) (Var R_X3)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X4) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001611dc: b.hi 0x001611f4 *)
(*    1446364: b.hi 0x001611f4 *)
| 0x1611dc => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x1611f4 64)
	) (* else *) (
		Nop
	)
)

(* 0x001611e0: add x1,x1,x2 *)
(*    1446368: add x1,x1,x2 *)
| 0x1611e0 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x001611e4: str x2,[x0] *)
(*    1446372: str x2,[x0] *)
| 0x1611e4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x001611e8: str x1,[x0, #0x10] *)
(*    1446376: str x1,[x0, #0x10] *)
| 0x1611e8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x001611ec: mov w0,#0x0 *)
(*    1446380: mov w0,#0x0 *)
| 0x1611ec => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001611f0: ret *)
(*    1446384: ret *)
| 0x1611f0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001611f4: mov w0,#0x16 *)
(*    1446388: mov w0,#0x16 *)
| 0x1611f4 => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x001611f8: b 0x001611f0 *)
(*    1446392: b 0x001611f0 *)
| 0x1611f8 => Some (4,
	Jmp (Word 0x1611f0 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setstack_armv8.
Proof. Picinae_typecheck. Qed.
