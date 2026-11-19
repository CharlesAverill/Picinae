(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setstacksize
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setstacksize_armv8 : program := fun _ a => match a with

(* 0x001611fc: sub x3,x1,#0x800 *)
(*    1446396: sub x3,x1,#0x800 *)
| 0x1611fc => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X1) (Word 0x800 64))
)

(* 0x00161200: mov x2,#0x3fffffffffffffff *)
(*    1446400: mov x2,#0x3fffffffffffffff *)
| 0x161200 => Some (4,
	Move R_X2 (Word 0x3fffffffffffffff 64)
)

(* 0x00161204: cmp x3,x2 *)
(*    1446404: cmp x3,x2 *)
| 0x161204 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X3) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00161208: b.hi 0x0016121c *)
(*    1446408: b.hi 0x0016121c *)
| 0x161208 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x16121c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016120c: str x1,[x0] *)
(*    1446412: str x1,[x0] *)
| 0x16120c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x00161210: str xzr,[x0, #0x10] *)
(*    1446416: str xzr,[x0, #0x10] *)
| 0x161210 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x00161214: mov w0,#0x0 *)
(*    1446420: mov w0,#0x0 *)
| 0x161214 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161218: ret *)
(*    1446424: ret *)
| 0x161218 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0016121c: mov w0,#0x16 *)
(*    1446428: mov w0,#0x16 *)
| 0x16121c => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00161220: b 0x00161218 *)
(*    1446432: b 0x00161218 *)
| 0x161220 => Some (4,
	Jmp (Word 0x161218 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setstacksize_armv8.
Proof. Picinae_typecheck. Qed.
