(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsnlen
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsnlen_armv8 : program := fun _ a => match a with

(* 0x0015fdb4: stp x29,x30,[sp, #-0x20]! *)
(*    1441204: stp x29,x30,[sp, #-0x20]! *)
| 0x15fdb4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fdb8: mov x2,x1 *)
(*    1441208: mov x2,x1 *)
| 0x15fdb8 => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0015fdbc: mov x29,sp *)
(*    1441212: mov x29,sp *)
| 0x15fdbc => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fdc0: stp x19,x20,[sp, #0x10] *)
(*    1441216: stp x19,x20,[sp, #0x10] *)
| 0x15fdc0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fdc4: mov x19,x0 *)
(*    1441220: mov x19,x0 *)
| 0x15fdc4 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fdc8: mov x20,x1 *)
(*    1441224: mov x20,x1 *)
| 0x15fdc8 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fdcc: mov w1,#0x0 *)
(*    1441228: mov w1,#0x0 *)
| 0x15fdcc => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015fdd0: bl 0x001601d0 *)
(*    1441232: bl 0x001601d0 *)
| 0x15fdd0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fdd0 64) (Word 0x4 64)) $;
	Jmp (Word 0x1601d0 64)
)

(* 0x0015fdd4: sub x19,x0,x19 *)
(*    1441236: sub x19,x0,x19 *)
| 0x15fdd4 => Some (4,
	Move R_X19 (BinOp OP_MINUS (Var R_X0) (Var R_X19))
)

(* 0x0015fdd8: cmp x0,#0x0 *)
(*    1441240: cmp x0,#0x0 *)
| 0x15fdd8 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015fddc: asr x19,x19,#0x2 *)
(*    1441244: asr x19,x19,#0x2 *)
| 0x15fddc => Some (4,
	Move R_X19 (BinOp OP_ARSHIFT (Var R_X19) (Word 0x2 64))
)

(* 0x0015fde0: csel x0,x19,x20,ne *)
(*    1441248: csel x0,x19,x20,ne *)
| 0x15fde0 => Some (4,
	Move (V_TEMP 0x1680) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0x1da80) (Var R_X19) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1680))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X20)
	) $;
	Move R_X0 (Var (V_TEMP 0x1da80))
)

(* 0x0015fde4: ldp x19,x20,[sp, #0x10] *)
(*    1441252: ldp x19,x20,[sp, #0x10] *)
| 0x15fde4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015fde8: ldp x29,x30,[sp], #0x20 *)
(*    1441256: ldp x29,x30,[sp], #0x20 *)
| 0x15fde8 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fdec: ret *)
(*    1441260: ret *)
| 0x15fdec => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsnlen_armv8.
Proof. Picinae_typecheck. Qed.
