(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ispunct
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ispunct_armv8 : program := fun _ a => match a with

(* 0x0011eeb4: sub w1,w0,#0x21 *)
(*    1175220: sub w1,w0,#0x21 *)
| 0x11eeb4 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x21 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0011eeb8: cmp w1,#0x5d *)
(*    1175224: cmp w1,#0x5d *)
| 0x11eeb8 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x5d 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x5d 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x5d 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x5d 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5d 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011eebc: b.ls 0x0011eec8 *)
(*    1175228: b.ls 0x0011eec8 *)
| 0x11eebc => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x11eec8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011eec0: mov w0,#0x0 *)
(*    1175232: mov w0,#0x0 *)
| 0x11eec0 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0011eec4: ret *)
(*    1175236: ret *)
| 0x11eec4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0011eec8: stp x29,x30,[sp, #-0x10]! *)
(*    1175240: stp x29,x30,[sp, #-0x10]! *)
| 0x11eec8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011eecc: mov x29,sp *)
(*    1175244: mov x29,sp *)
| 0x11eecc => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0011eed0: bl 0x0011edec *)
(*    1175248: bl 0x0011edec *)
| 0x11eed0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x11eed0 64) (Word 0x4 64)) $;
	Jmp (Word 0x11edec 64)
)

(* 0x0011eed4: cmp w0,#0x0 *)
(*    1175252: cmp w0,#0x0 *)
| 0x11eed4 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011eed8: cset w0,eq *)
(*    1175256: cset w0,eq *)
| 0x11eed8 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var R_ZR))
)

(* 0x0011eedc: ldp x29,x30,[sp], #0x10 *)
(*    1175260: ldp x29,x30,[sp], #0x10 *)
| 0x11eedc => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0011eee0: ret *)
(*    1175264: ret *)
| 0x11eee0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ispunct_armv8.
Proof. Picinae_typecheck. Qed.
