(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: iswspace
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswspace_armv8 : program := fun _ a => match a with

(* 0x0011f210: cbnz w0,0x0011f218 *)
(*    1176080: cbnz w0,0x0011f218 *)
| 0x11f210 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x11f218 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011f214: ret *)
(*    1176084: ret *)
| 0x11f214 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0011f218: stp x29,x30,[sp, #-0x10]! *)
(*    1176088: stp x29,x30,[sp, #-0x10]! *)
| 0x11f218 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011f21c: mov w1,w0 *)
(*    1176092: mov w1,w0 *)
| 0x11f21c => Some (4,
	Move R_X1 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0011f220: adrp x0,0x174000 *)
(*    1176096: adrp x0,0x174000 *)
| 0x11f220 => Some (4,
	Move R_X0 (Word 0x174000 64)
)

(* 0x0011f224: mov x29,sp *)
(*    1176100: mov x29,sp *)
| 0x11f224 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0011f228: add x0,x0,#0xe0 *)
(*    1176104: add x0,x0,#0xe0 *)
| 0x11f228 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0xe0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0011f22c: bl 0x0015fab4 *)
(*    1176108: bl 0x0015fab4 *)
| 0x11f22c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x11f22c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fab4 64)
)

(* 0x0011f230: cmp x0,#0x0 *)
(*    1176112: cmp x0,#0x0 *)
| 0x11f230 => Some (4,
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

(* 0x0011f234: cset w0,ne *)
(*    1176116: cset w0,ne *)
| 0x11f234 => Some (4,
	Move (V_TEMP 0x2300) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2300)))
)

(* 0x0011f238: ldp x29,x30,[sp], #0x10 *)
(*    1176120: ldp x29,x30,[sp], #0x10 *)
| 0x11f238 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0011f23c: ret *)
(*    1176124: ret *)
| 0x11f23c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx iswspace_armv8.
Proof. Picinae_typecheck. Qed.
