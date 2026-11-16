(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wmemcpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wmemcpy_armv8 : program := fun _ a => match a with

(* 0x0016022c: mov x3,#0x0 *)
(*    1442348: mov x3,#0x0 *)
| 0x16022c => Some (4,
	Move R_X3 (Word 0x0 64)
)

(* 0x00160230: b 0x00160240 *)
(*    1442352: b 0x00160240 *)
| 0x160230 => Some (4,
	Jmp (Word 0x160240 64)
)

(* 0x00160234: ldr w4,[x1, x3, LSL #0x2] *)
(*    1442356: ldr w4,[x1, x3, LSL #0x2] *)
| 0x160234 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160238: str w4,[x0, x3, LSL #0x2] *)
(*    1442360: str w4,[x0, x3, LSL #0x2] *)
| 0x160238 => Some (4,
	Move (V_TEMP 0x3a200) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a200))) LittleE 4)
)

(* 0x0016023c: add x3,x3,#0x1 *)
(*    1442364: add x3,x3,#0x1 *)
| 0x16023c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x00160240: cmp x2,x3 *)
(*    1442368: cmp x2,x3 *)
| 0x160240 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X3)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X3)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X2) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160244: b.ne 0x00160234 *)
(*    1442372: b.ne 0x00160234 *)
| 0x160244 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x160234 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160248: ret *)
(*    1442376: ret *)
| 0x160248 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wmemcpy_armv8.
Proof. Picinae_typecheck. Qed.
