(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: posix_spawnattr_setflags
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_setflags_armv8 : program := fun _ a => match a with

(* 0x00149558: sxth w1,w1 *)
(*    1348952: sxth w1,w1 *)
| 0x149558 => Some (4,
	Move (V_TEMP 0x3e380) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x3e500) (Cast CAST_SIGNED 32 (Extract 15 0 (Var (V_TEMP 0x3e380)))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3e500)))
)

(* 0x0014955c: cmp w1,#0xff *)
(*    1348956: cmp w1,#0xff *)
| 0x14955c => Some (4,
	Move (V_TEMP 0x1c500) (Word 0xff 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xff 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00149560: b.hi 0x00149570 *)
(*    1348960: b.hi 0x00149570 *)
| 0x149560 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x149570 64)
	) (* else *) (
		Nop
	)
)

(* 0x00149564: str w1,[x0] *)
(*    1348964: str w1,[x0] *)
| 0x149564 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00149568: mov w0,#0x0 *)
(*    1348968: mov w0,#0x0 *)
| 0x149568 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0014956c: ret *)
(*    1348972: ret *)
| 0x14956c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00149570: mov w0,#0x16 *)
(*    1348976: mov w0,#0x16 *)
| 0x149570 => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00149574: b 0x0014956c *)
(*    1348980: b 0x0014956c *)
| 0x149574 => Some (4,
	Jmp (Word 0x14956c 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx posix_spawnattr_setflags_armv8.
Proof. Picinae_typecheck. Qed.
