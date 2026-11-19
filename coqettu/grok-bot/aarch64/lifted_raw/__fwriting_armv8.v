(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __fwriting
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __fwriting_armv8 : program := fun _ a => match a with

(* 0x0015390c: ldr w1,[x0] *)
(*    1390860: ldr w1,[x0] *)
| 0x15390c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00153910: tbnz w1,#0x2,0x00153924 *)
(*    1390864: tbnz w1,#0x2,0x00153924 *)
| 0x153910 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x2 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x153924 64)
	) (* else *) (
		Nop
	)
)

(* 0x00153914: ldr x0,[x0, #0x20] *)
(*    1390868: ldr x0,[x0, #0x20] *)
| 0x153914 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00153918: cmp x0,#0x0 *)
(*    1390872: cmp x0,#0x0 *)
| 0x153918 => Some (4,
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

(* 0x0015391c: cset w0,ne *)
(*    1390876: cset w0,ne *)
| 0x15391c => Some (4,
	Move (V_TEMP 0x2300) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2300)))
)

(* 0x00153920: ret *)
(*    1390880: ret *)
| 0x153920 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00153924: mov w0,#0x1 *)
(*    1390884: mov w0,#0x1 *)
| 0x153924 => Some (4,
	Move R_X0 (Word 0x1 64)
)

(* 0x00153928: b 0x00153920 *)
(*    1390888: b 0x00153920 *)
| 0x153928 => Some (4,
	Jmp (Word 0x153920 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __fwriting_armv8.
Proof. Picinae_typecheck. Qed.
