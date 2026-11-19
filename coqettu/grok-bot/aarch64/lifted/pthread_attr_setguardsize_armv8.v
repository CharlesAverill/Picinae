(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setguardsize
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setguardsize_armv8 : program := fun _ a => match a with

(* 0x0016115c: mov x2,#0x1fffffffffffffff *)
(*    1446236: mov x2,#0x1fffffffffffffff *)
| 0x16115c => Some (4,
	Move R_X2 (Word 0x1fffffffffffffff 64)
)

(* 0x00161160: cmp x1,x2 *)
(*    1446240: cmp x1,x2 *)
| 0x161160 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00161164: b.hi 0x00161174 *)
(*    1446244: b.hi 0x00161174 *)
| 0x161164 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x161174 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161168: str x1,[x0, #0x8] *)
(*    1446248: str x1,[x0, #0x8] *)
| 0x161168 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x0016116c: mov w0,#0x0 *)
(*    1446252: mov w0,#0x0 *)
| 0x16116c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161170: ret *)
(*    1446256: ret *)
| 0x161170 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00161174: mov w0,#0x16 *)
(*    1446260: mov w0,#0x16 *)
| 0x161174 => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00161178: b 0x00161170 *)
(*    1446264: b 0x00161170 *)
| 0x161178 => Some (4,
	Jmp (Word 0x161170 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setguardsize_armv8.
Proof. Picinae_typecheck. Qed.
