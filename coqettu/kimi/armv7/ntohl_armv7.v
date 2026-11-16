(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: ntohl
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ntohl_armv7 : program := fun _ a => match a with

(* 0x000531de: rev r0,r0 *)
(*     340446: rev r0,r0 *)
| 0x531de => Some (2,
	Move (V_TEMP 0xb9800) (BinOp OP_AND (Var R_R0) (Word 0xff 32)) $;
	Move (V_TEMP 0xb9880) (BinOp OP_RSHIFT (Var R_R0) (Word 0x8 32)) $;
	Move (V_TEMP 0xb9980) (BinOp OP_AND (Var (V_TEMP 0xb9880)) (Word 0xff 32)) $;
	Move (V_TEMP 0xb9a00) (BinOp OP_RSHIFT (Var R_R0) (Word 0x10 32)) $;
	Move (V_TEMP 0xb9b00) (BinOp OP_AND (Var (V_TEMP 0xb9a00)) (Word 0xff 32)) $;
	Move (V_TEMP 0xb9b80) (BinOp OP_RSHIFT (Var R_R0) (Word 0x18 32)) $;
	Move (V_TEMP 0xb9c80) (BinOp OP_AND (Var (V_TEMP 0xb9b80)) (Word 0xff 32)) $;
	Move (V_TEMP 0xb9d00) (BinOp OP_LSHIFT (Var (V_TEMP 0xb9800)) (Word 0x18 32)) $;
	Move (V_TEMP 0xb9d80) (BinOp OP_LSHIFT (Var (V_TEMP 0xb9980)) (Word 0x10 32)) $;
	Move (V_TEMP 0xb9e00) (BinOp OP_OR (Var (V_TEMP 0xb9d00)) (Var (V_TEMP 0xb9d80))) $;
	Move (V_TEMP 0xb9e80) (BinOp OP_LSHIFT (Var (V_TEMP 0xb9b00)) (Word 0x8 32)) $;
	Move (V_TEMP 0xb9f00) (BinOp OP_OR (Var (V_TEMP 0xb9e00)) (Var (V_TEMP 0xb9e80))) $;
	Move R_R0 (BinOp OP_OR (Var (V_TEMP 0xb9f00)) (Var (V_TEMP 0xb9c80)))
)

(* 0x000531e0: bx lr *)
(*     340448: bx lr *)
| 0x531e0 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx ntohl_armv7.
Proof. Picinae_typecheck. Qed.
