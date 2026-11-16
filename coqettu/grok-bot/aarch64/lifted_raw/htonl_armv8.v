(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: htonl
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition htonl_armv8 : program := fun _ a => match a with

(* 0x00141de8: rev w0,w0 *)
(*    1318376: rev w0,w0 *)
| 0x141de8 => Some (4,
	Move (V_TEMP 0x2f800) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f880)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f980) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x2fa00) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f980)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2f900)) (Var (V_TEMP 0x2fa00))) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))
)

(* 0x00141dec: ret *)
(*    1318380: ret *)
| 0x141dec => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx htonl_armv8.
Proof. Picinae_typecheck. Qed.
