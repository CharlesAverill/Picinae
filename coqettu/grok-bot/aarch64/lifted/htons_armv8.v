(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: htons
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition htons_armv8 : program := fun _ a => match a with

(* 0x00141df0: rev16 w0,w0 *)
(*    1318384: rev16 w0,w0 *)
| 0x141df0 => Some (4,
	Move (V_TEMP 0x30400) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x30480) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x30500) (BinOp OP_RSHIFT (Var (V_TEMP 0x30480)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30580) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x30600) (BinOp OP_LSHIFT (Var (V_TEMP 0x30580)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30400) (BinOp OP_OR (Var (V_TEMP 0x30500)) (Var (V_TEMP 0x30600))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x30400)))
)

(* 0x00141df4: ret *)
(*    1318388: ret *)
| 0x141df4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx htons_armv8.
Proof. Picinae_typecheck. Qed.
