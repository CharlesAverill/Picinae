(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: htons
entry: 0x1f9d00 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition htons_arm8 : program := fun _ a => match a with

(* 0x001f9d00: rev16 w0,w0 *)
(*          0: rev16 w0,w0 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001f9d04: ret *)
(*          4: ret *)
| 0x4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx htons_arm8.
Proof. Picinae_typecheck. Qed.

