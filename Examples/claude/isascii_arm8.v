(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: isascii
entry: 0x134470 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition isascii_arm8 : program := fun _ a => match a with

(* 0x00134470: tst w0,#0xffffff80 *)
(*          0: tst w0,#0xffffff80 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffffff80 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x00134474: cset w0,eq *)
(*          4: cset w0,eq *)
| 0x4 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var R_ZR))
)

(* 0x00134478: ret *)
(*          8: ret *)
| 0x8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx isascii_arm8.
Proof. Picinae_typecheck. Qed.

