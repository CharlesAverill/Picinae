(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: imaxdiv
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition imaxdiv_armv8 : program := fun _ a => match a with

(* 0x0015d378: mov x2,x0 *)
(*    1430392: mov x2,x0 *)
| 0x15d378 => Some (4,
	Move R_X2 (Var R_X0)
)

(* 0x0015d37c: sdiv x0,x0,x1 *)
(*    1430396: sdiv x0,x0,x1 *)
| 0x15d37c => Some (4,
	Move (V_TEMP 0x36100) (Word 0x0 64) $;
	Move (V_TEMP 0x36180) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x36180))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x36100) (BinOp OP_SDIVIDE (Var R_X0) (Var R_X1))
	) $;
	Move R_X0 (Var (V_TEMP 0x36100))
)

(* 0x0015d380: msub x1,x0,x1,x2 *)
(*    1430400: msub x1,x0,x1,x2 *)
| 0x15d380 => Some (4,
	Move (V_TEMP 0x2ac80) (BinOp OP_TIMES (Var R_X0) (Var R_X1)) $;
	Move R_X1 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x2ac80)))
)

(* 0x0015d384: ret *)
(*    1430404: ret *)
| 0x15d384 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx imaxdiv_armv8.
Proof. Picinae_typecheck. Qed.
