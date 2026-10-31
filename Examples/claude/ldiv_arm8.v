(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: ldiv
entry: 0x13d860 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition ldiv_arm8 : program := fun _ a => match a with

(* 0x0013d860: mov x2,x0 *)
(*          0: mov x2,x0 *)
| 0x0 => Some (4,
	Move R_X2 (Var R_X0)
)

(* 0x0013d864: sdiv x0,x0,x1 *)
(*          4: sdiv x0,x0,x1 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X1) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Move R_X0 (Var (V_TEMP 0))
	) (* else *) (
		Move (V_TEMP 0) (BinOp OP_SDIVIDE (Var R_X0) (Var R_X1)) $;
		Move R_X0 (Var (V_TEMP 0))
	)
)

(* 0x0013d868: msub x1,x0,x1,x2 *)
(*          8: msub x1,x0,x1,x2 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_X0) (Var R_X1)) $;
	Move R_X1 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0)))
)

(* 0x0013d86c: ret *)
(*         12: ret *)
| 0xc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ldiv_arm8.
Proof. Picinae_typecheck. Qed.

