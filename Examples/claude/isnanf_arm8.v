(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: isnanf
entry: 0x13a210 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition isnanf_arm8 : program := fun _ a => match a with

(* 0x0013a210: fmov w1,s0 *)
(*          0: fmov w1,s0 *)
| 0x0 => Some (4,
	Move R_X1 (Concat (Word 0x0 32) (Extract 31 0 (Var R_Z0)))
)

(* 0x0013a214: mov w0,#0x7f800000 *)
(*          4: mov w0,#0x7f800000 *)
| 0x4 => Some (4,
	Move R_X0 (Word 0x7f800000 64)
)

(* 0x0013a218: and w1,w1,#0x7fffffff *)
(*          8: and w1,w1,#0x7fffffff *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0x7fffffff 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a21c: sub w0,w0,w1 *)
(*         12: sub w0,w0,w1 *)
| 0xc => Some (4,
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a220: lsr w0,w0,#0x1f *)
(*         16: lsr w0,w0,#0x1f *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a224: ret *)
(*         20: ret *)
| 0x14 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx isnanf_arm8.
Proof. Picinae_typecheck. Qed.

