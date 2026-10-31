(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: isnan
entry: 0x139f00 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition isnan_arm8 : program := fun _ a => match a with

(* 0x00139f00: fmov x1,d0 *)
(*          0: fmov x1,d0 *)
| 0x0 => Some (4,
	Move R_X1 (Extract 63 0 (Var R_Z0))
)

(* 0x00139f04: mov x0,#0x7ff0000000000000 *)
(*          4: mov x0,#0x7ff0000000000000 *)
| 0x4 => Some (4,
	Move R_X0 (Word 0x7ff0000000000000 64)
)

(* 0x00139f08: and x1,x1,#0x7fffffffffffffff *)
(*          8: and x1,x1,#0x7fffffffffffffff *)
| 0x8 => Some (4,
	Move R_X1 (BinOp OP_AND (Var R_X1) (Word 0x7fffffffffffffff 64))
)

(* 0x00139f0c: sub x0,x0,x1 *)
(*         12: sub x0,x0,x1 *)
| 0xc => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X0) (Var R_X1))
)

(* 0x00139f10: lsr x0,x0,#0x3f *)
(*         16: lsr x0,x0,#0x3f *)
| 0x10 => Some (4,
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Word 63 64))
)

(* 0x00139f14: ret *)
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

Theorem welltyped: welltyped_prog arm8typctx isnan_arm8.
Proof. Picinae_typecheck. Qed.

