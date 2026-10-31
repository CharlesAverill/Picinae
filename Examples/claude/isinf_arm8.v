(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: isinf
entry: 0x139ed0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition isinf_arm8 : program := fun _ a => match a with

(* 0x00139ed0: fmov x0,d0 *)
(*          0: fmov x0,d0 *)
| 0x0 => Some (4,
	Move R_X0 (Extract 63 0 (Var R_Z0))
)

(* 0x00139ed4: and x2,x0,#0x7fffffffffffffff *)
(*          4: and x2,x0,#0x7fffffffffffffff *)
| 0x4 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X0) (Word 0x7fffffffffffffff 64))
)

(* 0x00139ed8: asr x0,x0,#0x3e *)
(*          8: asr x0,x0,#0x3e *)
| 0x8 => Some (4,
	Move R_X0 (BinOp OP_ARSHIFT (Var R_X0) (Word 62 64))
)

(* 0x00139edc: eor x2,x2,#0x7ff0000000000000 *)
(*         12: eor x2,x2,#0x7ff0000000000000 *)
| 0xc => Some (4,
	Move R_X2 (BinOp OP_XOR (Var R_X2) (Word 0x7ff0000000000000 64))
)

(* 0x00139ee0: neg x1,x2 *)
(*         16: neg x1,x2 *)
| 0x10 => Some (4,
	Move R_X1 (UnOp OP_NEG (Var R_X2))
)

(* 0x00139ee4: orr x1,x1,x2 *)
(*         20: orr x1,x1,x2 *)
| 0x14 => Some (4,
	Move R_X1 (BinOp OP_OR (Var R_X1) (Var R_X2))
)

(* 0x00139ee8: asr x1,x1,#0x3f *)
(*         24: asr x1,x1,#0x3f *)
| 0x18 => Some (4,
	Move R_X1 (BinOp OP_ARSHIFT (Var R_X1) (Word 63 64))
)

(* 0x00139eec: bic w0,w0,w1 *)
(*         28: bic w0,w0,w1 *)
| 0x1c => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Var (V_TEMP 1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))
)

(* 0x00139ef0: ret *)
(*         32: ret *)
| 0x20 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx isinf_arm8.
Proof. Picinae_typecheck. Qed.

