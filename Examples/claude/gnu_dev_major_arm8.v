(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: gnu_dev_major
entry: 0x1e9a00 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition gnu_dev_major_arm8 : program := fun _ a => match a with

(* 0x001e9a00: mov x1,x0 *)
(*          0: mov x1,x0 *)
| 0x0 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x001e9a04: lsr x0,x0,#0x20 *)
(*          4: lsr x0,x0,#0x20 *)
| 0x4 => Some (4,
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Word 32 64))
)

(* 0x001e9a08: bfxil w0,w1,#0x8,#0xc *)
(*          8: bfxil w0,w1,#0x8,#0xc *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_MINUS (Word 0x20 32) (Word 0xc 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Word 0xffffffff 32) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 8 32)) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 3))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 6)))
)

(* 0x001e9a0c: ret *)
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

Theorem welltyped: welltyped_prog arm8typctx gnu_dev_major_arm8.
Proof. Picinae_typecheck. Qed.

