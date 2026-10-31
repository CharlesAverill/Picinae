(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: gnu_dev_makedev
entry: 0x1e9a20 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition gnu_dev_makedev_arm8 : program := fun _ a => match a with

(* 0x001e9a20: and x3,x1,#0xff *)
(*          0: and x3,x1,#0xff *)
| 0x0 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X1) (Word 0xff 64))
)

(* 0x001e9a24: lsl x2,x0,#0x20 *)
(*          4: lsl x2,x0,#0x20 *)
| 0x4 => Some (4,
	Move R_X2 (BinOp OP_LSHIFT (Var R_X0) (Word 32 64))
)

(* 0x001e9a28: ubfiz x1,x1,#0xc,#0x20 *)
(*          8: ubfiz x1,x1,#0xc,#0x20 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 52 64)) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x40 64) (Word 0x34 64)) $;
	Move (V_TEMP 3) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xffffffff000 64)) $;
	Move R_X1 (BinOp OP_AND (Var (V_TEMP 5)) (Word 0xfffffffffff 64))
)

(* 0x001e9a2c: and x2,x2,#-0x100000000000 *)
(*         12: and x2,x2,#-0x100000000000 *)
| 0xc => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xfffff00000000000 64))
)

(* 0x001e9a30: and x1,x1,#0xffffff00000 *)
(*         16: and x1,x1,#0xffffff00000 *)
| 0x10 => Some (4,
	Move R_X1 (BinOp OP_AND (Var R_X1) (Word 0xffffff00000 64))
)

(* 0x001e9a34: ubfiz x0,x0,#0x8,#0xc *)
(*         20: ubfiz x0,x0,#0x8,#0xc *)
| 0x14 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 56 64)) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x40 64) (Word 0x38 64)) $;
	Move (V_TEMP 3) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xfff00 64)) $;
	Move R_X0 (BinOp OP_AND (Var (V_TEMP 5)) (Word 0xfffff 64))
)

(* 0x001e9a38: orr x1,x1,x3 *)
(*         24: orr x1,x1,x3 *)
| 0x18 => Some (4,
	Move R_X1 (BinOp OP_OR (Var R_X1) (Var R_X3))
)

(* 0x001e9a3c: orr x0,x2,x0 *)
(*         28: orr x0,x2,x0 *)
| 0x1c => Some (4,
	Move R_X0 (BinOp OP_OR (Var R_X2) (Var R_X0))
)

(* 0x001e9a40: orr x0,x1,x0 *)
(*         32: orr x0,x1,x0 *)
| 0x20 => Some (4,
	Move R_X0 (BinOp OP_OR (Var R_X1) (Var R_X0))
)

(* 0x001e9a44: ret *)
(*         36: ret *)
| 0x24 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx gnu_dev_makedev_arm8.
Proof. Picinae_typecheck. Qed.

