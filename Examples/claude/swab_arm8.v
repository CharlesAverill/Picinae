(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: swab
entry: 0x195eb0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition swab_arm8 : program := fun _ a => match a with

(* 0x00195eb0: and x2,x2,#-0x2 *)
(*          0: and x2,x2,#-0x2 *)
| 0x0 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xfffffffffffffffe 64))
)

(* 0x00195eb4: cmp x2,#0x1 *)
(*          4: cmp x2,#0x1 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00195eb8: b.le 0x00195ee0 *)
(*          8: b.le 0x00195ee0 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_NG) (Var R_OV))) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var R_ZR) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x30 64)
	) (* else *) (
		Nop
	)
)

(* 0x00195ebc: sub x6,x0,#0x1 *)
(*         12: sub x6,x0,#0x1 *)
| 0xc => Some (4,
	Move R_X6 (BinOp OP_MINUS (Var R_X0) (Word 0x1 64))
)

(* 0x00195ec0: add x5,x1,#0x1 *)
(*         16: add x5,x1,#0x1 *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 1))
)

(* 0x00195ec4: nop *)
(*         20: nop *)
| 0x14 => Some (4,
	Nop
)

(* 0x00195ec8: ldrb w4,[x6, x2, LSL ] *)
(*         24: ldrb w4,[x6, x2, LSL ] *)
| 0x18 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X6) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)

(* 0x00195ecc: sub x2,x2,#0x2 *)
(*         28: sub x2,x2,#0x2 *)
| 0x1c => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x2 64))
)

(* 0x00195ed0: ldrb w3,[x0, x2, LSL ] *)
(*         32: ldrb w3,[x0, x2, LSL ] *)
| 0x20 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)

(* 0x00195ed4: strb w4,[x1, x2, LSL ] *)
(*         36: strb w4,[x1, x2, LSL ] *)
| 0x24 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 1) (Var R_X2) $;
	Move (V_TEMP 2) (Var (V_TEMP 1)) $;
	Move (V_TEMP 2) (BinOp OP_LSHIFT (Var (V_TEMP 2)) (Word 0 64)) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 4)) LittleE 1)
)

(* 0x00195ed8: strb w3,[x5, x2, LSL ] *)
(*         40: strb w3,[x5, x2, LSL ] *)
| 0x28 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 1) (Var R_X2) $;
	Move (V_TEMP 2) (Var (V_TEMP 1)) $;
	Move (V_TEMP 2) (BinOp OP_LSHIFT (Var (V_TEMP 2)) (Word 0 64)) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 4)) LittleE 1)
)

(* 0x00195edc: cbnz x2,0x00195ec8 *)
(*         44: cbnz x2,0x00195ec8 *)
| 0x2c => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_X2) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x18 64)
	) (* else *) (
		Nop
	)
)

(* 0x00195ee0: ret *)
(*         48: ret *)
| 0x30 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx swab_arm8.
Proof. Picinae_typecheck. Qed.

