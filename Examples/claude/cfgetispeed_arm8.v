(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: cfgetispeed
entry: 0x1e0ee0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition cfgetispeed_arm8 : program := fun _ a => match a with

(* 0x001e0ee0: ldr w1,[x0] *)
(*          0: ldr w1,[x0] *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x001e0ee4: tbnz w1,#0x1f,0x001e0ef8 *)
(*          4: tbnz w1,#0x1f,0x001e0ef8 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (
		Jmp (Word 0x18 64)
	) (* else *) (
		Nop
	)
)

(* 0x001e0ee8: ldr w0,[x0, #0x8] *)
(*          8: ldr w0,[x0, #0x8] *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x001e0eec: mov w1,#0x100f *)
(*         12: mov w1,#0x100f *)
| 0xc => Some (4,
	Move R_X1 (Word 0x100f 64)
)

(* 0x001e0ef0: and w0,w0,w1 *)
(*         16: and w0,w0,w1 *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001e0ef4: ret *)
(*         20: ret *)
| 0x14 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001e0ef8: mov w0,#0x0 *)
(*         24: mov w0,#0x0 *)
| 0x18 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001e0efc: ret *)
(*         28: ret *)
| 0x1c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx cfgetispeed_arm8.
Proof. Picinae_typecheck. Qed.

