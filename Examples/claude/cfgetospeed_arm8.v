(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: cfgetospeed
entry: 0x1e0ed0 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition cfgetospeed_arm8 : program := fun _ a => match a with

(* 0x001e0ed0: ldr w0,[x0, #0x8] *)
(*          0: ldr w0,[x0, #0x8] *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x001e0ed4: mov w1,#0x100f *)
(*          4: mov w1,#0x100f *)
| 0x4 => Some (4,
	Move R_X1 (Word 0x100f 64)
)

(* 0x001e0ed8: and w0,w0,w1 *)
(*          8: and w0,w0,w1 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x001e0edc: ret *)
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

Theorem welltyped: welltyped_prog arm8typctx cfgetospeed_arm8.
Proof. Picinae_typecheck. Qed.

