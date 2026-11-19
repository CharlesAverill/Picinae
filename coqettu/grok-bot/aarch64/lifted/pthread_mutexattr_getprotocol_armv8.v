(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_mutexattr_getprotocol
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_mutexattr_getprotocol_armv8 : program := fun _ a => match a with

(* 0x00161094: ldr w0,[x0] *)
(*    1446036: ldr w0,[x0] *)
| 0x161094 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00161098: ubfx x0,x0,#0x3,#0x1 *)
(*    1446040: ubfx x0,x0,#0x3,#0x1 *)
| 0x161098 => Some (4,
	Move (V_TEMP 0x41100) (Var R_X0) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x3 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x3 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xe000000000000001 64)) $;
	Move R_X0 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x1 64))
)

(* 0x0016109c: str w0,[x1] *)
(*    1446044: str w0,[x1] *)
| 0x16109c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X0))) LittleE 4)
)

(* 0x001610a0: mov w0,#0x0 *)
(*    1446048: mov w0,#0x0 *)
| 0x1610a0 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001610a4: ret *)
(*    1446052: ret *)
| 0x1610a4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_mutexattr_getprotocol_armv8.
Proof. Picinae_typecheck. Qed.
