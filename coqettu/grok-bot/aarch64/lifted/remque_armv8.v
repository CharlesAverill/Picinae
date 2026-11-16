(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: remque
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition remque_armv8 : program := fun _ a => match a with

(* 0x00151424: ldr x1,[x0] *)
(*    1381412: ldr x1,[x0] *)
| 0x151424 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151428: cbz x1,0x00151434 *)
(*    1381416: cbz x1,0x00151434 *)
| 0x151428 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x151434 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015142c: ldr x2,[x0, #0x8] *)
(*    1381420: ldr x2,[x0, #0x8] *)
| 0x15142c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00151430: str x2,[x1, #0x8] *)
(*    1381424: str x2,[x1, #0x8] *)
| 0x151430 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x00151434: ldr x1,[x0, #0x8] *)
(*    1381428: ldr x1,[x0, #0x8] *)
| 0x151434 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00151438: cbz x1,0x00151444 *)
(*    1381432: cbz x1,0x00151444 *)
| 0x151438 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x151444 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015143c: ldr x0,[x0] *)
(*    1381436: ldr x0,[x0] *)
| 0x15143c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151440: str x0,[x1] *)
(*    1381440: str x0,[x1] *)
| 0x151440 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00151444: ret *)
(*    1381444: ret *)
| 0x151444 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx remque_armv8.
Proof. Picinae_typecheck. Qed.
