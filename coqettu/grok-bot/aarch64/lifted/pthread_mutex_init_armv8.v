(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_mutex_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_mutex_init_armv8 : program := fun _ a => match a with

(* 0x0016360c: stp xzr,xzr,[x0] *)
(*    1455628: stp xzr,xzr,[x0] *)
| 0x16360c => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00163610: stp xzr,xzr,[x0, #0x10] *)
(*    1455632: stp xzr,xzr,[x0, #0x10] *)
| 0x163610 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00163614: str xzr,[x0, #0x20] *)
(*    1455636: str xzr,[x0, #0x20] *)
| 0x163614 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x00163618: cbz x1,0x00163624 *)
(*    1455640: cbz x1,0x00163624 *)
| 0x163618 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x163624 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016361c: ldr w1,[x1] *)
(*    1455644: ldr w1,[x1] *)
| 0x16361c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00163620: str w1,[x0] *)
(*    1455648: str w1,[x0] *)
| 0x163620 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00163624: mov w0,#0x0 *)
(*    1455652: mov w0,#0x0 *)
| 0x163624 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00163628: ret *)
(*    1455656: ret *)
| 0x163628 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_mutex_init_armv8.
Proof. Picinae_typecheck. Qed.
