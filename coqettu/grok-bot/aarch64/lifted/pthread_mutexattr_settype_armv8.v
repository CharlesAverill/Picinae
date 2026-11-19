(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_mutexattr_settype
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_mutexattr_settype_armv8 : program := fun _ a => match a with

(* 0x00163dac: cmp w1,#0x2 *)
(*    1457580: cmp w1,#0x2 *)
| 0x163dac => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x2 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00163db0: b.hi 0x00163dcc *)
(*    1457584: b.hi 0x00163dcc *)
| 0x163db0 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x163dcc 64)
	) (* else *) (
		Nop
	)
)

(* 0x00163db4: ldr w2,[x0] *)
(*    1457588: ldr w2,[x0] *)
| 0x163db4 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00163db8: and w2,w2,#0xfffffffc *)
(*    1457592: and w2,w2,#0xfffffffc *)
| 0x163db8 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Word 0xfffffffc 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00163dbc: orr w2,w2,w1 *)
(*    1457596: orr w2,w2,w1 *)
| 0x163dbc => Some (4,
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x00163dc0: str w2,[x0] *)
(*    1457600: str w2,[x0] *)
| 0x163dc0 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X2))) LittleE 4)
)

(* 0x00163dc4: mov w0,#0x0 *)
(*    1457604: mov w0,#0x0 *)
| 0x163dc4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00163dc8: ret *)
(*    1457608: ret *)
| 0x163dc8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00163dcc: mov w0,#0x16 *)
(*    1457612: mov w0,#0x16 *)
| 0x163dcc => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00163dd0: b 0x00163dc8 *)
(*    1457616: b 0x00163dc8 *)
| 0x163dd0 => Some (4,
	Jmp (Word 0x163dc8 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_mutexattr_settype_armv8.
Proof. Picinae_typecheck. Qed.
