(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcslen
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcslen_armv8 : program := fun _ a => match a with

(* 0x0015fc18: mov x1,x0 *)
(*    1440792: mov x1,x0 *)
| 0x15fc18 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x0015fc1c: b 0x0015fc24 *)
(*    1440796: b 0x0015fc24 *)
| 0x15fc1c => Some (4,
	Jmp (Word 0x15fc24 64)
)

(* 0x0015fc20: add x1,x1,#0x4 *)
(*    1440800: add x1,x1,#0x4 *)
| 0x15fc20 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015fc24: ldr w2,[x1] *)
(*    1440804: ldr w2,[x1] *)
| 0x15fc24 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fc28: cbnz w2,0x0015fc20 *)
(*    1440808: cbnz w2,0x0015fc20 *)
| 0x15fc28 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15fc20 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fc2c: sub x0,x1,x0 *)
(*    1440812: sub x0,x1,x0 *)
| 0x15fc2c => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x0015fc30: asr x0,x0,#0x2 *)
(*    1440816: asr x0,x0,#0x2 *)
| 0x15fc30 => Some (4,
	Move R_X0 (BinOp OP_ARSHIFT (Var R_X0) (Word 0x2 64))
)

(* 0x0015fc34: ret *)
(*    1440820: ret *)
| 0x15fc34 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcslen_armv8.
Proof. Picinae_typecheck. Qed.
