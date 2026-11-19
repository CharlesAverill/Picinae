(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_getcpuclockid
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_getcpuclockid_armv8 : program := fun _ a => match a with

(* 0x00162fdc: ldr w0,[x0, #0x20] *)
(*    1454044: ldr w0,[x0, #0x20] *)
| 0x162fdc => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00162fe0: mvn w0,w0 *)
(*    1454048: mvn w0,w0 *)
| 0x162fe0 => Some (4,
	Move (V_TEMP 0x2b100) (UnOp OP_NOT (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2b100)))
)

(* 0x00162fe4: lsl w0,w0,#0x3 *)
(*    1454052: lsl w0,w0,#0x3 *)
| 0x162fe4 => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x3 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x00162fe8: add w0,w0,#0x6 *)
(*    1454056: add w0,w0,#0x6 *)
| 0x162fe8 => Some (4,
	Move (V_TEMP 0x11680) (Word 0x6 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11680)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11780) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11780)))
)

(* 0x00162fec: str w0,[x1] *)
(*    1454060: str w0,[x1] *)
| 0x162fec => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X0))) LittleE 4)
)

(* 0x00162ff0: mov w0,#0x0 *)
(*    1454064: mov w0,#0x0 *)
| 0x162ff0 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00162ff4: ret *)
(*    1454068: ret *)
| 0x162ff4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_getcpuclockid_armv8.
Proof. Picinae_typecheck. Qed.
