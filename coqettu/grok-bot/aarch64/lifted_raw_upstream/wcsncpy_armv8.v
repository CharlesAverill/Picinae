(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsncpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsncpy_armv8 : program := fun _ a => match a with

(* 0x0015fd70: stp x29,x30,[sp, #-0x20]! *)
(*    1441136: stp x29,x30,[sp, #-0x20]! *)
| 0x15fd70 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fd74: mov x29,sp *)
(*    1441140: mov x29,sp *)
| 0x15fd74 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fd78: str x19,[sp, #0x10] *)
(*    1441144: str x19,[sp, #0x10] *)
| 0x15fd78 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015fd7c: mov x19,x0 *)
(*    1441148: mov x19,x0 *)
| 0x15fd7c => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fd80: b 0x0015fd8c *)
(*    1441152: b 0x0015fd8c *)
| 0x15fd80 => Some (4,
	Jmp (Word 0x15fd8c 64)
)

(* 0x0015fd84: sub x2,x2,#0x1 *)
(*    1441156: sub x2,x2,#0x1 *)
| 0x15fd84 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015fd88: str w3,[x0], #0x4 *)
(*    1441160: str w3,[x0], #0x4 *)
| 0x15fd88 => Some (4,
	Move (V_TEMP 0x3a100) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x4 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a100))) LittleE 4)
)

(* 0x0015fd8c: cbz x2,0x0015fd9c *)
(*    1441164: cbz x2,0x0015fd9c *)
| 0x15fd8c => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15fd9c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fd90: ldr w3,[x1] *)
(*    1441168: ldr w3,[x1] *)
| 0x15fd90 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fd94: add x1,x1,#0x4 *)
(*    1441172: add x1,x1,#0x4 *)
| 0x15fd94 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015fd98: cbnz w3,0x0015fd84 *)
(*    1441176: cbnz w3,0x0015fd84 *)
| 0x15fd98 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15fd84 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fd9c: mov w1,#0x0 *)
(*    1441180: mov w1,#0x0 *)
| 0x15fd9c => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015fda0: bl 0x00160294 *)
(*    1441184: bl 0x00160294 *)
| 0x15fda0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fda0 64) (Word 0x4 64)) $;
	Jmp (Word 0x160294 64)
)

(* 0x0015fda4: mov x0,x19 *)
(*    1441188: mov x0,x19 *)
| 0x15fda4 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015fda8: ldr x19,[sp, #0x10] *)
(*    1441192: ldr x19,[sp, #0x10] *)
| 0x15fda8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fdac: ldp x29,x30,[sp], #0x20 *)
(*    1441196: ldp x29,x30,[sp], #0x20 *)
| 0x15fdac => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fdb0: ret *)
(*    1441200: ret *)
| 0x15fdb0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsncpy_armv8.
Proof. Picinae_typecheck. Qed.
