(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsncat
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsncat_armv8 : program := fun _ a => match a with

(* 0x0015fcdc: stp x29,x30,[sp, #-0x30]! *)
(*    1440988: stp x29,x30,[sp, #-0x30]! *)
| 0x15fcdc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fce0: mov x29,sp *)
(*    1440992: mov x29,sp *)
| 0x15fce0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fce4: str x21,[sp, #0x20] *)
(*    1440996: str x21,[sp, #0x20] *)
| 0x15fce4 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0015fce8: mov x21,x0 *)
(*    1441000: mov x21,x0 *)
| 0x15fce8 => Some (4,
	Move R_X21 (Var R_X0)
)

(* 0x0015fcec: stp x19,x20,[sp, #0x10] *)
(*    1441004: stp x19,x20,[sp, #0x10] *)
| 0x15fcec => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fcf0: mov x20,x1 *)
(*    1441008: mov x20,x1 *)
| 0x15fcf0 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fcf4: mov x19,x2 *)
(*    1441012: mov x19,x2 *)
| 0x15fcf4 => Some (4,
	Move R_X19 (Var R_X2)
)

(* 0x0015fcf8: bl 0x0015fc18 *)
(*    1441016: bl 0x0015fc18 *)
| 0x15fcf8 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fcf8 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fc18 64)
)

(* 0x0015fcfc: add x0,x21,x0, LSL #0x2 *)
(*    1441020: add x0,x21,x0, LSL #0x2 *)
| 0x15fcfc => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) (Var R_X21))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X21) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X21) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015fd00: b 0x0015fd08 *)
(*    1441024: b 0x0015fd08 *)
| 0x15fd00 => Some (4,
	Jmp (Word 0x15fd08 64)
)

(* 0x0015fd04: str w1,[x0], #0x4 *)
(*    1441028: str w1,[x0], #0x4 *)
| 0x15fd04 => Some (4,
	Move (V_TEMP 0x3a100) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x4 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a100))) LittleE 4)
)

(* 0x0015fd08: cbz x19,0x0015fd1c *)
(*    1441032: cbz x19,0x0015fd1c *)
| 0x15fd08 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X19) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15fd1c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fd0c: ldr w1,[x20] *)
(*    1441036: ldr w1,[x20] *)
| 0x15fd0c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X20) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fd10: sub x19,x19,#0x1 *)
(*    1441040: sub x19,x19,#0x1 *)
| 0x15fd10 => Some (4,
	Move R_X19 (BinOp OP_MINUS (Var R_X19) (Word 0x1 64))
)

(* 0x0015fd14: add x20,x20,#0x4 *)
(*    1441044: add x20,x20,#0x4 *)
| 0x15fd14 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x11b80))
)

(* 0x0015fd18: cbnz w1,0x0015fd04 *)
(*    1441048: cbnz w1,0x0015fd04 *)
| 0x15fd18 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15fd04 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fd1c: str wzr,[x0] *)
(*    1441052: str wzr,[x0] *)
| 0x15fd1c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x300))) LittleE 4)
)

(* 0x0015fd20: mov x0,x21 *)
(*    1441056: mov x0,x21 *)
| 0x15fd20 => Some (4,
	Move R_X0 (Var R_X21)
)

(* 0x0015fd24: ldr x21,[sp, #0x20] *)
(*    1441060: ldr x21,[sp, #0x20] *)
| 0x15fd24 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fd28: ldp x19,x20,[sp, #0x10] *)
(*    1441064: ldp x19,x20,[sp, #0x10] *)
| 0x15fd28 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015fd2c: ldp x29,x30,[sp], #0x30 *)
(*    1441068: ldp x29,x30,[sp], #0x30 *)
| 0x15fd2c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fd30: ret *)
(*    1441072: ret *)
| 0x15fd30 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsncat_armv8.
Proof. Picinae_typecheck. Qed.
