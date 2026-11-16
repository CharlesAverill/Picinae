(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcscspn
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcscspn_armv8 : program := fun _ a => match a with

(* 0x0015fb44: ldr w2,[x1] *)
(*    1440580: ldr w2,[x1] *)
| 0x15fb44 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fb48: cbz w2,0x0015fbb4 *)
(*    1440584: cbz w2,0x0015fbb4 *)
| 0x15fb48 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15fbb4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fb4c: stp x29,x30,[sp, #-0x30]! *)
(*    1440588: stp x29,x30,[sp, #-0x30]! *)
| 0x15fb4c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fb50: mov x29,sp *)
(*    1440592: mov x29,sp *)
| 0x15fb50 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fb54: stp x19,x20,[sp, #0x10] *)
(*    1440596: stp x19,x20,[sp, #0x10] *)
| 0x15fb54 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fb58: mov x20,x1 *)
(*    1440600: mov x20,x1 *)
| 0x15fb58 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fb5c: mov x19,x0 *)
(*    1440604: mov x19,x0 *)
| 0x15fb5c => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fb60: str x21,[sp, #0x20] *)
(*    1440608: str x21,[sp, #0x20] *)
| 0x15fb60 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0015fb64: mov x21,x0 *)
(*    1440612: mov x21,x0 *)
| 0x15fb64 => Some (4,
	Move R_X21 (Var R_X0)
)

(* 0x0015fb68: ldr w1,[x1, #0x4] *)
(*    1440616: ldr w1,[x1, #0x4] *)
| 0x15fb68 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X1) (Word 0x4 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fb6c: cbz w1,0x0015fb8c *)
(*    1440620: cbz w1,0x0015fb8c *)
| 0x15fb6c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15fb8c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fb70: ldr w1,[x19] *)
(*    1440624: ldr w1,[x19] *)
| 0x15fb70 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X19) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fb74: mov x0,x20 *)
(*    1440628: mov x0,x20 *)
| 0x15fb74 => Some (4,
	Move R_X0 (Var R_X20)
)

(* 0x0015fb78: cbz w1,0x0015fbb8 *)
(*    1440632: cbz w1,0x0015fbb8 *)
| 0x15fb78 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15fbb8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fb7c: bl 0x0015fab4 *)
(*    1440636: bl 0x0015fab4 *)
| 0x15fb7c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fb7c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fab4 64)
)

(* 0x0015fb80: cbnz x0,0x0015fbb8 *)
(*    1440640: cbnz x0,0x0015fbb8 *)
| 0x15fb80 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15fbb8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fb84: add x19,x19,#0x4 *)
(*    1440644: add x19,x19,#0x4 *)
| 0x15fb84 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015fb88: b 0x0015fb70 *)
(*    1440648: b 0x0015fb70 *)
| 0x15fb88 => Some (4,
	Jmp (Word 0x15fb70 64)
)

(* 0x0015fb8c: mov w1,w2 *)
(*    1440652: mov w1,w2 *)
| 0x15fb8c => Some (4,
	Move R_X1 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015fb90: bl 0x0015fab4 *)
(*    1440656: bl 0x0015fab4 *)
| 0x15fb90 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fb90 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fab4 64)
)

(* 0x0015fb94: cbz x0,0x0015fba4 *)
(*    1440660: cbz x0,0x0015fba4 *)
| 0x15fb94 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15fba4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fb98: sub x0,x0,x21 *)
(*    1440664: sub x0,x0,x21 *)
| 0x15fb98 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X0) (Var R_X21))
)

(* 0x0015fb9c: asr x0,x0,#0x2 *)
(*    1440668: asr x0,x0,#0x2 *)
| 0x15fb9c => Some (4,
	Move R_X0 (BinOp OP_ARSHIFT (Var R_X0) (Word 0x2 64))
)

(* 0x0015fba0: b 0x0015fbc0 *)
(*    1440672: b 0x0015fbc0 *)
| 0x15fba0 => Some (4,
	Jmp (Word 0x15fbc0 64)
)

(* 0x0015fba4: ldp x19,x20,[sp, #0x10] *)
(*    1440676: ldp x19,x20,[sp, #0x10] *)
| 0x15fba4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015fba8: mov x0,x21 *)
(*    1440680: mov x0,x21 *)
| 0x15fba8 => Some (4,
	Move R_X0 (Var R_X21)
)

(* 0x0015fbac: ldr x21,[sp, #0x20] *)
(*    1440684: ldr x21,[sp, #0x20] *)
| 0x15fbac => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fbb0: ldp x29,x30,[sp], #0x30 *)
(*    1440688: ldp x29,x30,[sp], #0x30 *)
| 0x15fbb0 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fbb4: b 0x0015fc18 *)
(*    1440692: b 0x0015fc18 *)
| 0x15fbb4 => Some (4,
	Jmp (Word 0x15fc18 64)
)

(* 0x0015fbb8: sub x0,x19,x21 *)
(*    1440696: sub x0,x19,x21 *)
| 0x15fbb8 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X19) (Var R_X21))
)

(* 0x0015fbbc: asr x0,x0,#0x2 *)
(*    1440700: asr x0,x0,#0x2 *)
| 0x15fbbc => Some (4,
	Move R_X0 (BinOp OP_ARSHIFT (Var R_X0) (Word 0x2 64))
)

(* 0x0015fbc0: ldr x21,[sp, #0x20] *)
(*    1440704: ldr x21,[sp, #0x20] *)
| 0x15fbc0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fbc4: ldp x19,x20,[sp, #0x10] *)
(*    1440708: ldp x19,x20,[sp, #0x10] *)
| 0x15fbc4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015fbc8: ldp x29,x30,[sp], #0x30 *)
(*    1440712: ldp x29,x30,[sp], #0x30 *)
| 0x15fbc8 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fbcc: ret *)
(*    1440716: ret *)
| 0x15fbcc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcscspn_armv8.
Proof. Picinae_typecheck. Qed.
