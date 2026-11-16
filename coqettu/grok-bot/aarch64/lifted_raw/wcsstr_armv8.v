(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsstr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsstr_armv8 : program := fun _ a => match a with

(* 0x0015febc: stp x29,x30,[sp, #-0x60]! *)
(*    1441468: stp x29,x30,[sp, #-0x60]! *)
| 0x15febc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffa0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fec0: mov x29,sp *)
(*    1441472: mov x29,sp *)
| 0x15fec0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fec4: stp x19,x20,[sp, #0x10] *)
(*    1441476: stp x19,x20,[sp, #0x10] *)
| 0x15fec4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fec8: mov x19,x0 *)
(*    1441480: mov x19,x0 *)
| 0x15fec8 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fecc: ldr w2,[x1] *)
(*    1441484: ldr w2,[x1] *)
| 0x15fecc => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fed0: cbz w2,0x0016012c *)
(*    1441488: cbz w2,0x0016012c *)
| 0x15fed0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x16012c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fed4: ldr w3,[x0] *)
(*    1441492: ldr w3,[x0] *)
| 0x15fed4 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fed8: cbz w3,0x0015ff20 *)
(*    1441496: cbz w3,0x0015ff20 *)
| 0x15fed8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ff20 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fedc: mov x20,x1 *)
(*    1441500: mov x20,x1 *)
| 0x15fedc => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fee0: mov w1,w2 *)
(*    1441504: mov w1,w2 *)
| 0x15fee0 => Some (4,
	Move R_X1 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015fee4: bl 0x0015fab4 *)
(*    1441508: bl 0x0015fab4 *)
| 0x15fee4 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fee4 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fab4 64)
)

(* 0x0015fee8: mov x19,x0 *)
(*    1441512: mov x19,x0 *)
| 0x15fee8 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015feec: cbz x0,0x0015ff20 *)
(*    1441516: cbz x0,0x0015ff20 *)
| 0x15feec => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15ff20 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fef0: ldr w0,[x20, #0x4] *)
(*    1441520: ldr w0,[x20, #0x4] *)
| 0x15fef0 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X20) (Word 0x4 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fef4: cbz w0,0x0016012c *)
(*    1441524: cbz w0,0x0016012c *)
| 0x15fef4 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x16012c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fef8: ldr w0,[x19, #0x4] *)
(*    1441528: ldr w0,[x19, #0x4] *)
| 0x15fef8 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X19) (Word 0x4 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fefc: cbz w0,0x0015ff20 *)
(*    1441532: cbz w0,0x0015ff20 *)
| 0x15fefc => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ff20 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff00: stp x25,x26,[sp, #0x40] *)
(*    1441536: stp x25,x26,[sp, #0x40] *)
| 0x15ff00 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X25) $;
	Move (V_TEMP 0x39f80) (Var R_X26) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ff04: mov x25,#0x0 *)
(*    1441540: mov x25,#0x0 *)
| 0x15ff04 => Some (4,
	Move R_X25 (Word 0x0 64)
)

(* 0x0015ff08: ldr w0,[x20, x25, LSL #0x2] *)
(*    1441544: ldr w0,[x20, x25, LSL #0x2] *)
| 0x15ff08 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X25) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x0015ff0c: cbz w0,0x0015ff94 *)
(*    1441548: cbz w0,0x0015ff94 *)
| 0x15ff0c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ff94 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff10: ldr w0,[x19, x25, LSL #0x2] *)
(*    1441552: ldr w0,[x19, x25, LSL #0x2] *)
| 0x15ff10 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X25) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x0015ff14: add x25,x25,#0x1 *)
(*    1441556: add x25,x25,#0x1 *)
| 0x15ff14 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X25) (Var (V_TEMP 0x11a80))) (Var R_X25))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X25) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X25) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X25 (Var (V_TEMP 0x11b80))
)

(* 0x0015ff18: cbnz w0,0x0015ff08 *)
(*    1441560: cbnz w0,0x0015ff08 *)
| 0x15ff18 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15ff08 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff1c: ldp x25,x26,[sp, #0x40] *)
(*    1441564: ldp x25,x26,[sp, #0x40] *)
| 0x15ff1c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X25 (Var (V_TEMP 0x24180)) $;
	Move R_X26 (Var (V_TEMP 0x24300))
)

(* 0x0015ff20: mov x19,#0x0 *)
(*    1441568: mov x19,#0x0 *)
| 0x15ff20 => Some (4,
	Move R_X19 (Word 0x0 64)
)

(* 0x0015ff24: b 0x0016012c *)
(*    1441572: b 0x0016012c *)
| 0x15ff24 => Some (4,
	Jmp (Word 0x16012c 64)
)

(* 0x0015ff28: ldp x21,x22,[sp, #0x20] *)
(*    1441576: ldp x21,x22,[sp, #0x20] *)
| 0x15ff28 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x0015ff2c: ldp x23,x24,[sp, #0x30] *)
(*    1441580: ldp x23,x24,[sp, #0x30] *)
| 0x15ff2c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x0015ff30: ldp x25,x26,[sp, #0x40] *)
(*    1441584: ldp x25,x26,[sp, #0x40] *)
| 0x15ff30 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X25 (Var (V_TEMP 0x24180)) $;
	Move R_X26 (Var (V_TEMP 0x24300))
)

(* 0x0015ff34: ldp x27,x28,[sp, #0x50] *)
(*    1441588: ldp x27,x28,[sp, #0x50] *)
| 0x15ff34 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X27 (Var (V_TEMP 0x24180)) $;
	Move R_X28 (Var (V_TEMP 0x24300))
)

(* 0x0015ff38: b 0x0015ff20 *)
(*    1441592: b 0x0015ff20 *)
| 0x15ff38 => Some (4,
	Jmp (Word 0x15ff20 64)
)

(* 0x0015ff3c: cmp x1,x21 *)
(*    1441596: cmp x1,x21 *)
| 0x15ff3c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X21) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X21)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X21)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X21) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X21)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ff40: b.eq 0x0015ff4c *)
(*    1441600: b.eq 0x0015ff4c *)
| 0x15ff40 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ff4c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff44: add x1,x1,#0x1 *)
(*    1441604: add x1,x1,#0x1 *)
| 0x15ff44 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015ff48: b 0x0015ff54 *)
(*    1441608: b 0x0015ff54 *)
| 0x15ff48 => Some (4,
	Jmp (Word 0x15ff54 64)
)

(* 0x0015ff4c: mov x2,x0 *)
(*    1441612: mov x2,x0 *)
| 0x15ff4c => Some (4,
	Move R_X2 (Var R_X0)
)

(* 0x0015ff50: mov x1,#0x1 *)
(*    1441616: mov x1,#0x1 *)
| 0x15ff50 => Some (4,
	Move R_X1 (Word 0x1 64)
)

(* 0x0015ff54: add x0,x1,x2 *)
(*    1441620: add x0,x1,x2 *)
| 0x15ff54 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015ff58: add x3,x28,x1 *)
(*    1441624: add x3,x28,x1 *)
| 0x15ff58 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X1) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11f80))) (Var R_X28))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X28) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X28) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x12080))
)

(* 0x0015ff5c: cmp x25,x0 *)
(*    1441628: cmp x25,x0 *)
| 0x15ff5c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X0) (Var R_X25))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var R_X0)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var R_X0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X25) (Var R_X0)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ff60: b.ls 0x0015ffb4 *)
(*    1441632: b.ls 0x0015ffb4 *)
| 0x15ff60 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15ffb4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff64: ldr w4,[x20, x3, LSL #0x2] *)
(*    1441636: ldr w4,[x20, x3, LSL #0x2] *)
| 0x15ff64 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x0015ff68: ldr w3,[x20, x0, LSL #0x2] *)
(*    1441640: ldr w3,[x20, x0, LSL #0x2] *)
| 0x15ff68 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x0015ff6c: cmp w4,w3 *)
(*    1441644: cmp w4,w3 *)
| 0x15ff6c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ff70: b.eq 0x0015ff3c *)
(*    1441648: b.eq 0x0015ff3c *)
| 0x15ff70 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ff3c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff74: b.ls 0x0015ff80 *)
(*    1441652: b.ls 0x0015ff80 *)
| 0x15ff74 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15ff80 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ff78: sub x21,x0,x28 *)
(*    1441656: sub x21,x0,x28 *)
| 0x15ff78 => Some (4,
	Move R_X21 (BinOp OP_MINUS (Var R_X0) (Var R_X28))
)

(* 0x0015ff7c: b 0x0015ff4c *)
(*    1441660: b 0x0015ff4c *)
| 0x15ff7c => Some (4,
	Jmp (Word 0x15ff4c 64)
)

(* 0x0015ff80: mov x21,#0x1 *)
(*    1441664: mov x21,#0x1 *)
| 0x15ff80 => Some (4,
	Move R_X21 (Word 0x1 64)
)

(* 0x0015ff84: mov x28,x2 *)
(*    1441668: mov x28,x2 *)
| 0x15ff84 => Some (4,
	Move R_X28 (Var R_X2)
)

(* 0x0015ff88: mov x1,x21 *)
(*    1441672: mov x1,x21 *)
| 0x15ff88 => Some (4,
	Move R_X1 (Var R_X21)
)

(* 0x0015ff8c: add x2,x2,x21 *)
(*    1441676: add x2,x2,x21 *)
| 0x15ff8c => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X21) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x0015ff90: b 0x0015ff54 *)
(*    1441680: b 0x0015ff54 *)
| 0x15ff90 => Some (4,
	Jmp (Word 0x15ff54 64)
)

(* 0x0015ff94: mov x2,#0x0 *)
(*    1441684: mov x2,#0x0 *)
| 0x15ff94 => Some (4,
	Move R_X2 (Word 0x0 64)
)

(* 0x0015ff98: stp x21,x22,[sp, #0x20] *)
(*    1441688: stp x21,x22,[sp, #0x20] *)
| 0x15ff98 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ff9c: mov x21,#0x1 *)
(*    1441692: mov x21,#0x1 *)
| 0x15ff9c => Some (4,
	Move R_X21 (Word 0x1 64)
)

(* 0x0015ffa0: mov x1,x21 *)
(*    1441696: mov x1,x21 *)
| 0x15ffa0 => Some (4,
	Move R_X1 (Var R_X21)
)

(* 0x0015ffa4: stp x23,x24,[sp, #0x30] *)
(*    1441700: stp x23,x24,[sp, #0x30] *)
| 0x15ffa4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X23) $;
	Move (V_TEMP 0x39f80) (Var R_X24) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ffa8: stp x27,x28,[sp, #0x50] *)
(*    1441704: stp x27,x28,[sp, #0x50] *)
| 0x15ffa8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X27) $;
	Move (V_TEMP 0x39f80) (Var R_X28) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ffac: mov x28,#-0x1 *)
(*    1441708: mov x28,#-0x1 *)
| 0x15ffac => Some (4,
	Move R_X28 (Word 0xffffffffffffffff 64)
)

(* 0x0015ffb0: b 0x0015ff54 *)
(*    1441712: b 0x0015ff54 *)
| 0x15ffb0 => Some (4,
	Jmp (Word 0x15ff54 64)
)

(* 0x0015ffb4: mov x3,#0x1 *)
(*    1441716: mov x3,#0x1 *)
| 0x15ffb4 => Some (4,
	Move R_X3 (Word 0x1 64)
)

(* 0x0015ffb8: mov x2,#0x0 *)
(*    1441720: mov x2,#0x0 *)
| 0x15ffb8 => Some (4,
	Move R_X2 (Word 0x0 64)
)

(* 0x0015ffbc: mov x0,x3 *)
(*    1441724: mov x0,x3 *)
| 0x15ffbc => Some (4,
	Move R_X0 (Var R_X3)
)

(* 0x0015ffc0: mov x5,#-0x1 *)
(*    1441728: mov x5,#-0x1 *)
| 0x15ffc0 => Some (4,
	Move R_X5 (Word 0xffffffffffffffff 64)
)

(* 0x0015ffc4: b 0x0015ffec *)
(*    1441732: b 0x0015ffec *)
| 0x15ffc4 => Some (4,
	Jmp (Word 0x15ffec 64)
)

(* 0x0015ffc8: cmp x0,x3 *)
(*    1441736: cmp x0,x3 *)
| 0x15ffc8 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X3)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X3)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ffcc: b.eq 0x0015ffd8 *)
(*    1441740: b.eq 0x0015ffd8 *)
| 0x15ffcc => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ffd8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ffd0: add x0,x0,#0x1 *)
(*    1441744: add x0,x0,#0x1 *)
| 0x15ffd0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015ffd4: b 0x0015ffec *)
(*    1441748: b 0x0015ffec *)
| 0x15ffd4 => Some (4,
	Jmp (Word 0x15ffec 64)
)

(* 0x0015ffd8: mov x2,x1 *)
(*    1441752: mov x2,x1 *)
| 0x15ffd8 => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0015ffdc: mov x0,#0x1 *)
(*    1441756: mov x0,#0x1 *)
| 0x15ffdc => Some (4,
	Move R_X0 (Word 0x1 64)
)

(* 0x0015ffe0: b 0x0015ffec *)
(*    1441760: b 0x0015ffec *)
| 0x15ffe0 => Some (4,
	Jmp (Word 0x15ffec 64)
)

(* 0x0015ffe4: mov x5,x2 *)
(*    1441764: mov x5,x2 *)
| 0x15ffe4 => Some (4,
	Move R_X5 (Var R_X2)
)

(* 0x0015ffe8: add x2,x2,#0x1 *)
(*    1441768: add x2,x2,#0x1 *)
| 0x15ffe8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ffec: add x1,x0,x2 *)
(*    1441772: add x1,x0,x2 *)
| 0x15ffec => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x0015fff0: add x4,x5,x0 *)
(*    1441776: add x4,x5,x0 *)
| 0x15fff0 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 0x12080))
)

(* 0x0015fff4: cmp x25,x1 *)
(*    1441780: cmp x25,x1 *)
| 0x15fff4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X1) (Var R_X25))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var R_X1)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var R_X1)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X25) (Var R_X1)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015fff8: b.ls 0x00160024 *)
(*    1441784: b.ls 0x00160024 *)
| 0x15fff8 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x160024 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fffc: ldr w6,[x20, x4, LSL #0x2] *)
(*    1441788: ldr w6,[x20, x4, LSL #0x2] *)
| 0x15fffc => Some (4,
	Move (V_TEMP 0x5700) (Var R_X4) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160000: ldr w4,[x20, x1, LSL #0x2] *)
(*    1441792: ldr w4,[x20, x1, LSL #0x2] *)
| 0x160000 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X1) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160004: cmp w6,w4 *)
(*    1441796: cmp w6,w4 *)
| 0x160004 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X6)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X6)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X6)) (Extract 31 0 (Var R_X4))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X6)) (Extract 31 0 (Var R_X4))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X6)) (Extract 31 0 (Var R_X4))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160008: b.eq 0x0015ffc8 *)
(*    1441800: b.eq 0x0015ffc8 *)
| 0x160008 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ffc8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016000c: mov x3,#0x1 *)
(*    1441804: mov x3,#0x1 *)
| 0x16000c => Some (4,
	Move R_X3 (Word 0x1 64)
)

(* 0x00160010: mov x0,x3 *)
(*    1441808: mov x0,x3 *)
| 0x160010 => Some (4,
	Move R_X0 (Var R_X3)
)

(* 0x00160014: b.cs 0x0015ffe4 *)
(*    1441812: b.cs 0x0015ffe4 *)
| 0x160014 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x15ffe4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160018: mov x2,x1 *)
(*    1441816: mov x2,x1 *)
| 0x160018 => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0016001c: sub x3,x1,x5 *)
(*    1441820: sub x3,x1,x5 *)
| 0x16001c => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X1) (Var R_X5))
)

(* 0x00160020: b 0x0015ffec *)
(*    1441824: b 0x0015ffec *)
| 0x160020 => Some (4,
	Jmp (Word 0x15ffec 64)
)

(* 0x00160024: add x1,x5,#0x1 *)
(*    1441828: add x1,x5,#0x1 *)
| 0x160024 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x00160028: add x26,x28,#0x1 *)
(*    1441832: add x26,x28,#0x1 *)
| 0x160028 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11a80))) (Var R_X28))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X28) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X28) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X28) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X26 (Var (V_TEMP 0x11b80))
)

(* 0x0016002c: cmp x1,x26 *)
(*    1441836: cmp x1,x26 *)
| 0x16002c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X26) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X26)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X26)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X26) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X26)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160030: mov x0,x20 *)
(*    1441840: mov x0,x20 *)
| 0x160030 => Some (4,
	Move R_X0 (Var R_X20)
)

(* 0x00160034: csel x21,x21,x3,ls *)
(*    1441844: csel x21,x21,x3,ls *)
| 0x160034 => Some (4,
	Move (V_TEMP 0x1b80) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1c80) (BinOp OP_OR (Var (V_TEMP 0x1b80)) (Var R_ZR)) $;
	Move (V_TEMP 0x1da80) (Var R_X21) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1c80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X3)
	) $;
	Move R_X21 (Var (V_TEMP 0x1da80))
)

(* 0x00160038: csel x26,x26,x1,ls *)
(*    1441848: csel x26,x26,x1,ls *)
| 0x160038 => Some (4,
	Move (V_TEMP 0x1b80) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1c80) (BinOp OP_OR (Var (V_TEMP 0x1b80)) (Var R_ZR)) $;
	Move (V_TEMP 0x1da80) (Var R_X26) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1c80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X1)
	) $;
	Move R_X26 (Var (V_TEMP 0x1da80))
)

(* 0x0016003c: csel x28,x28,x5,ls *)
(*    1441852: csel x28,x28,x5,ls *)
| 0x16003c => Some (4,
	Move (V_TEMP 0x1b80) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1c80) (BinOp OP_OR (Var (V_TEMP 0x1b80)) (Var R_ZR)) $;
	Move (V_TEMP 0x1da80) (Var R_X28) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1c80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X5)
	) $;
	Move R_X28 (Var (V_TEMP 0x1da80))
)

(* 0x00160040: mov x2,x26 *)
(*    1441856: mov x2,x26 *)
| 0x160040 => Some (4,
	Move R_X2 (Var R_X26)
)

(* 0x00160044: add x1,x20,x21, LSL #0x2 *)
(*    1441860: add x1,x20,x21, LSL #0x2 *)
| 0x160044 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X21) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x00160048: lsl x22,x21,#0x2 *)
(*    1441864: lsl x22,x21,#0x2 *)
| 0x160048 => Some (4,
	Move R_X22 (BinOp OP_LSHIFT (Var R_X21) (Word 0x2 64))
)

(* 0x0016004c: bl 0x001601f8 *)
(*    1441868: bl 0x001601f8 *)
| 0x16004c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x16004c 64) (Word 0x4 64)) $;
	Jmp (Word 0x1601f8 64)
)

(* 0x00160050: sub x21,x25,x21 *)
(*    1441872: sub x21,x25,x21 *)
| 0x160050 => Some (4,
	Move R_X21 (BinOp OP_MINUS (Var R_X25) (Var R_X21))
)

(* 0x00160054: cbz w0,0x00160074 *)
(*    1441876: cbz w0,0x00160074 *)
| 0x160054 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x160074 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160058: sub x0,x25,#0x1 *)
(*    1441880: sub x0,x25,#0x1 *)
| 0x160058 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X25) (Word 0x1 64))
)

(* 0x0016005c: mov x21,#0x0 *)
(*    1441884: mov x21,#0x0 *)
| 0x16005c => Some (4,
	Move R_X21 (Word 0x0 64)
)

(* 0x00160060: sub x0,x0,x28 *)
(*    1441888: sub x0,x0,x28 *)
| 0x160060 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X0) (Var R_X28))
)

(* 0x00160064: cmp x0,x28 *)
(*    1441892: cmp x0,x28 *)
| 0x160064 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X28) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X28)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X28)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X28) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X28)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160068: csel x22,x0,x28,cs *)
(*    1441896: csel x22,x0,x28,cs *)
| 0x160068 => Some (4,
	Move (V_TEMP 0x1da80) (Var R_X0) $;
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X28)
	) $;
	Move R_X22 (Var (V_TEMP 0x1da80))
)

(* 0x0016006c: add x22,x22,#0x1 *)
(*    1441900: add x22,x22,#0x1 *)
| 0x16006c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11a80))) (Var R_X22))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X22) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X22) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X22 (Var (V_TEMP 0x11b80))
)

(* 0x00160070: lsl x22,x22,#0x2 *)
(*    1441904: lsl x22,x22,#0x2 *)
| 0x160070 => Some (4,
	Move R_X22 (BinOp OP_LSHIFT (Var R_X22) (Word 0x2 64))
)

(* 0x00160074: orr x23,x25,#0x3f *)
(*    1441908: orr x23,x25,#0x3f *)
| 0x160074 => Some (4,
	Move R_X23 (BinOp OP_OR (Var R_X25) (Word 0x3f 64))
)

(* 0x00160078: mov x27,x19 *)
(*    1441912: mov x27,x19 *)
| 0x160078 => Some (4,
	Move R_X27 (Var R_X19)
)

(* 0x0016007c: mov x24,#0x0 *)
(*    1441916: mov x24,#0x0 *)
| 0x16007c => Some (4,
	Move R_X24 (Word 0x0 64)
)

(* 0x00160080: b 0x001600d8 *)
(*    1441920: b 0x001600d8 *)
| 0x160080 => Some (4,
	Jmp (Word 0x1600d8 64)
)

(* 0x00160084: mov x2,x23 *)
(*    1441924: mov x2,x23 *)
| 0x160084 => Some (4,
	Move R_X2 (Var R_X23)
)

(* 0x00160088: mov x0,x27 *)
(*    1441928: mov x0,x27 *)
| 0x160088 => Some (4,
	Move R_X0 (Var R_X27)
)

(* 0x0016008c: mov w1,#0x0 *)
(*    1441932: mov w1,#0x0 *)
| 0x16008c => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x00160090: bl 0x001601d0 *)
(*    1441936: bl 0x001601d0 *)
| 0x160090 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x160090 64) (Word 0x4 64)) $;
	Jmp (Word 0x1601d0 64)
)

(* 0x00160094: cbz x0,0x001600ac *)
(*    1441940: cbz x0,0x001600ac *)
| 0x160094 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x1600ac 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160098: sub x1,x0,x19 *)
(*    1441944: sub x1,x0,x19 *)
| 0x160098 => Some (4,
	Move R_X1 (BinOp OP_MINUS (Var R_X0) (Var R_X19))
)

(* 0x0016009c: cmp x25,x1, ASR #0x2 *)
(*    1441948: cmp x25,x1, ASR #0x2 *)
| 0x16009c => Some (4,
	Move (V_TEMP 0x4600) (BinOp OP_ARSHIFT (Var R_X1) (Word 0x2 64)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x4600)) (Var R_X25))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x4600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001600a0: b.hi 0x0015ff28 *)
(*    1441952: b.hi 0x0015ff28 *)
| 0x1600a0 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x15ff28 64)
	) (* else *) (
		Nop
	)
)

(* 0x001600a4: mov x27,x0 *)
(*    1441956: mov x27,x0 *)
| 0x1600a4 => Some (4,
	Move R_X27 (Var R_X0)
)

(* 0x001600a8: b 0x001600e4 *)
(*    1441960: b 0x001600e4 *)
| 0x1600a8 => Some (4,
	Jmp (Word 0x1600e4 64)
)

(* 0x001600ac: add x27,x27,x23, LSL #0x2 *)
(*    1441964: add x27,x27,x23, LSL #0x2 *)
| 0x1600ac => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X23) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X27) (Var (V_TEMP 0x11f80))) (Var R_X27))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X27) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X27) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X27) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X27) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X27 (Var (V_TEMP 0x12080))
)

(* 0x001600b0: b 0x001600e4 *)
(*    1441968: b 0x001600e4 *)
| 0x1600b0 => Some (4,
	Jmp (Word 0x1600e4 64)
)

(* 0x001600b4: add x2,x2,#0x1 *)
(*    1441972: add x2,x2,#0x1 *)
| 0x1600b4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x001600b8: ldr w3,[x20, x2, LSL #0x2] *)
(*    1441976: ldr w3,[x20, x2, LSL #0x2] *)
| 0x1600b8 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x001600bc: cbz w3,0x001600f0 *)
(*    1441980: cbz w3,0x001600f0 *)
| 0x1600bc => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x1600f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001600c0: ldr w4,[x19, x2, LSL #0x2] *)
(*    1441984: ldr w4,[x19, x2, LSL #0x2] *)
| 0x1600c0 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x001600c4: cmp w3,w4 *)
(*    1441988: cmp w3,w4 *)
| 0x1600c4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X4))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X4))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X4))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001600c8: b.eq 0x001600b4 *)
(*    1441992: b.eq 0x001600b4 *)
| 0x1600c8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x1600b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x001600cc: sub x2,x2,x28 *)
(*    1441996: sub x2,x2,x28 *)
| 0x1600cc => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Var R_X28))
)

(* 0x001600d0: mov x24,#0x0 *)
(*    1442000: mov x24,#0x0 *)
| 0x1600d0 => Some (4,
	Move R_X24 (Word 0x0 64)
)

(* 0x001600d4: add x19,x19,x2, LSL #0x2 *)
(*    1442004: add x19,x19,x2, LSL #0x2 *)
| 0x1600d4 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X2) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x12080))
)

(* 0x001600d8: sub x0,x27,x19 *)
(*    1442008: sub x0,x27,x19 *)
| 0x1600d8 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X27) (Var R_X19))
)

(* 0x001600dc: cmp x25,x0, ASR #0x2 *)
(*    1442012: cmp x25,x0, ASR #0x2 *)
| 0x1600dc => Some (4,
	Move (V_TEMP 0x4600) (BinOp OP_ARSHIFT (Var R_X0) (Word 0x2 64)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x4600)) (Var R_X25))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X25) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x4600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X25) (Var (V_TEMP 0x4600))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001600e0: b.hi 0x00160084 *)
(*    1442016: b.hi 0x00160084 *)
| 0x1600e0 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x160084 64)
	) (* else *) (
		Nop
	)
)

(* 0x001600e4: cmp x24,x26 *)
(*    1442020: cmp x24,x26 *)
| 0x1600e4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X26) (Var R_X24))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X24) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X24) (Var R_X26)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X24) (Var R_X26)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X26) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X24) (Var R_X26)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001600e8: csel x2,x24,x26,cs *)
(*    1442024: csel x2,x24,x26,cs *)
| 0x1600e8 => Some (4,
	Move (V_TEMP 0x1da80) (Var R_X24) $;
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X26)
	) $;
	Move R_X2 (Var (V_TEMP 0x1da80))
)

(* 0x001600ec: b 0x001600b8 *)
(*    1442028: b 0x001600b8 *)
| 0x1600ec => Some (4,
	Jmp (Word 0x1600b8 64)
)

(* 0x001600f0: mov x2,x26 *)
(*    1442032: mov x2,x26 *)
| 0x1600f0 => Some (4,
	Move R_X2 (Var R_X26)
)

(* 0x001600f4: cmp x24,x2 *)
(*    1442036: cmp x24,x2 *)
| 0x1600f4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X24))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X24) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X24) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X24) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X24) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001600f8: b.cs 0x0016011c *)
(*    1442040: b.cs 0x0016011c *)
| 0x1600f8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x16011c 64)
	) (* else *) (
		Nop
	)
)

(* 0x001600fc: sub x2,x2,#0x1 *)
(*    1442044: sub x2,x2,#0x1 *)
| 0x1600fc => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x00160100: ldr w1,[x20, x2, LSL #0x2] *)
(*    1442048: ldr w1,[x20, x2, LSL #0x2] *)
| 0x160100 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160104: ldr w0,[x19, x2, LSL #0x2] *)
(*    1442052: ldr w0,[x19, x2, LSL #0x2] *)
| 0x160104 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160108: cmp w1,w0 *)
(*    1442056: cmp w1,w0 *)
| 0x160108 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0016010c: b.eq 0x001600f4 *)
(*    1442060: b.eq 0x001600f4 *)
| 0x16010c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x1600f4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160110: add x19,x19,x22 *)
(*    1442064: add x19,x19,x22 *)
| 0x160110 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X22) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x12080))
)

(* 0x00160114: mov x24,x21 *)
(*    1442068: mov x24,x21 *)
| 0x160114 => Some (4,
	Move R_X24 (Var R_X21)
)

(* 0x00160118: b 0x001600d8 *)
(*    1442072: b 0x001600d8 *)
| 0x160118 => Some (4,
	Jmp (Word 0x1600d8 64)
)

(* 0x0016011c: ldp x21,x22,[sp, #0x20] *)
(*    1442076: ldp x21,x22,[sp, #0x20] *)
| 0x16011c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x00160120: ldp x23,x24,[sp, #0x30] *)
(*    1442080: ldp x23,x24,[sp, #0x30] *)
| 0x160120 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x00160124: ldp x25,x26,[sp, #0x40] *)
(*    1442084: ldp x25,x26,[sp, #0x40] *)
| 0x160124 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X25 (Var (V_TEMP 0x24180)) $;
	Move R_X26 (Var (V_TEMP 0x24300))
)

(* 0x00160128: ldp x27,x28,[sp, #0x50] *)
(*    1442088: ldp x27,x28,[sp, #0x50] *)
| 0x160128 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X27 (Var (V_TEMP 0x24180)) $;
	Move R_X28 (Var (V_TEMP 0x24300))
)

(* 0x0016012c: mov x0,x19 *)
(*    1442092: mov x0,x19 *)
| 0x16012c => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x00160130: ldp x19,x20,[sp, #0x10] *)
(*    1442096: ldp x19,x20,[sp, #0x10] *)
| 0x160130 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x00160134: ldp x29,x30,[sp], #0x60 *)
(*    1442100: ldp x29,x30,[sp], #0x60 *)
| 0x160134 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x60 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x00160138: ret *)
(*    1442104: ret *)
| 0x160138 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsstr_armv8.
Proof. Picinae_typecheck. Qed.
