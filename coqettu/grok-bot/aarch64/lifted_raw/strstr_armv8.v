(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strstr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strstr_armv8 : program := fun _ a => match a with

(* 0x0015f684: ldrb w4,[x1] *)
(*    1439364: ldrb w4,[x1] *)
| 0x15f684 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f688: cbnz w4,0x0015f690 *)
(*    1439368: cbnz w4,0x0015f690 *)
| 0x15f688 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X4)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15f690 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f68c: ret *)
(*    1439372: ret *)
| 0x15f68c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015f690: stp x29,x30,[sp, #-0x20]! *)
(*    1439376: stp x29,x30,[sp, #-0x20]! *)
| 0x15f690 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f694: mov x3,x1 *)
(*    1439380: mov x3,x1 *)
| 0x15f694 => Some (4,
	Move R_X3 (Var R_X1)
)

(* 0x0015f698: mov w1,w4 *)
(*    1439384: mov w1,w4 *)
| 0x15f698 => Some (4,
	Move R_X1 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X4)))
)

(* 0x0015f69c: mov x29,sp *)
(*    1439388: mov x29,sp *)
| 0x15f69c => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f6a0: str x3,[sp, #0x18] *)
(*    1439392: str x3,[sp, #0x18] *)
| 0x15f6a0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x18 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X3)) LittleE 8)
)

(* 0x0015f6a4: bl 0x0015ebcc *)
(*    1439396: bl 0x0015ebcc *)
| 0x15f6a4 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f6a4 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ebcc 64)
)

(* 0x0015f6a8: mov x2,x0 *)
(*    1439400: mov x2,x0 *)
| 0x15f6a8 => Some (4,
	Move R_X2 (Var R_X0)
)

(* 0x0015f6ac: cbz x0,0x0015f7b8 *)
(*    1439404: cbz x0,0x0015f7b8 *)
| 0x15f6ac => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15f7b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6b0: ldr x3,[sp, #0x18] *)
(*    1439408: ldr x3,[sp, #0x18] *)
| 0x15f6b0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x18 64)) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f6b4: ldrb w4,[x3, #0x1] *)
(*    1439412: ldrb w4,[x3, #0x1] *)
| 0x15f6b4 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X3) (Word 0x1 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6b8: cbz w4,0x0015f7b8 *)
(*    1439416: cbz w4,0x0015f7b8 *)
| 0x15f6b8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X4)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6bc: ldrb w6,[x0, #0x1] *)
(*    1439420: ldrb w6,[x0, #0x1] *)
| 0x15f6bc => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X0) (Word 0x1 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6c0: cbz w6,0x0015f7b4 *)
(*    1439424: cbz w6,0x0015f7b4 *)
| 0x15f6c0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X6)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6c4: ldrb w5,[x3, #0x2] *)
(*    1439428: ldrb w5,[x3, #0x2] *)
| 0x15f6c4 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X3) (Word 0x2 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X5 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6c8: cbz w5,0x0015f6f8 *)
(*    1439432: cbz w5,0x0015f6f8 *)
| 0x15f6c8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X5)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f6f8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6cc: ldrb w1,[x0, #0x2] *)
(*    1439436: ldrb w1,[x0, #0x2] *)
| 0x15f6cc => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6d0: cbz w1,0x0015f7b4 *)
(*    1439440: cbz w1,0x0015f7b4 *)
| 0x15f6d0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6d4: ldrb w7,[x3, #0x3] *)
(*    1439444: ldrb w7,[x3, #0x3] *)
| 0x15f6d4 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X3) (Word 0x3 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X7 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6d8: cbz w7,0x0015f738 *)
(*    1439448: cbz w7,0x0015f738 *)
| 0x15f6d8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X7)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f738 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6dc: ldrb w1,[x0, #0x3] *)
(*    1439452: ldrb w1,[x0, #0x3] *)
| 0x15f6dc => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X0) (Word 0x3 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6e0: cbz w1,0x0015f7b4 *)
(*    1439456: cbz w1,0x0015f7b4 *)
| 0x15f6e0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6e4: ldrb w1,[x3, #0x4] *)
(*    1439460: ldrb w1,[x3, #0x4] *)
| 0x15f6e4 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X3) (Word 0x4 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f6e8: cbz w1,0x0015f780 *)
(*    1439464: cbz w1,0x0015f780 *)
| 0x15f6e8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f780 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f6ec: ldp x29,x30,[sp], #0x20 *)
(*    1439468: ldp x29,x30,[sp], #0x20 *)
| 0x15f6ec => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f6f0: mov x1,x3 *)
(*    1439472: mov x1,x3 *)
| 0x15f6f0 => Some (4,
	Move R_X1 (Var R_X3)
)

(* 0x0015f6f4: b 0x0015f394 *)
(*    1439476: b 0x0015f394 *)
| 0x15f6f4 => Some (4,
	Jmp (Word 0x15f394 64)
)

(* 0x0015f6f8: ldrh w3,[x3] *)
(*    1439480: ldrh w3,[x3] *)
| 0x15f6f8 => Some (4,
	Move (V_TEMP 0x6300) (Var R_X3) $;
	Move (V_TEMP 0x25200) (Load (Var V_MEM64) (Var (V_TEMP 0x6300)) LittleE 2) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25200)))
)

(* 0x0015f6fc: ldrh w0,[x2], #0x1 *)
(*    1439484: ldrh w0,[x2], #0x1 *)
| 0x15f6fc => Some (4,
	Move (V_TEMP 0x7000) (Var R_X2) $;
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x1 64)) $;
	Move (V_TEMP 0x25300) (Load (Var V_MEM64) (Var (V_TEMP 0x7000)) LittleE 2) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25300)))
)

(* 0x0015f700: rev16 w3,w3 *)
(*    1439488: rev16 w3,w3 *)
| 0x15f700 => Some (4,
	Move (V_TEMP 0x30400) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x30480) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x30500) (BinOp OP_RSHIFT (Var (V_TEMP 0x30480)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30580) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x30600) (BinOp OP_LSHIFT (Var (V_TEMP 0x30580)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30400) (BinOp OP_OR (Var (V_TEMP 0x30500)) (Var (V_TEMP 0x30600))) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x30400)))
)

(* 0x0015f704: rev16 w0,w0 *)
(*    1439492: rev16 w0,w0 *)
| 0x15f704 => Some (4,
	Move (V_TEMP 0x30400) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x30480) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x30500) (BinOp OP_RSHIFT (Var (V_TEMP 0x30480)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30580) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x30600) (BinOp OP_LSHIFT (Var (V_TEMP 0x30580)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30400) (BinOp OP_OR (Var (V_TEMP 0x30500)) (Var (V_TEMP 0x30600))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x30400)))
)

(* 0x0015f708: and w3,w3,#0xffff *)
(*    1439496: and w3,w3,#0xffff *)
| 0x15f708 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X3)) (Word 0xffff 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0015f70c: and w0,w0,#0xffff *)
(*    1439500: and w0,w0,#0xffff *)
| 0x15f70c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0015f710: b 0x0015f720 *)
(*    1439504: b 0x0015f720 *)
| 0x15f710 => Some (4,
	Jmp (Word 0x15f720 64)
)

(* 0x0015f714: ldrb w1,[x2, #0x1]! *)
(*    1439508: ldrb w1,[x2, #0x1]! *)
| 0x15f714 => Some (4,
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x1 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var R_X2) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015f718: orr w0,w1,w0, LSL #0x8 *)
(*    1439512: orr w0,w1,w0, LSL #0x8 *)
| 0x15f718 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f71c: and w0,w0,#0xffff *)
(*    1439516: and w0,w0,#0xffff *)
| 0x15f71c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0015f720: ldrb w1,[x2] *)
(*    1439520: ldrb w1,[x2] *)
| 0x15f720 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X2) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f724: cbz w1,0x0015f7b4 *)
(*    1439524: cbz w1,0x0015f7b4 *)
| 0x15f724 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f728: cmp w0,w3 *)
(*    1439528: cmp w0,w3 *)
| 0x15f728 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f72c: b.ne 0x0015f714 *)
(*    1439532: b.ne 0x0015f714 *)
| 0x15f72c => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15f714 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f730: sub x2,x2,#0x1 *)
(*    1439536: sub x2,x2,#0x1 *)
| 0x15f730 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015f734: b 0x0015f7b8 *)
(*    1439540: b 0x0015f7b8 *)
| 0x15f734 => Some (4,
	Jmp (Word 0x15f7b8 64)
)

(* 0x0015f738: ldrb w3,[x3] *)
(*    1439544: ldrb w3,[x3] *)
| 0x15f738 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f73c: lsl w4,w4,#0x10 *)
(*    1439548: lsl w4,w4,#0x10 *)
| 0x15f73c => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X4)) (Word 0x10 32)) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x0015f740: ldrb w0,[x2], #0x2 *)
(*    1439552: ldrb w0,[x2], #0x2 *)
| 0x15f740 => Some (4,
	Move (V_TEMP 0x7000) (Var R_X2) $;
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x2 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var (V_TEMP 0x7000)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015f744: lsl w6,w6,#0x10 *)
(*    1439556: lsl w6,w6,#0x10 *)
| 0x15f744 => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X6)) (Word 0x10 32)) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x0015f748: orr w3,w4,w3, LSL #0x18 *)
(*    1439560: orr w3,w4,w3, LSL #0x18 *)
| 0x15f748 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X3)) (Word 0x18 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X4)) (Var (V_TEMP 0x3e80))) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f74c: orr w0,w6,w0, LSL #0x18 *)
(*    1439564: orr w0,w6,w0, LSL #0x18 *)
| 0x15f74c => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x18 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X6)) (Var (V_TEMP 0x3e80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f750: orr w5,w3,w5, LSL #0x8 *)
(*    1439568: orr w5,w3,w5, LSL #0x8 *)
| 0x15f750 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X5)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x3e80))) $;
	Move R_X5 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f754: orr w0,w0,w1, LSL #0x8 *)
(*    1439572: orr w0,w0,w1, LSL #0x8 *)
| 0x15f754 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x3e80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f758: b 0x0015f768 *)
(*    1439576: b 0x0015f768 *)
| 0x15f758 => Some (4,
	Jmp (Word 0x15f768 64)
)

(* 0x0015f75c: ldrb w1,[x2, #0x1]! *)
(*    1439580: ldrb w1,[x2, #0x1]! *)
| 0x15f75c => Some (4,
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x1 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var R_X2) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015f760: orr w0,w1,w0 *)
(*    1439584: orr w0,w1,w0 *)
| 0x15f760 => Some (4,
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f764: lsl w0,w0,#0x8 *)
(*    1439588: lsl w0,w0,#0x8 *)
| 0x15f764 => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x0015f768: ldrb w1,[x2] *)
(*    1439592: ldrb w1,[x2] *)
| 0x15f768 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X2) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f76c: cbz w1,0x0015f7b4 *)
(*    1439596: cbz w1,0x0015f7b4 *)
| 0x15f76c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f770: cmp w5,w0 *)
(*    1439600: cmp w5,w0 *)
| 0x15f770 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X5)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X5)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X5)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X5)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X5)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f774: b.ne 0x0015f75c *)
(*    1439604: b.ne 0x0015f75c *)
| 0x15f774 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15f75c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f778: sub x2,x2,#0x2 *)
(*    1439608: sub x2,x2,#0x2 *)
| 0x15f778 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x2 64))
)

(* 0x0015f77c: b 0x0015f7b8 *)
(*    1439612: b 0x0015f7b8 *)
| 0x15f77c => Some (4,
	Jmp (Word 0x15f7b8 64)
)

(* 0x0015f780: ldr w0,[x2], #0x3 *)
(*    1439616: ldr w0,[x2], #0x3 *)
| 0x15f780 => Some (4,
	Move (V_TEMP 0x7000) (Var R_X2) $;
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x3 64)) $;
	Move (V_TEMP 0x24900) (Load (Var V_MEM64) (Var (V_TEMP 0x7000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24900)))
)

(* 0x0015f784: ldr w3,[x3] *)
(*    1439620: ldr w3,[x3] *)
| 0x15f784 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X3) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015f788: rev w0,w0 *)
(*    1439624: rev w0,w0 *)
| 0x15f788 => Some (4,
	Move (V_TEMP 0x2f800) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f880)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f980) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x2fa00) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f980)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2f900)) (Var (V_TEMP 0x2fa00))) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))
)

(* 0x0015f78c: rev w3,w3 *)
(*    1439628: rev w3,w3 *)
| 0x15f78c => Some (4,
	Move (V_TEMP 0x2f800) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f880)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f980) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x2fa00) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f980)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2f900)) (Var (V_TEMP 0x2fa00))) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80))) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))
)

(* 0x0015f790: b 0x0015f79c *)
(*    1439632: b 0x0015f79c *)
| 0x15f790 => Some (4,
	Jmp (Word 0x15f79c 64)
)

(* 0x0015f794: ldrb w1,[x2, #0x1]! *)
(*    1439636: ldrb w1,[x2, #0x1]! *)
| 0x15f794 => Some (4,
	Move R_X2 (BinOp OP_PLUS (Var R_X2) (Word 0x1 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var R_X2) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015f798: orr w0,w1,w0, LSL #0x8 *)
(*    1439640: orr w0,w1,w0, LSL #0x8 *)
| 0x15f798 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0015f79c: ldrb w1,[x2] *)
(*    1439644: ldrb w1,[x2] *)
| 0x15f79c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X2) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f7a0: cbz w1,0x0015f7b4 *)
(*    1439648: cbz w1,0x0015f7b4 *)
| 0x15f7a0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f7a4: cmp w3,w0 *)
(*    1439652: cmp w3,w0 *)
| 0x15f7a4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f7a8: b.ne 0x0015f794 *)
(*    1439656: b.ne 0x0015f794 *)
| 0x15f7a8 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15f794 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f7ac: sub x2,x2,#0x3 *)
(*    1439660: sub x2,x2,#0x3 *)
| 0x15f7ac => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x3 64))
)

(* 0x0015f7b0: b 0x0015f7b8 *)
(*    1439664: b 0x0015f7b8 *)
| 0x15f7b0 => Some (4,
	Jmp (Word 0x15f7b8 64)
)

(* 0x0015f7b4: mov x2,#0x0 *)
(*    1439668: mov x2,#0x0 *)
| 0x15f7b4 => Some (4,
	Move R_X2 (Word 0x0 64)
)

(* 0x0015f7b8: mov x0,x2 *)
(*    1439672: mov x0,x2 *)
| 0x15f7b8 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f7bc: ldp x29,x30,[sp], #0x20 *)
(*    1439676: ldp x29,x30,[sp], #0x20 *)
| 0x15f7bc => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f7c0: ret *)
(*    1439680: ret *)
| 0x15f7c0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strstr_armv8.
Proof. Picinae_typecheck. Qed.
