(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: lsearch
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition lsearch_armv8 : program := fun _ a => match a with

(* 0x00151448: stp x29,x30,[sp, #-0x50]! *)
(*    1381448: stp x29,x30,[sp, #-0x50]! *)
| 0x151448 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffb0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015144c: mov x29,sp *)
(*    1381452: mov x29,sp *)
| 0x15144c => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x00151450: stp x19,x20,[sp, #0x10] *)
(*    1381456: stp x19,x20,[sp, #0x10] *)
| 0x151450 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151454: mov x20,x1 *)
(*    1381460: mov x20,x1 *)
| 0x151454 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x00151458: mov x19,#0x0 *)
(*    1381464: mov x19,#0x0 *)
| 0x151458 => Some (4,
	Move R_X19 (Word 0x0 64)
)

(* 0x0015145c: stp x21,x22,[sp, #0x20] *)
(*    1381468: stp x21,x22,[sp, #0x20] *)
| 0x15145c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151460: mov x22,x0 *)
(*    1381472: mov x22,x0 *)
| 0x151460 => Some (4,
	Move R_X22 (Var R_X0)
)

(* 0x00151464: mov x21,x3 *)
(*    1381476: mov x21,x3 *)
| 0x151464 => Some (4,
	Move R_X21 (Var R_X3)
)

(* 0x00151468: stp x23,x24,[sp, #0x30] *)
(*    1381480: stp x23,x24,[sp, #0x30] *)
| 0x151468 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X23) $;
	Move (V_TEMP 0x39f80) (Var R_X24) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015146c: mov x24,x4 *)
(*    1381484: mov x24,x4 *)
| 0x15146c => Some (4,
	Move R_X24 (Var R_X4)
)

(* 0x00151470: stp x25,x26,[sp, #0x40] *)
(*    1381488: stp x25,x26,[sp, #0x40] *)
| 0x151470 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X25) $;
	Move (V_TEMP 0x39f80) (Var R_X26) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151474: mov x26,x1 *)
(*    1381492: mov x26,x1 *)
| 0x151474 => Some (4,
	Move R_X26 (Var R_X1)
)

(* 0x00151478: mov x25,x2 *)
(*    1381496: mov x25,x2 *)
| 0x151478 => Some (4,
	Move R_X25 (Var R_X2)
)

(* 0x0015147c: ldr x23,[x2] *)
(*    1381500: ldr x23,[x2] *)
| 0x15147c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move R_X23 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151480: b 0x0015148c *)
(*    1381504: b 0x0015148c *)
| 0x151480 => Some (4,
	Jmp (Word 0x15148c 64)
)

(* 0x00151484: add x20,x20,x21 *)
(*    1381508: add x20,x20,x21 *)
| 0x151484 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X21) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x12080))
)

(* 0x00151488: add x19,x19,#0x1 *)
(*    1381512: add x19,x19,#0x1 *)
| 0x151488 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015148c: cmp x19,x23 *)
(*    1381516: cmp x19,x23 *)
| 0x15148c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X23) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X19) (Var R_X23)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X19) (Var R_X23)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X23) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X19) (Var R_X23)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00151490: b.eq 0x001514c0 *)
(*    1381520: b.eq 0x001514c0 *)
| 0x151490 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x1514c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00151494: mov x1,x20 *)
(*    1381524: mov x1,x20 *)
| 0x151494 => Some (4,
	Move R_X1 (Var R_X20)
)

(* 0x00151498: mov x0,x22 *)
(*    1381528: mov x0,x22 *)
| 0x151498 => Some (4,
	Move R_X0 (Var R_X22)
)

(* 0x0015149c: blr x24 *)
(*    1381532: blr x24 *)
| 0x15149c => Some (4,
	Move R_PC (Var R_X24) $;
	Move R_X30 (BinOp OP_PLUS (Word 0x15149c 64) (Word 0x4 64)) $;
	Jmp (Var R_PC)
)

(* 0x001514a0: cbnz w0,0x00151484 *)
(*    1381536: cbnz w0,0x00151484 *)
| 0x1514a0 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x151484 64)
	) (* else *) (
		Nop
	)
)

(* 0x001514a4: mov x0,x20 *)
(*    1381540: mov x0,x20 *)
| 0x1514a4 => Some (4,
	Move R_X0 (Var R_X20)
)

(* 0x001514a8: ldp x19,x20,[sp, #0x10] *)
(*    1381544: ldp x19,x20,[sp, #0x10] *)
| 0x1514a8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x001514ac: ldp x21,x22,[sp, #0x20] *)
(*    1381548: ldp x21,x22,[sp, #0x20] *)
| 0x1514ac => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x001514b0: ldp x23,x24,[sp, #0x30] *)
(*    1381552: ldp x23,x24,[sp, #0x30] *)
| 0x1514b0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x001514b4: ldp x25,x26,[sp, #0x40] *)
(*    1381556: ldp x25,x26,[sp, #0x40] *)
| 0x1514b4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X25 (Var (V_TEMP 0x24180)) $;
	Move R_X26 (Var (V_TEMP 0x24300))
)

(* 0x001514b8: ldp x29,x30,[sp], #0x50 *)
(*    1381560: ldp x29,x30,[sp], #0x50 *)
| 0x1514b8 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x001514bc: ret *)
(*    1381564: ret *)
| 0x1514bc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001514c0: add x0,x19,#0x1 *)
(*    1381568: add x0,x19,#0x1 *)
| 0x1514c0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x001514c4: str x0,[x25] *)
(*    1381572: str x0,[x25] *)
| 0x1514c4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X25) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x001514c8: mov x2,x21 *)
(*    1381576: mov x2,x21 *)
| 0x1514c8 => Some (4,
	Move R_X2 (Var R_X21)
)

(* 0x001514cc: madd x0,x21,x19,x26 *)
(*    1381580: madd x0,x21,x19,x26 *)
| 0x1514cc => Some (4,
	Move (V_TEMP 0x28b00) (BinOp OP_TIMES (Var R_X21) (Var R_X19)) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X26) (Var (V_TEMP 0x28b00)))
)

(* 0x001514d0: ldp x23,x24,[sp, #0x30] *)
(*    1381584: ldp x23,x24,[sp, #0x30] *)
| 0x1514d0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x001514d4: mov x1,x22 *)
(*    1381588: mov x1,x22 *)
| 0x1514d4 => Some (4,
	Move R_X1 (Var R_X22)
)

(* 0x001514d8: ldp x19,x20,[sp, #0x10] *)
(*    1381592: ldp x19,x20,[sp, #0x10] *)
| 0x1514d8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x001514dc: ldp x21,x22,[sp, #0x20] *)
(*    1381596: ldp x21,x22,[sp, #0x20] *)
| 0x1514dc => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x001514e0: ldp x25,x26,[sp, #0x40] *)
(*    1381600: ldp x25,x26,[sp, #0x40] *)
| 0x1514e0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X25 (Var (V_TEMP 0x24180)) $;
	Move R_X26 (Var (V_TEMP 0x24300))
)

(* 0x001514e4: ldp x29,x30,[sp], #0x50 *)
(*    1381604: ldp x29,x30,[sp], #0x50 *)
| 0x1514e4 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x001514e8: b 0x00118270 *)
(*    1381608: b 0x00118270 *)
| 0x1514e8 => Some (4,
	Jmp (Word 0x118270 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx lsearch_armv8.
Proof. Picinae_typecheck. Qed.
