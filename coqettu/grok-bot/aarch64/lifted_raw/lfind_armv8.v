(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: lfind
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition lfind_armv8 : program := fun _ a => match a with

(* 0x001514ec: stp x29,x30,[sp, #-0x50]! *)
(*    1381612: stp x29,x30,[sp, #-0x50]! *)
| 0x1514ec => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffb0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001514f0: mov x29,sp *)
(*    1381616: mov x29,sp *)
| 0x1514f0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x001514f4: stp x19,x20,[sp, #0x10] *)
(*    1381620: stp x19,x20,[sp, #0x10] *)
| 0x1514f4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001514f8: mov x19,x1 *)
(*    1381624: mov x19,x1 *)
| 0x1514f8 => Some (4,
	Move R_X19 (Var R_X1)
)

(* 0x001514fc: mov x20,#0x0 *)
(*    1381628: mov x20,#0x0 *)
| 0x1514fc => Some (4,
	Move R_X20 (Word 0x0 64)
)

(* 0x00151500: stp x21,x22,[sp, #0x20] *)
(*    1381632: stp x21,x22,[sp, #0x20] *)
| 0x151500 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151504: ldr x22,[x2] *)
(*    1381636: ldr x22,[x2] *)
| 0x151504 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move R_X22 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151508: stp x23,x24,[sp, #0x30] *)
(*    1381640: stp x23,x24,[sp, #0x30] *)
| 0x151508 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X23) $;
	Move (V_TEMP 0x39f80) (Var R_X24) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015150c: mov x23,x0 *)
(*    1381644: mov x23,x0 *)
| 0x15150c => Some (4,
	Move R_X23 (Var R_X0)
)

(* 0x00151510: mov x24,x4 *)
(*    1381648: mov x24,x4 *)
| 0x151510 => Some (4,
	Move R_X24 (Var R_X4)
)

(* 0x00151514: str x25,[sp, #0x40] *)
(*    1381652: str x25,[sp, #0x40] *)
| 0x151514 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X25)) LittleE 8)
)

(* 0x00151518: mov x25,x3 *)
(*    1381656: mov x25,x3 *)
| 0x151518 => Some (4,
	Move R_X25 (Var R_X3)
)

(* 0x0015151c: b 0x00151528 *)
(*    1381660: b 0x00151528 *)
| 0x15151c => Some (4,
	Jmp (Word 0x151528 64)
)

(* 0x00151520: add x19,x19,x25 *)
(*    1381664: add x19,x19,x25 *)
| 0x151520 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X25) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x12080))
)

(* 0x00151524: add x20,x20,#0x1 *)
(*    1381668: add x20,x20,#0x1 *)
| 0x151524 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x11b80))
)

(* 0x00151528: cmp x20,x22 *)
(*    1381672: cmp x20,x22 *)
| 0x151528 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X22) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X20) (Var R_X22)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X20) (Var R_X22)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X22) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X20) (Var R_X22)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015152c: b.eq 0x00151548 *)
(*    1381676: b.eq 0x00151548 *)
| 0x15152c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x151548 64)
	) (* else *) (
		Nop
	)
)

(* 0x00151530: mov x21,x19 *)
(*    1381680: mov x21,x19 *)
| 0x151530 => Some (4,
	Move R_X21 (Var R_X19)
)

(* 0x00151534: mov x1,x19 *)
(*    1381684: mov x1,x19 *)
| 0x151534 => Some (4,
	Move R_X1 (Var R_X19)
)

(* 0x00151538: mov x0,x23 *)
(*    1381688: mov x0,x23 *)
| 0x151538 => Some (4,
	Move R_X0 (Var R_X23)
)

(* 0x0015153c: blr x24 *)
(*    1381692: blr x24 *)
| 0x15153c => Some (4,
	Move R_PC (Var R_X24) $;
	Move R_X30 (BinOp OP_PLUS (Word 0x15153c 64) (Word 0x4 64)) $;
	Jmp (Var R_PC)
)

(* 0x00151540: cbnz w0,0x00151520 *)
(*    1381696: cbnz w0,0x00151520 *)
| 0x151540 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x151520 64)
	) (* else *) (
		Nop
	)
)

(* 0x00151544: b 0x0015154c *)
(*    1381700: b 0x0015154c *)
| 0x151544 => Some (4,
	Jmp (Word 0x15154c 64)
)

(* 0x00151548: mov x21,#0x0 *)
(*    1381704: mov x21,#0x0 *)
| 0x151548 => Some (4,
	Move R_X21 (Word 0x0 64)
)

(* 0x0015154c: ldr x25,[sp, #0x40] *)
(*    1381708: ldr x25,[sp, #0x40] *)
| 0x15154c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move R_X25 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00151550: mov x0,x21 *)
(*    1381712: mov x0,x21 *)
| 0x151550 => Some (4,
	Move R_X0 (Var R_X21)
)

(* 0x00151554: ldp x19,x20,[sp, #0x10] *)
(*    1381716: ldp x19,x20,[sp, #0x10] *)
| 0x151554 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x00151558: ldp x21,x22,[sp, #0x20] *)
(*    1381720: ldp x21,x22,[sp, #0x20] *)
| 0x151558 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x0015155c: ldp x23,x24,[sp, #0x30] *)
(*    1381724: ldp x23,x24,[sp, #0x30] *)
| 0x15155c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x00151560: ldp x29,x30,[sp], #0x50 *)
(*    1381728: ldp x29,x30,[sp], #0x50 *)
| 0x151560 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x00151564: ret *)
(*    1381732: ret *)
| 0x151564 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx lfind_armv8.
Proof. Picinae_typecheck. Qed.
