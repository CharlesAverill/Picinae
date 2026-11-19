(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strcasecmp
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcasecmp_armv8 : program := fun _ a => match a with

(* 0x0015ea9c: stp x29,x30,[sp, #-0x30]! *)
(*    1436316: stp x29,x30,[sp, #-0x30]! *)
| 0x15ea9c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015eaa0: mov x29,sp *)
(*    1436320: mov x29,sp *)
| 0x15eaa0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015eaa4: stp x19,x20,[sp, #0x10] *)
(*    1436324: stp x19,x20,[sp, #0x10] *)
| 0x15eaa4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015eaa8: mov x20,x0 *)
(*    1436328: mov x20,x0 *)
| 0x15eaa8 => Some (4,
	Move R_X20 (Var R_X0)
)

(* 0x0015eaac: mov x19,x1 *)
(*    1436332: mov x19,x1 *)
| 0x15eaac => Some (4,
	Move R_X19 (Var R_X1)
)

(* 0x0015eab0: str x21,[sp, #0x20] *)
(*    1436336: str x21,[sp, #0x20] *)
| 0x15eab0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0015eab4: b 0x0015eac0 *)
(*    1436340: b 0x0015eac0 *)
| 0x15eab4 => Some (4,
	Jmp (Word 0x15eac0 64)
)

(* 0x0015eab8: add x20,x20,#0x1 *)
(*    1436344: add x20,x20,#0x1 *)
| 0x15eab8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x11b80))
)

(* 0x0015eabc: add x19,x19,#0x1 *)
(*    1436348: add x19,x19,#0x1 *)
| 0x15eabc => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015eac0: ldrb w2,[x20] *)
(*    1436352: ldrb w2,[x20] *)
| 0x15eac0 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X20) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015eac4: mov w0,w2 *)
(*    1436356: mov w0,w2 *)
| 0x15eac4 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015eac8: cbz w2,0x0015eaf8 *)
(*    1436360: cbz w2,0x0015eaf8 *)
| 0x15eac8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15eaf8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015eacc: ldrb w1,[x19] *)
(*    1436364: ldrb w1,[x19] *)
| 0x15eacc => Some (4,
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ead0: cbz w1,0x0015eaf8 *)
(*    1436368: cbz w1,0x0015eaf8 *)
| 0x15ead0 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15eaf8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ead4: cmp w2,w1 *)
(*    1436372: cmp w2,w1 *)
| 0x15ead4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ead8: b.eq 0x0015eab8 *)
(*    1436376: b.eq 0x0015eab8 *)
| 0x15ead8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15eab8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015eadc: bl 0x0011f2d0 *)
(*    1436380: bl 0x0011f2d0 *)
| 0x15eadc => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15eadc 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015eae0: mov w21,w0 *)
(*    1436384: mov w21,w0 *)
| 0x15eae0 => Some (4,
	Move R_X21 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0015eae4: ldrb w0,[x19] *)
(*    1436388: ldrb w0,[x19] *)
| 0x15eae4 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015eae8: bl 0x0011f2d0 *)
(*    1436392: bl 0x0011f2d0 *)
| 0x15eae8 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15eae8 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015eaec: cmp w21,w0 *)
(*    1436396: cmp w21,w0 *)
| 0x15eaec => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X21)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X21)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X21)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X21)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X21)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015eaf0: b.eq 0x0015eab8 *)
(*    1436400: b.eq 0x0015eab8 *)
| 0x15eaf0 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15eab8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015eaf4: ldrb w2,[x20] *)
(*    1436404: ldrb w2,[x20] *)
| 0x15eaf4 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X20) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015eaf8: mov w0,w2 *)
(*    1436408: mov w0,w2 *)
| 0x15eaf8 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015eafc: bl 0x0011f2d0 *)
(*    1436412: bl 0x0011f2d0 *)
| 0x15eafc => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15eafc 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015eb00: mov w20,w0 *)
(*    1436416: mov w20,w0 *)
| 0x15eb00 => Some (4,
	Move R_X20 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0015eb04: ldrb w0,[x19] *)
(*    1436420: ldrb w0,[x19] *)
| 0x15eb04 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015eb08: bl 0x0011f2d0 *)
(*    1436424: bl 0x0011f2d0 *)
| 0x15eb08 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15eb08 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015eb0c: sub w0,w20,w0 *)
(*    1436428: sub w0,w20,w0 *)
| 0x15eb0c => Some (4,
	Move (V_TEMP 0x3cc80) (BinOp OP_MINUS (Extract 31 0 (Var R_X20)) (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3cc80)))
)

(* 0x0015eb10: ldr x21,[sp, #0x20] *)
(*    1436432: ldr x21,[sp, #0x20] *)
| 0x15eb10 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015eb14: ldp x19,x20,[sp, #0x10] *)
(*    1436436: ldp x19,x20,[sp, #0x10] *)
| 0x15eb14 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015eb18: ldp x29,x30,[sp], #0x30 *)
(*    1436440: ldp x29,x30,[sp], #0x30 *)
| 0x15eb18 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015eb1c: ret *)
(*    1436444: ret *)
| 0x15eb1c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strcasecmp_armv8.
Proof. Picinae_typecheck. Qed.
