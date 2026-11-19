(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: getenv
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition getenv_armv8 : program := fun _ a => match a with

(* 0x0011ff88: stp x29,x30,[sp, #-0x30]! *)
(*    1179528: stp x29,x30,[sp, #-0x30]! *)
| 0x11ff88 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011ff8c: mov w1,#0x3d *)
(*    1179532: mov w1,#0x3d *)
| 0x11ff8c => Some (4,
	Move R_X1 (Word 0x3d 64)
)

(* 0x0011ff90: mov x29,sp *)
(*    1179536: mov x29,sp *)
| 0x11ff90 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0011ff94: str x21,[sp, #0x20] *)
(*    1179540: str x21,[sp, #0x20] *)
| 0x11ff94 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0011ff98: mov x21,x0 *)
(*    1179544: mov x21,x0 *)
| 0x11ff98 => Some (4,
	Move R_X21 (Var R_X0)
)

(* 0x0011ff9c: stp x19,x20,[sp, #0x10] *)
(*    1179548: stp x19,x20,[sp, #0x10] *)
| 0x11ff9c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011ffa0: bl 0x0015ebf4 *)
(*    1179552: bl 0x0015ebf4 *)
| 0x11ffa0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x11ffa0 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ebf4 64)
)

(* 0x0011ffa4: subs x20,x0,x21 *)
(*    1179556: subs x20,x0,x21 *)
| 0x11ffa4 => Some (4,
	Move (V_TEMP 0x3db80) (Var R_X21) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x3db80)) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x3db80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x3db80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3db80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x3dc80) (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x3db80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3dc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3dc80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x3dc80)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011ffa8: b.eq 0x0011ffc4 *)
(*    1179560: b.eq 0x0011ffc4 *)
| 0x11ffa8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x11ffc4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011ffac: ldrb w0,[x0] *)
(*    1179564: ldrb w0,[x0] *)
| 0x11ffac => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0011ffb0: cbnz w0,0x0011ffc4 *)
(*    1179568: cbnz w0,0x0011ffc4 *)
| 0x11ffb0 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x11ffc4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011ffb4: adrp x0,0x1bf000 *)
(*    1179572: adrp x0,0x1bf000 *)
| 0x11ffb4 => Some (4,
	Move R_X0 (Word 0x1bf000 64)
)

(* 0x0011ffb8: ldr x0,[x0, #0xfa8] *)
(*    1179576: ldr x0,[x0, #0xfa8] *)
| 0x11ffb8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0xfa8 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0011ffbc: ldr x19,[x0] *)
(*    1179580: ldr x19,[x0] *)
| 0x11ffbc => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0011ffc0: cbnz x19,0x0011ffdc *)
(*    1179584: cbnz x19,0x0011ffdc *)
| 0x11ffc0 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X19) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x11ffdc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011ffc4: mov x0,#0x0 *)
(*    1179588: mov x0,#0x0 *)
| 0x11ffc4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0011ffc8: ldr x21,[sp, #0x20] *)
(*    1179592: ldr x21,[sp, #0x20] *)
| 0x11ffc8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0011ffcc: ldp x19,x20,[sp, #0x10] *)
(*    1179596: ldp x19,x20,[sp, #0x10] *)
| 0x11ffcc => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0011ffd0: ldp x29,x30,[sp], #0x30 *)
(*    1179600: ldp x29,x30,[sp], #0x30 *)
| 0x11ffd0 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0011ffd4: ret *)
(*    1179604: ret *)
| 0x11ffd4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0011ffd8: add x19,x19,#0x8 *)
(*    1179608: add x19,x19,#0x8 *)
| 0x11ffd8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0011ffdc: ldr x1,[x19] *)
(*    1179612: ldr x1,[x19] *)
| 0x11ffdc => Some (4,
	Move (V_TEMP 0x6400) (Var R_X19) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0011ffe0: cbz x1,0x0011ffc4 *)
(*    1179616: cbz x1,0x0011ffc4 *)
| 0x11ffe0 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x11ffc4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011ffe4: mov x2,x20 *)
(*    1179620: mov x2,x20 *)
| 0x11ffe4 => Some (4,
	Move R_X2 (Var R_X20)
)

(* 0x0011ffe8: mov x0,x21 *)
(*    1179624: mov x0,x21 *)
| 0x11ffe8 => Some (4,
	Move R_X0 (Var R_X21)
)

(* 0x0011ffec: bl 0x0015f110 *)
(*    1179628: bl 0x0015f110 *)
| 0x11ffec => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x11ffec 64) (Word 0x4 64)) $;
	Jmp (Word 0x15f110 64)
)

(* 0x0011fff0: cbnz w0,0x0011ffd8 *)
(*    1179632: cbnz w0,0x0011ffd8 *)
| 0x11fff0 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x11ffd8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011fff4: ldr x0,[x19] *)
(*    1179636: ldr x0,[x19] *)
| 0x11fff4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X19) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0011fff8: ldrb w1,[x0, x20, LSL ] *)
(*    1179640: ldrb w1,[x0, x20, LSL ] *)
| 0x11fff8 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X20) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0011fffc: cmp w1,#0x3d *)
(*    1179644: cmp w1,#0x3d *)
| 0x11fffc => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x3d 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x3d 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x3d 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x3d 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3d 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00120000: b.ne 0x0011ffd8 *)
(*    1179648: b.ne 0x0011ffd8 *)
| 0x120000 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x11ffd8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00120004: add x20,x20,#0x1 *)
(*    1179652: add x20,x20,#0x1 *)
| 0x120004 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x11b80))
)

(* 0x00120008: add x0,x0,x20 *)
(*    1179656: add x0,x0,x20 *)
| 0x120008 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X20) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0012000c: b 0x0011ffc8 *)
(*    1179660: b 0x0011ffc8 *)
| 0x12000c => Some (4,
	Jmp (Word 0x11ffc8 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx getenv_armv8.
Proof. Picinae_typecheck. Qed.
