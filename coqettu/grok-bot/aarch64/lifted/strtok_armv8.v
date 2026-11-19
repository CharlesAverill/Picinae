(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strtok
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strtok_armv8 : program := fun _ a => match a with

(* 0x0015f7c4: stp x29,x30,[sp, #-0x40]! *)
(*    1439684: stp x29,x30,[sp, #-0x40]! *)
| 0x15f7c4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f7c8: mov x29,sp *)
(*    1439688: mov x29,sp *)
| 0x15f7c8 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f7cc: stp x19,x20,[sp, #0x10] *)
(*    1439692: stp x19,x20,[sp, #0x10] *)
| 0x15f7cc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f7d0: mov x19,x0 *)
(*    1439696: mov x19,x0 *)
| 0x15f7d0 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f7d4: str x21,[sp, #0x20] *)
(*    1439700: str x21,[sp, #0x20] *)
| 0x15f7d4 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0015f7d8: adrp x21,0x1c2000 *)
(*    1439704: adrp x21,0x1c2000 *)
| 0x15f7d8 => Some (4,
	Move R_X21 (Word 0x1c2000 64)
)

(* 0x0015f7dc: cbz x0,0x0015f838 *)
(*    1439708: cbz x0,0x0015f838 *)
| 0x15f7dc => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15f838 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f7e0: mov x20,x1 *)
(*    1439712: mov x20,x1 *)
| 0x15f7e0 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015f7e4: mov x0,x19 *)
(*    1439716: mov x0,x19 *)
| 0x15f7e4 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015f7e8: bl 0x0015f2e8 *)
(*    1439720: bl 0x0015f2e8 *)
| 0x15f7e8 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f7e8 64) (Word 0x4 64)) $;
	Jmp (Word 0x15f2e8 64)
)

(* 0x0015f7ec: add x2,x19,x0 *)
(*    1439724: add x2,x19,x0 *)
| 0x15f7ec => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x0015f7f0: ldrb w0,[x19, x0, LSL ] *)
(*    1439728: ldrb w0,[x19, x0, LSL ] *)
| 0x15f7f0 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015f7f4: cbz w0,0x0015f844 *)
(*    1439732: cbz w0,0x0015f844 *)
| 0x15f7f4 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f844 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f7f8: mov x1,x20 *)
(*    1439736: mov x1,x20 *)
| 0x15f7f8 => Some (4,
	Move R_X1 (Var R_X20)
)

(* 0x0015f7fc: mov x0,x2 *)
(*    1439740: mov x0,x2 *)
| 0x15f7fc => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f800: str x2,[sp, #0x38] *)
(*    1439744: str x2,[sp, #0x38] *)
| 0x15f800 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x38 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x0015f804: bl 0x0015ecf0 *)
(*    1439748: bl 0x0015ecf0 *)
| 0x15f804 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f804 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ecf0 64)
)

(* 0x0015f808: ldr x2,[sp, #0x38] *)
(*    1439752: ldr x2,[sp, #0x38] *)
| 0x15f808 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x38 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f80c: add x1,x2,x0 *)
(*    1439756: add x1,x2,x0 *)
| 0x15f80c => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x0015f810: ldrb w3,[x2, x0, LSL ] *)
(*    1439760: ldrb w3,[x2, x0, LSL ] *)
| 0x15f810 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015f814: cbz w3,0x0015f850 *)
(*    1439764: cbz w3,0x0015f850 *)
| 0x15f814 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f850 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f818: add x1,x1,#0x1 *)
(*    1439768: add x1,x1,#0x1 *)
| 0x15f818 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015f81c: str x1,[x21, #0x5e0] *)
(*    1439772: str x1,[x21, #0x5e0] *)
| 0x15f81c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X21) (Word 0x5e0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x0015f820: strb wzr,[x2, x0, LSL ] *)
(*    1439776: strb wzr,[x2, x0, LSL ] *)
| 0x15f820 => Some (4,
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move (V_TEMP 0x3a400) (Var (V_TEMP 0x300)) $;
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a400)))) LittleE 1)
)

(* 0x0015f824: ldr x21,[sp, #0x20] *)
(*    1439780: ldr x21,[sp, #0x20] *)
| 0x15f824 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f828: mov x0,x2 *)
(*    1439784: mov x0,x2 *)
| 0x15f828 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f82c: ldp x19,x20,[sp, #0x10] *)
(*    1439788: ldp x19,x20,[sp, #0x10] *)
| 0x15f82c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015f830: ldp x29,x30,[sp], #0x40 *)
(*    1439792: ldp x29,x30,[sp], #0x40 *)
| 0x15f830 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f834: ret *)
(*    1439796: ret *)
| 0x15f834 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015f838: ldr x19,[x21, #0x5e0] *)
(*    1439800: ldr x19,[x21, #0x5e0] *)
| 0x15f838 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X21) (Word 0x5e0 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f83c: cbnz x19,0x0015f7e0 *)
(*    1439804: cbnz x19,0x0015f7e0 *)
| 0x15f83c => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X19) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15f7e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f840: b 0x0015f848 *)
(*    1439808: b 0x0015f848 *)
| 0x15f840 => Some (4,
	Jmp (Word 0x15f848 64)
)

(* 0x0015f844: str xzr,[x21, #0x5e0] *)
(*    1439812: str xzr,[x21, #0x5e0] *)
| 0x15f844 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X21) (Word 0x5e0 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x0015f848: mov x2,#0x0 *)
(*    1439816: mov x2,#0x0 *)
| 0x15f848 => Some (4,
	Move R_X2 (Word 0x0 64)
)

(* 0x0015f84c: b 0x0015f824 *)
(*    1439820: b 0x0015f824 *)
| 0x15f84c => Some (4,
	Jmp (Word 0x15f824 64)
)

(* 0x0015f850: str xzr,[x21, #0x5e0] *)
(*    1439824: str xzr,[x21, #0x5e0] *)
| 0x15f850 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X21) (Word 0x5e0 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x0015f854: b 0x0015f824 *)
(*    1439828: b 0x0015f824 *)
| 0x15f854 => Some (4,
	Jmp (Word 0x15f824 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx strtok_armv8.
Proof. Picinae_typecheck. Qed.
