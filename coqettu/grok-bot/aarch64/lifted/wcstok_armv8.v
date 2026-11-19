(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcstok
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcstok_armv8 : program := fun _ a => match a with

(* 0x0016013c: stp x29,x30,[sp, #-0x30]! *)
(*    1442108: stp x29,x30,[sp, #-0x30]! *)
| 0x16013c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00160140: mov x29,sp *)
(*    1442112: mov x29,sp *)
| 0x160140 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x00160144: stp x19,x20,[sp, #0x10] *)
(*    1442116: stp x19,x20,[sp, #0x10] *)
| 0x160144 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00160148: mov x19,x0 *)
(*    1442120: mov x19,x0 *)
| 0x160148 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0016014c: stp x21,x22,[sp, #0x20] *)
(*    1442124: stp x21,x22,[sp, #0x20] *)
| 0x16014c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00160150: mov x21,x2 *)
(*    1442128: mov x21,x2 *)
| 0x160150 => Some (4,
	Move R_X21 (Var R_X2)
)

(* 0x00160154: cbz x0,0x001601ac *)
(*    1442132: cbz x0,0x001601ac *)
| 0x160154 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x1601ac 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160158: mov x20,x1 *)
(*    1442136: mov x20,x1 *)
| 0x160158 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0016015c: mov x0,x19 *)
(*    1442140: mov x0,x19 *)
| 0x16015c => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x00160160: bl 0x0015fe6c *)
(*    1442144: bl 0x0015fe6c *)
| 0x160160 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x160160 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fe6c 64)
)

(* 0x00160164: add x22,x19,x0, LSL #0x2 *)
(*    1442148: add x22,x19,x0, LSL #0x2 *)
| 0x160164 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X22 (Var (V_TEMP 0x12080))
)

(* 0x00160168: ldr w0,[x19, x0, LSL #0x2] *)
(*    1442152: ldr w0,[x19, x0, LSL #0x2] *)
| 0x160168 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x0016016c: cbz w0,0x001601b8 *)
(*    1442156: cbz w0,0x001601b8 *)
| 0x16016c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x1601b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160170: mov x1,x20 *)
(*    1442160: mov x1,x20 *)
| 0x160170 => Some (4,
	Move R_X1 (Var R_X20)
)

(* 0x00160174: mov x0,x22 *)
(*    1442164: mov x0,x22 *)
| 0x160174 => Some (4,
	Move R_X0 (Var R_X22)
)

(* 0x00160178: bl 0x0015fb44 *)
(*    1442168: bl 0x0015fb44 *)
| 0x160178 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x160178 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fb44 64)
)

(* 0x0016017c: lsl x1,x0,#0x2 *)
(*    1442172: lsl x1,x0,#0x2 *)
| 0x16017c => Some (4,
	Move R_X1 (BinOp OP_LSHIFT (Var R_X0) (Word 0x2 64))
)

(* 0x00160180: add x0,x22,x0, LSL #0x2 *)
(*    1442176: add x0,x22,x0, LSL #0x2 *)
| 0x160180 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11f80))) (Var R_X22))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X22) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X22) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x00160184: ldr w2,[x22, x1, LSL #0x0] *)
(*    1442180: ldr w2,[x22, x1, LSL #0x0] *)
| 0x160184 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X1) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160188: cbz w2,0x001601c4 *)
(*    1442184: cbz w2,0x001601c4 *)
| 0x160188 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x1601c4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016018c: add x0,x0,#0x4 *)
(*    1442188: add x0,x0,#0x4 *)
| 0x16018c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x00160190: str wzr,[x22, x1, LSL #0x0] *)
(*    1442192: str wzr,[x22, x1, LSL #0x0] *)
| 0x160190 => Some (4,
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move (V_TEMP 0x3a200) (Var (V_TEMP 0x300)) $;
	Move (V_TEMP 0x5700) (Var R_X1) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a200))) LittleE 4)
)

(* 0x00160194: str x0,[x21] *)
(*    1442196: str x0,[x21] *)
| 0x160194 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X21) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00160198: mov x0,x22 *)
(*    1442200: mov x0,x22 *)
| 0x160198 => Some (4,
	Move R_X0 (Var R_X22)
)

(* 0x0016019c: ldp x19,x20,[sp, #0x10] *)
(*    1442204: ldp x19,x20,[sp, #0x10] *)
| 0x16019c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x001601a0: ldp x21,x22,[sp, #0x20] *)
(*    1442208: ldp x21,x22,[sp, #0x20] *)
| 0x1601a0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x001601a4: ldp x29,x30,[sp], #0x30 *)
(*    1442212: ldp x29,x30,[sp], #0x30 *)
| 0x1601a4 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x001601a8: ret *)
(*    1442216: ret *)
| 0x1601a8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001601ac: ldr x19,[x2] *)
(*    1442220: ldr x19,[x2] *)
| 0x1601ac => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x001601b0: cbnz x19,0x00160158 *)
(*    1442224: cbnz x19,0x00160158 *)
| 0x1601b0 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X19) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x160158 64)
	) (* else *) (
		Nop
	)
)

(* 0x001601b4: b 0x001601bc *)
(*    1442228: b 0x001601bc *)
| 0x1601b4 => Some (4,
	Jmp (Word 0x1601bc 64)
)

(* 0x001601b8: str xzr,[x21] *)
(*    1442232: str xzr,[x21] *)
| 0x1601b8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X21) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x001601bc: mov x22,#0x0 *)
(*    1442236: mov x22,#0x0 *)
| 0x1601bc => Some (4,
	Move R_X22 (Word 0x0 64)
)

(* 0x001601c0: b 0x00160198 *)
(*    1442240: b 0x00160198 *)
| 0x1601c0 => Some (4,
	Jmp (Word 0x160198 64)
)

(* 0x001601c4: str xzr,[x21] *)
(*    1442244: str xzr,[x21] *)
| 0x1601c4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X21) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x001601c8: b 0x00160198 *)
(*    1442248: b 0x00160198 *)
| 0x1601c8 => Some (4,
	Jmp (Word 0x160198 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx wcstok_armv8.
Proof. Picinae_typecheck. Qed.
