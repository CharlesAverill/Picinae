(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wmemmove
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wmemmove_armv8 : program := fun _ a => match a with

(* 0x0016024c: cmp x0,x1 *)
(*    1442380: cmp x0,x1 *)
| 0x16024c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X1) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X1)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X1)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X1)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160250: b.eq 0x00160278 *)
(*    1442384: b.eq 0x00160278 *)
| 0x160250 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x160278 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160254: sub x3,x0,x1 *)
(*    1442388: sub x3,x0,x1 *)
| 0x160254 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X0) (Var R_X1))
)

(* 0x00160258: cmp x3,x2, LSL #0x2 *)
(*    1442392: cmp x3,x2, LSL #0x2 *)
| 0x160258 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X2) (Word 0x2 64)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x4400)) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x4400))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x4400))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x4400)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x4400))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0016025c: b.cc 0x00160274 *)
(*    1442396: b.cc 0x00160274 *)
| 0x16025c => Some (4,
	Move (V_TEMP 0xb00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xb00))) (
		Jmp (Word 0x160274 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160260: mov x3,#0x0 *)
(*    1442400: mov x3,#0x0 *)
| 0x160260 => Some (4,
	Move R_X3 (Word 0x0 64)
)

(* 0x00160264: b 0x00160288 *)
(*    1442404: b 0x00160288 *)
| 0x160264 => Some (4,
	Jmp (Word 0x160288 64)
)

(* 0x00160268: sub x2,x2,#0x1 *)
(*    1442408: sub x2,x2,#0x1 *)
| 0x160268 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0016026c: ldr w3,[x1, x2, LSL #0x2] *)
(*    1442412: ldr w3,[x1, x2, LSL #0x2] *)
| 0x16026c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160270: str w3,[x0, x2, LSL #0x2] *)
(*    1442416: str w3,[x0, x2, LSL #0x2] *)
| 0x160270 => Some (4,
	Move (V_TEMP 0x3a200) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a200))) LittleE 4)
)

(* 0x00160274: cbnz x2,0x00160268 *)
(*    1442420: cbnz x2,0x00160268 *)
| 0x160274 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x160268 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160278: ret *)
(*    1442424: ret *)
| 0x160278 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0016027c: ldr w4,[x1, x3, LSL #0x2] *)
(*    1442428: ldr w4,[x1, x3, LSL #0x2] *)
| 0x16027c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x24c80) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c80)))
)

(* 0x00160280: str w4,[x0, x3, LSL #0x2] *)
(*    1442432: str w4,[x0, x3, LSL #0x2] *)
| 0x160280 => Some (4,
	Move (V_TEMP 0x3a200) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x2 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a200))) LittleE 4)
)

(* 0x00160284: add x3,x3,#0x1 *)
(*    1442436: add x3,x3,#0x1 *)
| 0x160284 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x00160288: cmp x2,x3 *)
(*    1442440: cmp x2,x3 *)
| 0x160288 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X3)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X3)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X2) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0016028c: b.ne 0x0016027c *)
(*    1442444: b.ne 0x0016027c *)
| 0x16028c => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x16027c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160290: b 0x00160278 *)
(*    1442448: b 0x00160278 *)
| 0x160290 => Some (4,
	Jmp (Word 0x160278 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx wmemmove_armv8.
Proof. Picinae_typecheck. Qed.
