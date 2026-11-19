(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_barrier_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_barrier_init_armv8 : program := fun _ a => match a with

(* 0x00161290: cmp w2,#0x0 *)
(*    1446544: cmp w2,#0x0 *)
| 0x161290 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00161294: b.le 0x001612bc *)
(*    1446548: b.le 0x001612bc *)
| 0x161294 => Some (4,
	Move (V_TEMP 0x1480) (BinOp OP_NEQ (Var R_NG) (Var R_OV)) $;
	Move (V_TEMP 0x1580) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var R_ZR)) (Var (V_TEMP 0x1480)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1580))) (
		Jmp (Word 0x1612bc 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161298: sub w2,w2,#0x1 *)
(*    1446552: sub w2,w2,#0x1 *)
| 0x161298 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x1 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0016129c: cbz x1,0x001612a8 *)
(*    1446556: cbz x1,0x001612a8 *)
| 0x16129c => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x1612a8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001612a0: ldr w1,[x1] *)
(*    1446560: ldr w1,[x1] *)
| 0x1612a0 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x001612a4: orr w2,w2,w1 *)
(*    1446564: orr w2,w2,w1 *)
| 0x1612a4 => Some (4,
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x001612a8: stp xzr,xzr,[x0] *)
(*    1446568: stp xzr,xzr,[x0] *)
| 0x1612a8 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001612ac: str w2,[x0, #0x8] *)
(*    1446572: str w2,[x0, #0x8] *)
| 0x1612ac => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X2))) LittleE 4)
)

(* 0x001612b0: stp xzr,xzr,[x0, #0x10] *)
(*    1446576: stp xzr,xzr,[x0, #0x10] *)
| 0x1612b0 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001612b4: mov w0,#0x0 *)
(*    1446580: mov w0,#0x0 *)
| 0x1612b4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001612b8: ret *)
(*    1446584: ret *)
| 0x1612b8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001612bc: mov w0,#0x16 *)
(*    1446588: mov w0,#0x16 *)
| 0x1612bc => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x001612c0: b 0x001612b8 *)
(*    1446592: b 0x001612b8 *)
| 0x1612c0 => Some (4,
	Jmp (Word 0x1612b8 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_barrier_init_armv8.
Proof. Picinae_typecheck. Qed.
