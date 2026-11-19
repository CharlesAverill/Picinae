(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_condattr_setclock
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_condattr_setclock_armv8 : program := fun _ a => match a with

(* 0x00162484: sub w2,w1,#0x2 *)
(*    1451140: sub w2,w1,#0x2 *)
| 0x162484 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x00162488: cmp w1,#0x0 *)
(*    1451144: cmp w1,#0x0 *)
| 0x162488 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0016248c: ccmp w2,#0x1,#0x0,ge *)
(*    1451148: ccmp w2,#0x1,#0x0,ge *)
| 0x16248c => Some (4,
	Move (V_TEMP 0x1d80) (BinOp OP_EQ (Var R_NG) (Var R_OV)) $;
	Move (V_TEMP 0x19800) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x1d80))) $;
	Move (V_TEMP 0x19880) (Word 0x0 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19900) (BinOp OP_XOR (Var (V_TEMP 0x19800)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19900))) (
		Jmp (Word 0x162490 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x1 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19a00) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x1 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00162490: b.ls 0x001624ac *)
(*    1451152: b.ls 0x001624ac *)
| 0x162490 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x1624ac 64)
	) (* else *) (
		Nop
	)
)

(* 0x00162494: ldr w2,[x0] *)
(*    1451156: ldr w2,[x0] *)
| 0x162494 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00162498: and w2,w2,#0x80000000 *)
(*    1451160: and w2,w2,#0x80000000 *)
| 0x162498 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Word 0x80000000 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0016249c: orr w2,w2,w1 *)
(*    1451164: orr w2,w2,w1 *)
| 0x16249c => Some (4,
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x001624a0: str w2,[x0] *)
(*    1451168: str w2,[x0] *)
| 0x1624a0 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X2))) LittleE 4)
)

(* 0x001624a4: mov w0,#0x0 *)
(*    1451172: mov w0,#0x0 *)
| 0x1624a4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001624a8: ret *)
(*    1451176: ret *)
| 0x1624a8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001624ac: mov w0,#0x16 *)
(*    1451180: mov w0,#0x16 *)
| 0x1624ac => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x001624b0: b 0x001624a8 *)
(*    1451184: b 0x001624a8 *)
| 0x1624b0 => Some (4,
	Jmp (Word 0x1624a8 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_condattr_setclock_armv8.
Proof. Picinae_typecheck. Qed.
