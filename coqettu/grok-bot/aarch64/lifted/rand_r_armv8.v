(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: rand_r
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition rand_r_armv8 : program := fun _ a => match a with

(* 0x00147f38: ldr w1,[x0] *)
(*    1343288: ldr w1,[x0] *)
| 0x147f38 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00147f3c: mov w3,#0x4e6d *)
(*    1343292: mov w3,#0x4e6d *)
| 0x147f3c => Some (4,
	Move R_X3 (Word 0x4e6d 64)
)

(* 0x00147f40: movk w3,#0x41c6, LSL #16 *)
(*    1343296: movk w3,#0x41c6, LSL #16 *)
| 0x147f40 => Some (4,
	Move (V_TEMP 0x29b00) (BinOp OP_AND (Extract 31 0 (Var R_X3)) (Word 0xffff 32)) $;
	Move (V_TEMP 0x29b00) (BinOp OP_OR (Var (V_TEMP 0x29b00)) (Word 0x41c60000 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x29b00)))
)

(* 0x00147f44: mov w2,#0x3039 *)
(*    1343300: mov w2,#0x3039 *)
| 0x147f44 => Some (4,
	Move R_X2 (Word 0x3039 64)
)

(* 0x00147f48: madd w1,w1,w3,w2 *)
(*    1343304: madd w1,w1,w3,w2 *)
| 0x147f48 => Some (4,
	Move (V_TEMP 0x28880) (BinOp OP_TIMES (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x28880))) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x28880))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x28880)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x28980) (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x28880))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28980)))
)

(* 0x00147f4c: str w1,[x0] *)
(*    1343308: str w1,[x0] *)
| 0x147f4c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00147f50: eor w0,w1,w1, LSR #0xb *)
(*    1343312: eor w0,w1,w1, LSR #0xb *)
| 0x147f50 => Some (4,
	Move (V_TEMP 0x3f80) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0xb 32)) $;
	Move (V_TEMP 0x1ff00) (BinOp OP_XOR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3f80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1ff00)))
)

(* 0x00147f54: mov w1,#0x5680 *)
(*    1343316: mov w1,#0x5680 *)
| 0x147f54 => Some (4,
	Move R_X1 (Word 0x5680 64)
)

(* 0x00147f58: movk w1,#0x9d2c, LSL #16 *)
(*    1343320: movk w1,#0x9d2c, LSL #16 *)
| 0x147f58 => Some (4,
	Move (V_TEMP 0x29b00) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0xffff 32)) $;
	Move (V_TEMP 0x29b00) (BinOp OP_OR (Var (V_TEMP 0x29b00)) (Word 0x9d2c0000 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x29b00)))
)

(* 0x00147f5c: and w1,w1,w0, LSL #0x7 *)
(*    1343324: and w1,w1,w0, LSL #0x7 *)
| 0x147f5c => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x7 32)) $;
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x00147f60: eor w0,w0,w1 *)
(*    1343328: eor w0,w0,w1 *)
| 0x147f60 => Some (4,
	Move (V_TEMP 0x1ff00) (BinOp OP_XOR (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1ff00)))
)

(* 0x00147f64: mov w1,#0xefc60000 *)
(*    1343332: mov w1,#0xefc60000 *)
| 0x147f64 => Some (4,
	Move R_X1 (Word 0xefc60000 64)
)

(* 0x00147f68: and w1,w1,w0, LSL #0xf *)
(*    1343336: and w1,w1,w0, LSL #0xf *)
| 0x147f68 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0xf 32)) $;
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x00147f6c: eor w0,w0,w1 *)
(*    1343340: eor w0,w0,w1 *)
| 0x147f6c => Some (4,
	Move (V_TEMP 0x1ff00) (BinOp OP_XOR (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1ff00)))
)

(* 0x00147f70: eor w0,w0,w0, LSR #0x12 *)
(*    1343344: eor w0,w0,w0, LSR #0x12 *)
| 0x147f70 => Some (4,
	Move (V_TEMP 0x3f80) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x12 32)) $;
	Move (V_TEMP 0x1ff00) (BinOp OP_XOR (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x3f80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1ff00)))
)

(* 0x00147f74: lsr w0,w0,#0x1 *)
(*    1343348: lsr w0,w0,#0x1 *)
| 0x147f74 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x00147f78: ret *)
(*    1343352: ret *)
| 0x147f78 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx rand_r_armv8.
Proof. Picinae_typecheck. Qed.
