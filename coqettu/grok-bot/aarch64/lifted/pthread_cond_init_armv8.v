(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_cond_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_cond_init_armv8 : program := fun _ a => match a with

(* 0x00161c04: stp xzr,xzr,[x0] *)
(*    1448964: stp xzr,xzr,[x0] *)
| 0x161c04 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00161c08: stp xzr,xzr,[x0, #0x10] *)
(*    1448968: stp xzr,xzr,[x0, #0x10] *)
| 0x161c08 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00161c0c: stp xzr,xzr,[x0, #0x20] *)
(*    1448972: stp xzr,xzr,[x0, #0x20] *)
| 0x161c0c => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00161c10: cbz x1,0x00161c24 *)
(*    1448976: cbz x1,0x00161c24 *)
| 0x161c10 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x161c24 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161c14: ldr w1,[x1] *)
(*    1448980: ldr w1,[x1] *)
| 0x161c14 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00161c18: and w2,w1,#0x7fffffff *)
(*    1448984: and w2,w1,#0x7fffffff *)
| 0x161c18 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0x7fffffff 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00161c1c: str w2,[x0, #0x10] *)
(*    1448988: str w2,[x0, #0x10] *)
| 0x161c1c => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X2))) LittleE 4)
)

(* 0x00161c20: tbnz w1,#0x1f,0x00161c2c *)
(*    1448992: tbnz w1,#0x1f,0x00161c2c *)
| 0x161c20 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x161c2c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161c24: mov w0,#0x0 *)
(*    1448996: mov w0,#0x0 *)
| 0x161c24 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161c28: ret *)
(*    1449000: ret *)
| 0x161c28 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00161c2c: mov x1,#-0x1 *)
(*    1449004: mov x1,#-0x1 *)
| 0x161c2c => Some (4,
	Move R_X1 (Word 0xffffffffffffffff 64)
)

(* 0x00161c30: str x1,[x0] *)
(*    1449008: str x1,[x0] *)
| 0x161c30 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x00161c34: b 0x00161c24 *)
(*    1449012: b 0x00161c24 *)
| 0x161c34 => Some (4,
	Jmp (Word 0x161c24 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_cond_init_armv8.
Proof. Picinae_typecheck. Qed.
