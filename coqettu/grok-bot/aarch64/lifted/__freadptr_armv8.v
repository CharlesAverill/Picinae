(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __freadptr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __freadptr_armv8 : program := fun _ a => match a with

(* 0x001539d8: ldp x3,x2,[x0, #0x8] *)
(*    1391064: ldp x3,x2,[x0, #0x8] *)
| 0x1539d8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X3 (Var (V_TEMP 0x24180)) $;
	Move R_X2 (Var (V_TEMP 0x24300))
)

(* 0x001539dc: cmp x3,x2 *)
(*    1391068: cmp x3,x2 *)
| 0x1539dc => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X3) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001539e0: b.eq 0x001539f4 *)
(*    1391072: b.eq 0x001539f4 *)
| 0x1539e0 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x1539f4 64)
	) (* else *) (
		Nop
	)
)

(* 0x001539e4: sub x2,x2,x3 *)
(*    1391076: sub x2,x2,x3 *)
| 0x1539e4 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Var R_X3))
)

(* 0x001539e8: str x2,[x1] *)
(*    1391080: str x2,[x1] *)
| 0x1539e8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x001539ec: ldr x0,[x0, #0x8] *)
(*    1391084: ldr x0,[x0, #0x8] *)
| 0x1539ec => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x001539f0: ret *)
(*    1391088: ret *)
| 0x1539f0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001539f4: mov x0,#0x0 *)
(*    1391092: mov x0,#0x0 *)
| 0x1539f4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001539f8: b 0x001539f0 *)
(*    1391096: b 0x001539f0 *)
| 0x1539f8 => Some (4,
	Jmp (Word 0x1539f0 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __freadptr_armv8.
Proof. Picinae_typecheck. Qed.
