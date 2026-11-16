(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: sigismember
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition sigismember_armv8 : program := fun _ a => match a with

(* 0x00152330: sub w1,w1,#0x1 *)
(*    1385264: sub w1,w1,#0x1 *)
| 0x152330 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x1 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x00152334: cmp w1,#0x3f *)
(*    1385268: cmp w1,#0x3f *)
| 0x152334 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x3f 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x3f 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x3f 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x3f 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3f 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00152338: b.hi 0x0015234c *)
(*    1385272: b.hi 0x0015234c *)
| 0x152338 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x15234c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015233c: ldr x0,[x0] *)
(*    1385276: ldr x0,[x0] *)
| 0x15233c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00152340: lsr x0,x0,x1 *)
(*    1385280: lsr x0,x0,x1 *)
| 0x152340 => Some (4,
	Move (V_TEMP 0x28300) (BinOp OP_AND (Var R_X1) (Word 0x3f 64)) $;
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Var (V_TEMP 0x28300)))
)

(* 0x00152344: and w0,w0,#0x1 *)
(*    1385284: and w0,w0,#0x1 *)
| 0x152344 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00152348: ret *)
(*    1385288: ret *)
| 0x152348 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015234c: mov w0,#0x0 *)
(*    1385292: mov w0,#0x0 *)
| 0x15234c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00152350: b 0x00152348 *)
(*    1385296: b 0x00152348 *)
| 0x152350 => Some (4,
	Jmp (Word 0x152348 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx sigismember_armv8.
Proof. Picinae_typecheck. Qed.
