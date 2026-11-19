(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __freading
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __freading_armv8 : program := fun _ a => match a with

(* 0x0015392c: ldr w1,[x0] *)
(*    1390892: ldr w1,[x0] *)
| 0x15392c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00153930: tbnz w1,#0x3,0x00153944 *)
(*    1390896: tbnz w1,#0x3,0x00153944 *)
| 0x153930 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x3 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x153944 64)
	) (* else *) (
		Nop
	)
)

(* 0x00153934: ldr x0,[x0, #0x10] *)
(*    1390900: ldr x0,[x0, #0x10] *)
| 0x153934 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00153938: cmp x0,#0x0 *)
(*    1390904: cmp x0,#0x0 *)
| 0x153938 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015393c: cset w0,ne *)
(*    1390908: cset w0,ne *)
| 0x15393c => Some (4,
	Move (V_TEMP 0x2300) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2300)))
)

(* 0x00153940: ret *)
(*    1390912: ret *)
| 0x153940 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00153944: mov w0,#0x1 *)
(*    1390916: mov w0,#0x1 *)
| 0x153944 => Some (4,
	Move R_X0 (Word 0x1 64)
)

(* 0x00153948: b 0x00153940 *)
(*    1390920: b 0x00153940 *)
| 0x153948 => Some (4,
	Jmp (Word 0x153940 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __freading_armv8.
Proof. Picinae_typecheck. Qed.
