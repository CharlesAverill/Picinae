(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ffs
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ffs_armv8 : program := fun _ a => match a with

(* 0x0013b294: cbz w0,0x0013b2a8 *)
(*    1290900: cbz w0,0x0013b2a8 *)
| 0x13b294 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x13b2a8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b298: sxtw x0,w0 *)
(*    1290904: sxtw x0,w0 *)
| 0x13b298 => Some (4,
	Move R_X0 (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0013b29c: rbit x0,x0 *)
(*    1290908: rbit x0,x0 *)
| 0x13b29c => Some (4,
	Move (V_TEMP 0x2e980) (Var R_X0) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xaaaaaaaaaaaaaaaa 64)) $;
	Move (V_TEMP 0x2ea80) (BinOp OP_RSHIFT (Var (V_TEMP 0x2ea00)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2eb00) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0x5555555555555555 64)) $;
	Move (V_TEMP 0x2eb80) (BinOp OP_LSHIFT (Var (V_TEMP 0x2eb00)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_OR (Var (V_TEMP 0x2ea80)) (Var (V_TEMP 0x2eb80))) $;
	Move (V_TEMP 0x2ec80) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xcccccccccccccccc 64)) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_RSHIFT (Var (V_TEMP 0x2ec80)) (Word 0x2 64)) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0x3333333333333333 64)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_LSHIFT (Var (V_TEMP 0x2ed80)) (Word 0x2 64)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_OR (Var (V_TEMP 0x2ed00)) (Var (V_TEMP 0x2ee00))) $;
	Move (V_TEMP 0x2ef00) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xf0f0f0f0f0f0f0f0 64)) $;
	Move (V_TEMP 0x2ef80) (BinOp OP_RSHIFT (Var (V_TEMP 0x2ef00)) (Word 0x4 64)) $;
	Move (V_TEMP 0x2f000) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xf0f0f0f0f0f0f0f 64)) $;
	Move (V_TEMP 0x2f080) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f000)) (Word 0x4 64)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_OR (Var (V_TEMP 0x2ef80)) (Var (V_TEMP 0x2f080))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 0x2f200) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f180)) (Word 0x8 64)) $;
	Move (V_TEMP 0x2f280) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 0x2f300) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f280)) (Word 0x8 64)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_OR (Var (V_TEMP 0x2f200)) (Var (V_TEMP 0x2f300))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 0x2f480) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f400)) (Word 0x10 64)) $;
	Move (V_TEMP 0x2f500) (BinOp OP_AND (Var (V_TEMP 0x2e980)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 0x2f580) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f500)) (Word 0x10 64)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_OR (Var (V_TEMP 0x2f480)) (Var (V_TEMP 0x2f580))) $;
	Move (V_TEMP 0x2f680) (BinOp OP_RSHIFT (Var (V_TEMP 0x2e980)) (Word 0x20 64)) $;
	Move (V_TEMP 0x2f700) (BinOp OP_LSHIFT (Var (V_TEMP 0x2e980)) (Word 0x20 64)) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f700)))
)

(* 0x0013b2a0: clz x0,x0 *)
(*    1290912: clz x0,x0 *)
| 0x13b2a0 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Word 64 64) (UnOp OP_POPCOUNT (Var R_X0))))
)

(* 0x0013b2a4: add w0,w0,#0x1 *)
(*    1290916: add w0,w0,#0x1 *)
| 0x13b2a4 => Some (4,
	Move (V_TEMP 0x11680) (Word 0x1 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11680)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11780) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11780)))
)

(* 0x0013b2a8: ret *)
(*    1290920: ret *)
| 0x13b2a8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ffs_armv8.
Proof. Picinae_typecheck. Qed.
