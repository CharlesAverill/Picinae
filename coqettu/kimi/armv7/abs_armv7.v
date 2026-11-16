(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: abs
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition abs_armv7 : program := fun _ a => match a with

(* 0x0005a468: cmp r0,#0x0 *)
(*     369768: cmp r0,#0x0 *)
| 0x5a468 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005a46a: it lt *)
(*     369770: it lt *)
| 0x5a46a => Some (2,
	Move (V_TEMP 0x96700) (BinOp OP_EQ (Var R_NF) (Var R_VF))
)

(* 0x0005a46c: rsb.lt r0,r0 *)
(*     369772: rsb.lt r0,r0 *)
| 0x5a46c => Some (2,
	Move (V_TEMP 0xe80) (BinOp OP_NEQ (Var R_NF) (Var R_VF)) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0xe80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x5a46e 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005a46e: bx lr *)
(*     369774: bx lr *)
| 0x5a46e => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx abs_armv7.
Proof. Picinae_typecheck. Qed.
