(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: isblank
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition isblank_armv7 : program := fun _ a => match a with

(* 0x0004d972: cmp r0,#0x9 *)
(*     317810: cmp r0,#0x9 *)
| 0x4d972 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x9 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x9 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x9 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004d974: it ne *)
(*     317812: it ne *)
| 0x4d974 => Some (2,
	Move (V_TEMP 0x95c00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0004d976: cmp.ne r0,#0x20 *)
(*     317814: cmp.ne r0,#0x20 *)
| 0x4d976 => Some (2,
	Move (V_TEMP 0x380) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x380))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4d978 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x20 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x20 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004d978: ite eq *)
(*     317816: ite eq *)
| 0x4d978 => Some (2,
	Move (V_TEMP 0x95b00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0004d97a: mov.eq r0,#0x1 *)
(*     317818: mov.eq r0,#0x1 *)
| 0x4d97a => Some (2,
	Move (V_TEMP 0x280) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1300) (UnOp OP_NOT (Var (V_TEMP 0x280))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1300))) (
		Jmp (Word 0x4d97c 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x1 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004d97c: mov.ne r0,#0x0 *)
(*     317820: mov.ne r0,#0x0 *)
| 0x4d97c => Some (2,
	Move (V_TEMP 0x380) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x380))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4d97e 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x0 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004d97e: bx lr *)
(*     317822: bx lr *)
| 0x4d97e => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx isblank_armv7.
Proof. Picinae_typecheck. Qed.
