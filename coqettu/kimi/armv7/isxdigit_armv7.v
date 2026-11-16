(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: isxdigit
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition isxdigit_armv7 : program := fun _ a => match a with

(* 0x0004dbb6: sub.w r3,r0,#0x30 *)
(*     318390: sub.w r3,r0,#0x30 *)
| 0x4dbb6 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x30 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97780)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0004dbba: cmp r3,#0x9 *)
(*     318394: cmp r3,#0x9 *)
| 0x4dbba => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x9 32) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Word 0x9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Word 0x9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x9 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R3) (Word 0x9 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004dbbc: bls 0x0004dbce *)
(*     318396: bls 0x0004dbce *)
| 0x4dbbc => Some (2,
	Move (V_TEMP 0x94300) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0x94400) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var (V_TEMP 0x94300)) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x94400))) (
		Jmp (Word 0x4dbce 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004dbbe: orr r0,r0,#0x20 *)
(*     318398: orr r0,r0,#0x20 *)
| 0x4dbbe => Some (4,
	Move (V_TEMP 0x97780) (Word 0x20 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R0 (BinOp OP_OR (Var R_R0) (Var (V_TEMP 0x97780))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004dbc2: subs r0,#0x61 *)
(*     318402: subs r0,#0x61 *)
| 0x4dbc2 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x61 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x61 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x61 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x61 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R0) (Word 0x61 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004dbc4: cmp r0,#0x5 *)
(*     318404: cmp r0,#0x5 *)
| 0x4dbc4 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x5 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x5 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x5 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x5 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004dbc6: ite hi *)
(*     318406: ite hi *)
| 0x4dbc6 => Some (2,
	Move (V_TEMP 0x96280) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0x96380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var R_CF) (Var (V_TEMP 0x96280))))
)

(* 0x0004dbc8: mov.hi r0,#0x0 *)
(*     318408: mov.hi r0,#0x0 *)
| 0x4dbc8 => Some (2,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xb00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var R_CF) (Var (V_TEMP 0xa00)))) $;
	Move (V_TEMP 0x1300) (UnOp OP_NOT (Var (V_TEMP 0xb00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1300))) (
		Jmp (Word 0x4dbca 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x0 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004dbca: mov.ls r0,#0x1 *)
(*     318410: mov.ls r0,#0x1 *)
| 0x4dbca => Some (2,
	Move (V_TEMP 0xb80) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0xc80) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var (V_TEMP 0xb80)) (Var R_ZF))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0xc80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4dbcc 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x1 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004dbcc: bx lr *)
(*     318412: bx lr *)
| 0x4dbcc => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x0004dbce: movs r0,#0x1 *)
(*     318414: movs r0,#0x1 *)
| 0x4dbce => Some (2,
	Move R_R0 (Word 0x1 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0004dbd0: bx lr *)
(*     318416: bx lr *)
| 0x4dbd0 => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx isxdigit_armv7.
Proof. Picinae_typecheck. Qed.
