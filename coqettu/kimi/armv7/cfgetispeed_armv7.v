(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: cfgetispeed
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfgetispeed_armv7 : program := fun _ a => match a with

(* 0x0005c554: movw r3,#0x100f *)
(*     378196: movw r3,#0x100f *)
| 0x5c554 => Some (4,
	Move R_R3 (Cast CAST_UNSIGNED 32 (Word 0x100f 16)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005c558: ldrh r0,[r0,#0xa] *)
(*     378200: ldrh r0,[r0,#0xa] *)
| 0x5c558 => Some (2,
	Move (V_TEMP 0xa2780) (BinOp OP_PLUS (Var R_R0) (Word 0xa 32)) $;
	Move (V_TEMP 0xa7b80) (Load (Var V_MEM32) (Var (V_TEMP 0xa2780)) LittleE 2) $;
	Move R_R0 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7b80)))
)

(* 0x0005c55a: ands r0,r3 *)
(*     378202: ands r0,r3 *)
| 0x5c55a => Some (2,
	Move R_R0 (BinOp OP_AND (Var R_R0) (Var R_R3)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c55c: bx lr *)
(*     378204: bx lr *)
| 0x5c55c => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx cfgetispeed_armv7.
Proof. Picinae_typecheck. Qed.
