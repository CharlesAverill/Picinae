(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: cfgetospeed
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfgetospeed_armv7 : program := fun _ a => match a with

(* 0x0005c54a: movw r2,#0x100f *)
(*     378186: movw r2,#0x100f *)
| 0x5c54a => Some (4,
	Move R_R2 (Cast CAST_UNSIGNED 32 (Word 0x100f 16)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0005c54e: ldr r0,[r0,#0x8] *)
(*     378190: ldr r0,[r0,#0x8] *)
| 0x5c54e => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R0) (Word 0x8 32)) $;
	Move R_R0 (Load (Var V_MEM32) (Var (V_TEMP 0xa2680)) LittleE 4)
)

(* 0x0005c550: ands r0,r2 *)
(*     378192: ands r0,r2 *)
| 0x5c550 => Some (2,
	Move R_R0 (BinOp OP_AND (Var R_R0) (Var R_R2)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c552: bx lr *)
(*     378194: bx lr *)
| 0x5c552 => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx cfgetospeed_armv7.
Proof. Picinae_typecheck. Qed.
