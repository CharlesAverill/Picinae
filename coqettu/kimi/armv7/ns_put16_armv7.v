(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: ns_put16
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ns_put16_armv7 : program := fun _ a => match a with

(* 0x00052f58: lsrs r3,r0,#0x8 *)
(*     339800: lsrs r3,r0,#0x8 *)
| 0x52f58 => Some (2,
	Move (V_TEMP 0xacd80) (Word 0x8 32) $;
	Move (V_TEMP 0xac800) (BinOp OP_MINUS (Var (V_TEMP 0xacd80)) (Word 0x1 32)) $;
	Move (V_TEMP 0xac880) (BinOp OP_RSHIFT (Var R_R0) (Var (V_TEMP 0xac800))) $;
	Move (V_TEMP 0xac980) (BinOp OP_AND (Var (V_TEMP 0xac880)) (Word 0x1 32)) $;
	Move (V_TEMP 0xaca00) (BinOp OP_EQ (Var (V_TEMP 0xacd80)) (Word 0x0 32)) $;
	Move (V_TEMP 0xaca80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xaca00)) (Var R_CF))) $;
	Move (V_TEMP 0xacb00) (BinOp OP_NEQ (Var (V_TEMP 0xacd80)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacb80) (BinOp OP_NEQ (Var (V_TEMP 0xac980)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacc00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xacb00)) (Var (V_TEMP 0xacb80)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xaca80))) (Cast CAST_LOW 1 (Var (V_TEMP 0xacc00)))))) $;
	Move R_R3 (BinOp OP_RSHIFT (Var R_R0) (Word 0x8 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x00052f5a: strb r0,[r1,#0x1] *)
(*     339802: strb r0,[r1,#0x1] *)
| 0x52f5a => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R1) (Word 0x1 32)) $;
	Move (V_TEMP 0xd2200) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var R_R0) (Word 0 32))) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2880)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0xd2200))) LittleE 1)
)

(* 0x00052f5c: strb r3,[r1,#0x0] *)
(*     339804: strb r3,[r1,#0x0] *)
| 0x52f5c => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R1) (Word 0x0 32)) $;
	Move (V_TEMP 0xd2200) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var R_R3) (Word 0 32))) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2880)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0xd2200))) LittleE 1)
)

(* 0x00052f5e: bx lr *)
(*     339806: bx lr *)
| 0x52f5e => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx ns_put16_armv7.
Proof. Picinae_typecheck. Qed.
