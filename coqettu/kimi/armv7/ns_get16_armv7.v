(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: ns_get16
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ns_get16_armv7 : program := fun _ a => match a with

(* 0x00052f4a: ldrh r0,[r0,#0x0] *)
(*     339786: ldrh r0,[r0,#0x0] *)
| 0x52f4a => Some (2,
	Move (V_TEMP 0xa2780) (BinOp OP_PLUS (Var R_R0) (Word 0x0 32)) $;
	Move (V_TEMP 0xa7b80) (Load (Var V_MEM32) (Var (V_TEMP 0xa2780)) LittleE 2) $;
	Move R_R0 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7b80)))
)

(* 0x00052f4c: rev16 r0,r0 *)
(*     339788: rev16 r0,r0 *)
| 0x52f4c => Some (2,
	Move (V_TEMP 0xba080) (BinOp OP_AND (Var R_R0) (Word 0xff 32)) $;
	Move (V_TEMP 0xba100) (BinOp OP_RSHIFT (Var R_R0) (Word 0x8 32)) $;
	Move (V_TEMP 0xba200) (BinOp OP_AND (Var (V_TEMP 0xba100)) (Word 0xff 32)) $;
	Move (V_TEMP 0xba280) (BinOp OP_RSHIFT (Var R_R0) (Word 0x10 32)) $;
	Move (V_TEMP 0xba380) (BinOp OP_AND (Var (V_TEMP 0xba280)) (Word 0xff 32)) $;
	Move (V_TEMP 0xba400) (BinOp OP_RSHIFT (Var R_R0) (Word 0x18 32)) $;
	Move (V_TEMP 0xba500) (BinOp OP_AND (Var (V_TEMP 0xba400)) (Word 0xff 32)) $;
	Move (V_TEMP 0xba580) (BinOp OP_LSHIFT (Var (V_TEMP 0xba380)) (Word 0x18 32)) $;
	Move (V_TEMP 0xba600) (BinOp OP_LSHIFT (Var (V_TEMP 0xba500)) (Word 0x10 32)) $;
	Move (V_TEMP 0xba680) (BinOp OP_OR (Var (V_TEMP 0xba580)) (Var (V_TEMP 0xba600))) $;
	Move (V_TEMP 0xba700) (BinOp OP_LSHIFT (Var (V_TEMP 0xba080)) (Word 0x8 32)) $;
	Move (V_TEMP 0xba780) (BinOp OP_OR (Var (V_TEMP 0xba680)) (Var (V_TEMP 0xba700))) $;
	Move R_R0 (BinOp OP_OR (Var (V_TEMP 0xba780)) (Var (V_TEMP 0xba200)))
)

(* 0x00052f4e: uxth r0,r0 *)
(*     339790: uxth r0,r0 *)
| 0x52f4e => Some (2,
	Move (V_TEMP 0xe6700) (Cast CAST_LOW 16 (BinOp OP_RSHIFT (Var R_R0) (Word 0 32))) $;
	Move R_R0 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xe6700)))
)

(* 0x00052f50: bx lr *)
(*     339792: bx lr *)
| 0x52f50 => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx ns_get16_armv7.
Proof. Picinae_typecheck. Qed.
