(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: imaxabs
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition imaxabs_armv7 : program := fun _ a => match a with

(* 0x0005a5cc: asrs r3,r1,#0x1f *)
(*     370124: asrs r3,r1,#0x1f *)
| 0x5a5cc => Some (2,
	Move (V_TEMP 0xa4300) (BinOp OP_MINUS (Word 0x1f 32) (Word 0x1 32)) $;
	Move (V_TEMP 0xa4380) (BinOp OP_ARSHIFT (Var R_R1) (Var (V_TEMP 0xa4300))) $;
	Move (V_TEMP 0xa4480) (BinOp OP_AND (Var (V_TEMP 0xa4380)) (Word 0x1 32)) $;
	Move (V_TEMP 0xa4500) (BinOp OP_EQ (Word 0x1f 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xa4580) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xa4500)) (Var R_CF))) $;
	Move (V_TEMP 0xa4600) (BinOp OP_NEQ (Word 0x1f 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xa4680) (BinOp OP_NEQ (Var (V_TEMP 0xa4480)) (Word 0x0 32)) $;
	Move (V_TEMP 0xa4700) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xa4600)) (Var (V_TEMP 0xa4680)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xa4580))) (Cast CAST_LOW 1 (Var (V_TEMP 0xa4700)))))) $;
	Move R_R3 (BinOp OP_ARSHIFT (Var R_R1) (Word 0x1f 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005a5ce: eor.w r0,r0,r1, asr #0x1f *)
(*     370126: eor.w r0,r0,r1, asr #0x1f *)
| 0x5a5ce => Some (4,
	Move (V_TEMP 0x98b00) (BinOp OP_MINUS (Word 0x1f 32) (Word 0x1 32)) $;
	Move (V_TEMP 0x98b80) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x98b00))) $;
	Move (V_TEMP 0x98c80) (BinOp OP_AND (Var (V_TEMP 0x98b80)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98c80)) (Word 0 32))) $;
	Move (V_TEMP 0x98e00) (BinOp OP_ARSHIFT (Var R_R1) (Word 0x1f 32)) $;
	Move R_R0 (BinOp OP_XOR (Var R_R0) (Var (V_TEMP 0x98e00))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005a5d2: subs r0,r0,r3 *)
(*     370130: subs r0,r0,r3 *)
| 0x5a5d2 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R3) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R3)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R0) (Var R_R3)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005a5d4: eor.w r1,r1,r1, asr #0x1f *)
(*     370132: eor.w r1,r1,r1, asr #0x1f *)
| 0x5a5d4 => Some (4,
	Move (V_TEMP 0x98b00) (BinOp OP_MINUS (Word 0x1f 32) (Word 0x1 32)) $;
	Move (V_TEMP 0x98b80) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x98b00))) $;
	Move (V_TEMP 0x98c80) (BinOp OP_AND (Var (V_TEMP 0x98b80)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98c80)) (Word 0 32))) $;
	Move (V_TEMP 0x98e00) (BinOp OP_ARSHIFT (Var R_R1) (Word 0x1f 32)) $;
	Move R_R1 (BinOp OP_XOR (Var R_R1) (Var (V_TEMP 0x98e00))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0005a5d8: sbc.w r1,r1,r3 *)
(*     370136: sbc.w r1,r1,r3 *)
| 0x5a5d8 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91800) (BinOp OP_MINUS (Var R_R1) (Var R_R3)) $;
	Move (V_TEMP 0x91880) (BinOp OP_LT (Var R_R3) (Var R_R1)) $;
	Move (V_TEMP 0x91900) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91980) (BinOp OP_LT (Var (V_TEMP 0x91800)) (Var (V_TEMP 0x91900))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var (V_TEMP 0x91880)) (Var (V_TEMP 0x91980))))) $;
	Move (V_TEMP 0x91a80) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Var R_R3)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Var R_R3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91b00) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0x91b80) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x91b00))) $;
	Move (V_TEMP 0x91c00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91800)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x91800)) (Var (V_TEMP 0x91b80))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x91800)) (Var (V_TEMP 0x91b80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91b80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91a80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91c00)))))) $;
	Move (V_TEMP 0xc2100) (BinOp OP_MINUS (Var R_R1) (Var R_R3)) $;
	Move (V_TEMP 0xc2180) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0xc2200) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc2180))) $;
	Move R_R1 (BinOp OP_MINUS (Var (V_TEMP 0xc2100)) (Var (V_TEMP 0xc2200))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0005a5dc: bx lr *)
(*     370140: bx lr *)
| 0x5a5dc => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx imaxabs_armv7.
Proof. Picinae_typecheck. Qed.
