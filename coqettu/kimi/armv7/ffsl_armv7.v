(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: ffsl
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ffsl_armv7 : program := fun _ a => match a with

(* 0x0005082e: cbz r0,0x0005083a *)
(*     329774: cbz r0,0x0005083a *)
| 0x5082e => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R0) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5083a 32)
	) (* else *) (
		Nop
	)
)

(* 0x00050830: rbit r0,r0 *)
(*     329776: rbit r0,r0 *)
| 0x50830 => Some (4,
	Move (V_TEMP 0xbbf00) (BinOp OP_AND (Var R_R0) (Word 0xff 32)) $;
	Move (V_TEMP 0xbbf80) (Cast CAST_LOW 8 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_RSHIFT (Var R_R0) (Word 0x8 32)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_AND (Var (V_TEMP 0xbc000)) (Word 0xff 32)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_LOW 8 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_RSHIFT (Var R_R0) (Word 0x10 32)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_AND (Var (V_TEMP 0xbc180)) (Word 0xff 32)) $;
	Move (V_TEMP 0xbc280) (Cast CAST_LOW 8 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_RSHIFT (Var R_R0) (Word 0x18 32)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_AND (Var (V_TEMP 0xbc300)) (Word 0xff 32)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_LOW 8 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbad80) (Var (V_TEMP 0xbbf80)) $;
	Move (V_TEMP 0xbae00) (Word 0x0 8) $;
	Move (V_TEMP 0xbae80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbae80)) (Var (V_TEMP 0xbaf00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb080)) (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb300) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb280)) (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb500) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb500))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb680)) (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb900) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb880)) (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbb00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbbc80)) (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbf80) (Var (V_TEMP 0xbae00)) $;
	Move (V_TEMP 0xbad80) (Var (V_TEMP 0xbc100)) $;
	Move (V_TEMP 0xbae00) (Word 0x0 8) $;
	Move (V_TEMP 0xbae80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbae80)) (Var (V_TEMP 0xbaf00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb080)) (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb300) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb280)) (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb500) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb500))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb680)) (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb900) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb880)) (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbb00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbbc80)) (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbc100) (Var (V_TEMP 0xbae00)) $;
	Move (V_TEMP 0xbad80) (Var (V_TEMP 0xbc280)) $;
	Move (V_TEMP 0xbae00) (Word 0x0 8) $;
	Move (V_TEMP 0xbae80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbae80)) (Var (V_TEMP 0xbaf00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb080)) (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb300) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb280)) (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb500) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb500))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb680)) (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb900) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb880)) (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbb00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbbc80)) (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbc280) (Var (V_TEMP 0xbae00)) $;
	Move (V_TEMP 0xbad80) (Var (V_TEMP 0xbc400)) $;
	Move (V_TEMP 0xbae00) (Word 0x0 8) $;
	Move (V_TEMP 0xbae80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbae80)) (Var (V_TEMP 0xbaf00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb080)) (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb300) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb280)) (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb500) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb500))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb680)) (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbb900) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbb880)) (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbb00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbae00)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbad80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbae00) (BinOp OP_OR (Var (V_TEMP 0xbbc80)) (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Var (V_TEMP 0xbad80)) (Cast CAST_LOW 8 (Word 0x1 32))) $;
	Move (V_TEMP 0xbc400) (Var (V_TEMP 0xbae00)) $;
	Move (V_TEMP 0xbc480) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbbf80))) $;
	Move (V_TEMP 0xbc500) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc480)) (Word 0x18 32)) $;
	Move (V_TEMP 0xbc580) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbc100))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc580)) (Word 0x10 32)) $;
	Move (V_TEMP 0xbc680) (BinOp OP_OR (Var (V_TEMP 0xbc500)) (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbc280))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 0x8 32)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc880) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbc400))) $;
	Move R_R0 (BinOp OP_OR (Var (V_TEMP 0xbc800)) (Var (V_TEMP 0xbc880)))
)

(* 0x00050834: clz r0,r0 *)
(*     329780: clz r0,r0 *)
| 0x50834 => Some (4,
	Move R_R0 (Cast CAST_UNSIGNED 32 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Var R_R0))))
)

(* 0x00050838: adds r0,#0x1 *)
(*     329784: adds r0,#0x1 *)
| 0x50838 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005083a: bx lr *)
(*     329786: bx lr *)
| 0x5083a => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx ffsl_armv7.
Proof. Picinae_typecheck. Qed.
