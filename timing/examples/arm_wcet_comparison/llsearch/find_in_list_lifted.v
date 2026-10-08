(* Automatically generated with pcode2coq
arch: amd64
file: linked_list
function: find_in_list
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition linked_list_find_in_list_amd64 : program := fun _ a => match a with

(* 0x00101330: JMP 0x00101349 *)
(*          0: JMP 0x00101349 *)
| 0x0 => Some (2,
	Jmp (Word 0x19 64)
)

(* 0x00101340: CMP RSI,qword ptr [RDI] *)
(*         16: CMP RSI,qword ptr [RDI] *)
| 0x10 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move (V_TEMP 0x3f880) (Var (V_TEMP 0x12000)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSI) (Var (V_TEMP 0x3f880)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RSI) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x00101343: JZ 0x00101358 *)
(*         19: JZ 0x00101358 *)
| 0x13 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x28 64)
	) (* else *) (
		Nop
	)
)

(* 0x00101345: MOV RDI,qword ptr [RDI + 0x8] *)
(*         21: MOV RDI,qword ptr [RDI + 0x8] *)
| 0x15 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx linked_list_find_in_list_amd64.
Proof. Picinae_typecheck. Qed.
