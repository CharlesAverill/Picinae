(* Automatically generated with pcode2coq
arch: amd64
file: linked_list
function: insert_in_sorted_list
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition linked_list_insert_in_sorted_list_amd64 : program := fun _ a => match a with

(* 0x00101360: MOV RAX,qword ptr [RSI] *)
(*          0: MOV RAX,qword ptr [RSI] *)
| 0x0 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x00101363: CMP RAX,0x7fffffff *)
(*          3: CMP RAX,0x7fffffff *)
| 0x3 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x7fffffff 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x7fffffff 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x7fffffff 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x7fffffff 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3e180) (BinOp OP_MINUS (Var R_RAX) (Word 0x7fffffff 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e180)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e180)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x00101369: JZ 0x00101388 *)
(*          9: JZ 0x00101388 *)
| 0x9 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x28 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010136b: NOP dword ptr [RAX + RAX*0x1] *)
(*         11: NOP dword ptr [RAX + RAX*0x1] *)
| 0xb => Some (5,
	Move (V_TEMP 0x5100) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5200) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5100)))
)

(* 0x00101370: MOV RDX,RDI *)
(*         16: MOV RDX,RDI *)
| 0x10 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x00101373: MOV RDI,qword ptr [RDI + 0x8] *)
(*         19: MOV RDI,qword ptr [RDI + 0x8] *)
| 0x13 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x00101377: CMP RAX,qword ptr [RDI] *)
(*         23: CMP RAX,qword ptr [RDI] *)
| 0x17 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move (V_TEMP 0x3f880) (Var (V_TEMP 0x12000)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 0x3f880)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RAX) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x0010137a: JNC 0x00101370 *)
(*         26: JNC 0x00101370 *)
| 0x1a => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_CF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x10 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010137c: MOV qword ptr [RSI + 0x8],RDI *)
(*         28: MOV qword ptr [RSI + 0x8],RDI *)
| 0x1c => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_LOW 64 (Var (V_TEMP 0x6b80))) LittleE 8)
)

(* 0x00101380: MOV qword ptr [RDX + 0x8],RSI *)
(*         32: MOV qword ptr [RDX + 0x8],RSI *)
| 0x20 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_LOW 64 (Var (V_TEMP 0x6b80))) LittleE 8)
)

(* 0x00101384: RET *)
(*         36: RET *)
| 0x24 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00101388: MOV RDX,RDI *)
(*         40: MOV RDX,RDI *)
| 0x28 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x0010138b: MOV RDI,qword ptr [RDI + 0x8] *)
(*         43: MOV RDI,qword ptr [RDI + 0x8] *)
| 0x2b => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x0010138f: MOV qword ptr [RSI + 0x8],RDI *)
(*         47: MOV qword ptr [RSI + 0x8],RDI *)
| 0x2f => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_LOW 64 (Var (V_TEMP 0x6b80))) LittleE 8)
)

(* 0x00101393: MOV qword ptr [RDX + 0x8],RSI *)
(*         51: MOV qword ptr [RDX + 0x8],RSI *)
| 0x33 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_LOW 64 (Var (V_TEMP 0x6b80))) LittleE 8)
)

(* 0x00101397: RET *)
(*         55: RET *)
| 0x37 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx linked_list_insert_in_sorted_list_amd64.
Proof. Picinae_typecheck. Qed.
