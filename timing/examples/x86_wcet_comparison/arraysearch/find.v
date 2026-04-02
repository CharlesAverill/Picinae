(* Automatically generated with pcode2coq
arch: amd64
file: arraysearch
function: find
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition arraysearch_find_amd64 : program := fun _ a => match a with

(* 0x00101140: MOVZX ECX,SI *)
(*          0: MOVZX ECX,SI *)
| 0x0 => Some (3,
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 15 0 (Var R_RSI))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00101143: TEST SI,SI *)
(*          3: TEST SI,SI *)
| 0x3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70380) (BinOp OP_AND (Extract 15 0 (Var R_RSI)) (Extract 15 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70380)) (Word 0x0 16))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70380)) (Word 0x0 16))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70380)) (Word 0xff 16)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x00101146: JZ 0x00101160 *)
(*          6: JZ 0x00101160 *)
| 0x6 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x20 64)
	) (* else *) (
		Nop
	)
)

(* 0x00101148: XOR EAX,EAX *)
(*          8: XOR EAX,EAX *)
| 0x8 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x0010114a: JMP 0x00101158 *)
(*         10: JMP 0x00101158 *)
| 0xa => Some (2,
	Jmp (Word 0x18 64)
)

(* 0x00101150: ADD RAX,0x1 *)
(*         16: ADD RAX,0x1 *)
| 0x10 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x00101154: CMP EAX,ECX *)
(*         20: CMP EAX,ECX *)
| 0x14 => Some (2,
	Move (V_TEMP 0x3ef80) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x00101156: JNC 0x00101160 *)
(*         22: JNC 0x00101160 *)
| 0x16 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_CF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x20 64)
	) (* else *) (
		Nop
	)
)

(* 0x00101158: CMP qword ptr [RDI + RAX*0x8],RDX *)
(*         24: CMP qword ptr [RDI + RAX*0x8],RDX *)
| 0x18 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x8 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move (V_TEMP 0x3f100) (Var (V_TEMP 0x12000)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x0010115c: JNZ 0x00101150 *)
(*         28: JNZ 0x00101150 *)
| 0x1c => Some (2,
	Move (V_TEMP 0x12880) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x10 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010115e: RET *)
(*         30: RET *)
| 0x1e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00101160: MOV EAX,0xffffffff *)
(*         32: MOV EAX,0xffffffff *)
| 0x20 => Some (5,
	Move R_RAX (Word 0xffffffff 64)
)

(* 0x00101165: RET *)
(*         37: RET *)
| 0x25 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx arraysearch_find_amd64.
Proof. Picinae_typecheck. Qed.
