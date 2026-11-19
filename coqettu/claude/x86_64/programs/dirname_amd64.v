(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: dirname
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition dirname_amd64 : program := fun _ a => match a with

(* 0x0013b3b0: TEST RDI,RDI *)
(*    1291184: TEST RDI,RDI *)
| 0x13b3b0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3b3: JZ 0x0013b3ba *)
(*    1291187: JZ 0x0013b3ba *)
| 0x13b3b3 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x13b3ba 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b3b5: CMP byte ptr [RDI],0x0 *)
(*    1291189: CMP byte ptr [RDI],0x0 *)
| 0x13b3b5 => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RDI) LittleE 1) $;
	Move (V_TEMP 0x3e100) (Var (V_TEMP 0x11d80)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e100)) (Word 0x0 8))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e100)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x0 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x0 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e200) (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x0 8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e200)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3b8: JNZ 0x0013b3ce *)
(*    1291192: JNZ 0x0013b3ce *)
| 0x13b3b8 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13b3ce 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b3ba: LEA RAX,[0x1a22a6] *)
(*    1291194: LEA RAX,[0x1a22a6] *)
| 0x13b3ba => Some (7,
	Move R_RAX (Word 0x1a22a6 64)
)

(* 0x0013b3c1: RET *)
(*    1291201: RET *)
| 0x13b3c1 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0013b3c2: LEA RAX,[0x1a22a6] *)
(*    1291202: LEA RAX,[0x1a22a6] *)
| 0x13b3c2 => Some (7,
	Move R_RAX (Word 0x1a22a6 64)
)

(* 0x0013b3c9: ADD RSP,0x18 *)
(*    1291209: ADD RSP,0x18 *)
| 0x13b3c9 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Var R_RSP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3cd: RET *)
(*    1291213: RET *)
| 0x13b3cd => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0013b3ce: SUB RSP,0x18 *)
(*    1291214: SUB RSP,0x18 *)
| 0x13b3ce => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSP) (Word 0x18 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3d2: MOV qword ptr [RSP + 0x8],RDI *)
(*    1291218: MOV qword ptr [RSP + 0x8],RDI *)
| 0x13b3d2 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6a80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0013b3d7: CALL 0x001348c0 *)
(*    1291223: CALL 0x001348c0 *)
| 0x13b3d7 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x13b3dc 64)) LittleE 8) $;
	Jmp (Word 0x1348c0 64)
)

(* 0x0013b3dc: MOV RDI,qword ptr [RSP + 0x8] *)
(*    1291228: MOV RDI,qword ptr [RSP + 0x8] *)
| 0x13b3dc => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x11f00))
)

(* 0x0013b3e1: SUB RAX,0x1 *)
(*    1291233: SUB RAX,0x1 *)
| 0x13b3e1 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3e5: CMP byte ptr [RDI + RAX*0x1],0x2f *)
(*    1291237: CMP byte ptr [RDI + RAX*0x1],0x2f *)
| 0x13b3e5 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x3e100) (Var (V_TEMP 0x11d80)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e100)) (Word 0x2f 8))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e100)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2f 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e200) (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e200)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3e9: JNZ 0x0013b400 *)
(*    1291241: JNZ 0x0013b400 *)
| 0x13b3e9 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13b400 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b3eb: TEST RAX,RAX *)
(*    1291243: TEST RAX,RAX *)
| 0x13b3eb => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3ee: JZ 0x0013b42f *)
(*    1291246: JZ 0x0013b42f *)
| 0x13b3ee => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x13b42f 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b3f0: SUB RAX,0x1 *)
(*    1291248: SUB RAX,0x1 *)
| 0x13b3f0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b3f4: JMP 0x0013b3e5 *)
(*    1291252: JMP 0x0013b3e5 *)
| 0x13b3f4 => Some (2,
	Jmp (Word 0x13b3e5 64)
)

(* 0x0013b400: TEST RAX,RAX *)
(*    1291264: TEST RAX,RAX *)
| 0x13b400 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b403: JZ 0x0013b3c2 *)
(*    1291267: JZ 0x0013b3c2 *)
| 0x13b403 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x13b3c2 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b405: SUB RAX,0x1 *)
(*    1291269: SUB RAX,0x1 *)
| 0x13b405 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b409: CMP byte ptr [RDI + RAX*0x1],0x2f *)
(*    1291273: CMP byte ptr [RDI + RAX*0x1],0x2f *)
| 0x13b409 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x3e100) (Var (V_TEMP 0x11d80)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e100)) (Word 0x2f 8))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e100)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2f 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e200) (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e200)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b40d: JNZ 0x0013b400 *)
(*    1291277: JNZ 0x0013b400 *)
| 0x13b40d => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13b400 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b40f: JMP 0x0013b424 *)
(*    1291279: JMP 0x0013b424 *)
| 0x13b40f => Some (2,
	Jmp (Word 0x13b424 64)
)

(* 0x0013b420: SUB RAX,0x1 *)
(*    1291296: SUB RAX,0x1 *)
| 0x13b420 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b424: CMP byte ptr [RDI + RAX*0x1],0x2f *)
(*    1291300: CMP byte ptr [RDI + RAX*0x1],0x2f *)
| 0x13b424 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x3e100) (Var (V_TEMP 0x11d80)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e100)) (Word 0x2f 8))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e100)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2f 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e200) (BinOp OP_MINUS (Var (V_TEMP 0x3e100)) (Word 0x2f 8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e200)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e200)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b428: JNZ 0x0013b438 *)
(*    1291304: JNZ 0x0013b438 *)
| 0x13b428 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13b438 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b42a: TEST RAX,RAX *)
(*    1291306: TEST RAX,RAX *)
| 0x13b42a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013b42d: JNZ 0x0013b420 *)
(*    1291309: JNZ 0x0013b420 *)
| 0x13b42d => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13b420 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b42f: LEA RAX,[0x1a282c] *)
(*    1291311: LEA RAX,[0x1a282c] *)
| 0x13b42f => Some (7,
	Move R_RAX (Word 0x1a282c 64)
)

(* 0x0013b436: JMP 0x0013b3c9 *)
(*    1291318: JMP 0x0013b3c9 *)
| 0x13b436 => Some (2,
	Jmp (Word 0x13b3c9 64)
)

(* 0x0013b438: MOV byte ptr [RDI + RAX*0x1 + 0x1],0x0 *)
(*    1291320: MOV byte ptr [RDI + RAX*0x1 + 0x1],0x0 *)
| 0x13b438 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x1 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6900) (Word 0x0 8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x6900))) LittleE 1)
)

(* 0x0013b43d: MOV RAX,RDI *)
(*    1291325: MOV RAX,RDI *)
| 0x13b43d => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x0013b440: JMP 0x0013b3c9 *)
(*    1291328: JMP 0x0013b3c9 *)
| 0x13b440 => Some (2,
	Jmp (Word 0x13b3c9 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx dirname_amd64.
Proof. Picinae_typecheck. Qed.
