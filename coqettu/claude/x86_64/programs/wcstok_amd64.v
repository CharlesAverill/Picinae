(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcstok
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcstok_amd64 : program := fun _ a => match a with

(* 0x00166021: PUSH R12 *)
(*    1466401: PUSH R12 *)
| 0x166021 => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00166023: PUSH RBP *)
(*    1466403: PUSH RBP *)
| 0x166023 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00166024: PUSH RBX *)
(*    1466404: PUSH RBX *)
| 0x166024 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00166025: MOV RBX,RDI *)
(*    1466405: MOV RBX,RDI *)
| 0x166025 => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x00166028: TEST RDI,RDI *)
(*    1466408: TEST RDI,RDI *)
| 0x166028 => Some (3,
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

(* 0x0016602b: JZ 0x00166070 *)
(*    1466411: JZ 0x00166070 *)
| 0x16602b => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x166070 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016602d: MOV RDI,RBX *)
(*    1466413: MOV RDI,RBX *)
| 0x16602d => Some (3,
	Move R_RDI (Var R_RBX)
)

(* 0x00166030: MOV R12,RDX *)
(*    1466416: MOV R12,RDX *)
| 0x166030 => Some (3,
	Move R_R12 (Var R_RDX)
)

(* 0x00166033: MOV RBP,RSI *)
(*    1466419: MOV RBP,RSI *)
| 0x166033 => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x00166036: CALL 0x00165fec *)
(*    1466422: CALL 0x00165fec *)
| 0x166036 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x16603b 64)) LittleE 8) $;
	Jmp (Word 0x165fec 64)
)

(* 0x0016603b: LEA RBX,[RBX + RAX*0x4] *)
(*    1466427: LEA RBX,[RBX + RAX*0x4] *)
| 0x16603b => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x4 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RBX) (Var (V_TEMP 0x4980))) $;
	Move R_RBX (Var (V_TEMP 0x4a80))
)

(* 0x0016603f: MOV ECX,dword ptr [RBX] *)
(*    1466431: MOV ECX,dword ptr [RBX] *)
| 0x16603f => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RBX) LittleE 4) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00166041: TEST ECX,ECX *)
(*    1466433: TEST ECX,ECX *)
| 0x166041 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166043: JZ 0x0016607a *)
(*    1466435: JZ 0x0016607a *)
| 0x166043 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x16607a 64)
	) (* else *) (
		Nop
	)
)

(* 0x00166045: MOV RSI,RBP *)
(*    1466437: MOV RSI,RBP *)
| 0x166045 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x00166048: MOV RDI,RBX *)
(*    1466440: MOV RDI,RBX *)
| 0x166048 => Some (3,
	Move R_RDI (Var R_RBX)
)

(* 0x0016604b: CALL 0x00165e5a *)
(*    1466443: CALL 0x00165e5a *)
| 0x16604b => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x166050 64)) LittleE 8) $;
	Jmp (Word 0x165e5a 64)
)

(* 0x00166050: LEA RAX,[RBX + RAX*0x4] *)
(*    1466448: LEA RAX,[RBX + RAX*0x4] *)
| 0x166050 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x4 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RBX) (Var (V_TEMP 0x4980))) $;
	Move R_RAX (Var (V_TEMP 0x4a80))
)

(* 0x00166054: MOV EDX,dword ptr [RAX] *)
(*    1466452: MOV EDX,dword ptr [RAX] *)
| 0x166054 => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RAX) LittleE 4) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00166056: TEST EDX,EDX *)
(*    1466454: TEST EDX,EDX *)
| 0x166056 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166058: JZ 0x00166086 *)
(*    1466456: JZ 0x00166086 *)
| 0x166058 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x166086 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016605a: LEA RDX,[RAX + 0x4] *)
(*    1466458: LEA RDX,[RAX + 0x4] *)
| 0x16605a => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) $;
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x0016605e: MOV dword ptr [RAX],0x0 *)
(*    1466462: MOV dword ptr [RAX],0x0 *)
| 0x16605e => Some (6,
	Move (V_TEMP 0x6a00) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x00166064: MOV qword ptr [R12],RDX *)
(*    1466468: MOV qword ptr [R12],RDX *)
| 0x166064 => Some (4,
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R12) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00166068: MOV RAX,RBX *)
(*    1466472: MOV RAX,RBX *)
| 0x166068 => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x0016606b: POP RBX *)
(*    1466475: POP RBX *)
| 0x16606b => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x0016606c: POP RBP *)
(*    1466476: POP RBP *)
| 0x16606c => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x0016606d: POP R12 *)
(*    1466477: POP R12 *)
| 0x16606d => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x0016606f: RET *)
(*    1466479: RET *)
| 0x16606f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00166070: MOV RBX,qword ptr [RDX] *)
(*    1466480: MOV RBX,qword ptr [RDX] *)
| 0x166070 => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	Move R_RBX (Var (V_TEMP 0x11f00))
)

(* 0x00166073: TEST RBX,RBX *)
(*    1466483: TEST RBX,RBX *)
| 0x166073 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RBX) (Var R_RBX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166076: JNZ 0x0016602d *)
(*    1466486: JNZ 0x0016602d *)
| 0x166076 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x16602d 64)
	) (* else *) (
		Nop
	)
)

(* 0x00166078: JMP 0x00166082 *)
(*    1466488: JMP 0x00166082 *)
| 0x166078 => Some (2,
	Jmp (Word 0x166082 64)
)

(* 0x0016607a: MOV qword ptr [R12],0x0 *)
(*    1466490: MOV qword ptr [R12],0x0 *)
| 0x16607a => Some (8,
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R12) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00166082: XOR EBX,EBX *)
(*    1466498: XOR EBX,EBX *)
| 0x166082 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RBX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RBX)) (Extract 31 0 (Var R_RBX)))) (Word 0 64)) (BinOp OP_AND (Var R_RBX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RBX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RBX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RBX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RBX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166084: JMP 0x00166068 *)
(*    1466500: JMP 0x00166068 *)
| 0x166084 => Some (2,
	Jmp (Word 0x166068 64)
)

(* 0x00166086: MOV qword ptr [R12],0x0 *)
(*    1466502: MOV qword ptr [R12],0x0 *)
| 0x166086 => Some (8,
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R12) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0016608e: JMP 0x00166068 *)
(*    1466510: JMP 0x00166068 *)
| 0x16608e => Some (2,
	Jmp (Word 0x166068 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx wcstok_amd64.
Proof. Picinae_typecheck. Qed.
