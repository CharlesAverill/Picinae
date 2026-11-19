(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcscspn
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcscspn_amd64 : program := fun _ a => match a with

(* 0x00165e5a: MOV EAX,dword ptr [RSI] *)
(*    1465946: MOV EAX,dword ptr [RSI] *)
| 0x165e5a => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RSI) LittleE 4) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00165e5c: TEST EAX,EAX *)
(*    1465948: TEST EAX,EAX *)
| 0x165e5c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165e5e: JZ 0x00165ea0 *)
(*    1465950: JZ 0x00165ea0 *)
| 0x165e5e => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165ea0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165e60: PUSH R12 *)
(*    1465952: PUSH R12 *)
| 0x165e60 => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165e62: MOV R12,RSI *)
(*    1465954: MOV R12,RSI *)
| 0x165e62 => Some (3,
	Move R_R12 (Var R_RSI)
)

(* 0x00165e65: PUSH RBP *)
(*    1465957: PUSH RBP *)
| 0x165e65 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165e66: MOV RBP,RDI *)
(*    1465958: MOV RBP,RDI *)
| 0x165e66 => Some (3,
	Move R_RBP (Var R_RDI)
)

(* 0x00165e69: PUSH RBX *)
(*    1465961: PUSH RBX *)
| 0x165e69 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165e6a: MOV EDX,dword ptr [RSI + 0x4] *)
(*    1465962: MOV EDX,dword ptr [RSI + 0x4] *)
| 0x165e6a => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00165e6d: MOV RBX,RDI *)
(*    1465965: MOV RBX,RDI *)
| 0x165e6d => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x00165e70: TEST EDX,EDX *)
(*    1465968: TEST EDX,EDX *)
| 0x165e70 => Some (2,
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

(* 0x00165e72: JZ 0x00165e8d *)
(*    1465970: JZ 0x00165e8d *)
| 0x165e72 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165e8d 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165e74: MOV ESI,dword ptr [RBX] *)
(*    1465972: MOV ESI,dword ptr [RBX] *)
| 0x165e74 => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RBX) LittleE 4) $;
	Move R_RSI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RSI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00165e76: TEST ESI,ESI *)
(*    1465974: TEST ESI,ESI *)
| 0x165e76 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165e78: JZ 0x00165ea5 *)
(*    1465976: JZ 0x00165ea5 *)
| 0x165e78 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165ea5 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165e7a: MOV RDI,R12 *)
(*    1465978: MOV RDI,R12 *)
| 0x165e7a => Some (3,
	Move R_RDI (Var R_R12)
)

(* 0x00165e7d: CALL 0x0013c310 *)
(*    1465981: CALL 0x0013c310 *)
| 0x165e7d => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165e82 64)) LittleE 8) $;
	Jmp (Word 0x13c310 64)
)

(* 0x00165e82: TEST RAX,RAX *)
(*    1465986: TEST RAX,RAX *)
| 0x165e82 => Some (3,
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

(* 0x00165e85: JNZ 0x00165ea5 *)
(*    1465989: JNZ 0x00165ea5 *)
| 0x165e85 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x165ea5 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165e87: ADD RBX,0x4 *)
(*    1465991: ADD RBX,0x4 *)
| 0x165e87 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) (Var R_RBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165e8b: JMP 0x00165e74 *)
(*    1465995: JMP 0x00165e74 *)
| 0x165e8b => Some (2,
	Jmp (Word 0x165e74 64)
)

(* 0x00165e8d: MOV ESI,EAX *)
(*    1465997: MOV ESI,EAX *)
| 0x165e8d => Some (2,
	Move R_RSI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RSI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00165e8f: CALL 0x0013c310 *)
(*    1465999: CALL 0x0013c310 *)
| 0x165e8f => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165e94 64)) LittleE 8) $;
	Jmp (Word 0x13c310 64)
)

(* 0x00165e94: TEST RAX,RAX *)
(*    1466004: TEST RAX,RAX *)
| 0x165e94 => Some (3,
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

(* 0x00165e97: JNZ 0x00165ea8 *)
(*    1466007: JNZ 0x00165ea8 *)
| 0x165e97 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x165ea8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165e99: POP RBX *)
(*    1466009: POP RBX *)
| 0x165e99 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165e9a: MOV RDI,RBP *)
(*    1466010: MOV RDI,RBP *)
| 0x165e9a => Some (3,
	Move R_RDI (Var R_RBP)
)

(* 0x00165e9d: POP RBP *)
(*    1466013: POP RBP *)
| 0x165e9d => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00165e9e: POP R12 *)
(*    1466014: POP R12 *)
| 0x165e9e => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00165ea0: JMP 0x0013c380 *)
(*    1466016: JMP 0x0013c380 *)
| 0x165ea0 => Some (5,
	Jmp (Word 0x13c380 64)
)

(* 0x00165ea5: MOV RAX,RBX *)
(*    1466021: MOV RAX,RBX *)
| 0x165ea5 => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x00165ea8: SUB RAX,RBP *)
(*    1466024: SUB RAX,RBP *)
| 0x165ea8 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Var R_RBP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165eab: POP RBX *)
(*    1466027: POP RBX *)
| 0x165eab => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165eac: POP RBP *)
(*    1466028: POP RBP *)
| 0x165eac => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00165ead: SAR RAX,0x2 *)
(*    1466029: SAR RAX,0x2 *)
| 0x165ead => Some (4,
	Move (V_TEMP 0x68800) (BinOp OP_AND (Word 0x2 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x68880) (Var R_RAX) $;
	Move R_RAX (BinOp OP_ARSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68800)))) $;
	Move (V_TEMP 0x2ef00) (BinOp OP_NEQ (Var (V_TEMP 0x68800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2ef80) (BinOp OP_MINUS (Var (V_TEMP 0x68800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f000) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2ef80)))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f180) (BinOp OP_NEQ (Var (V_TEMP 0x2f080)) (Word 0x0 64)) $;
	Move (V_TEMP 0x2f200) (UnOp OP_NOT (Var (V_TEMP 0x2ef00))) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f200)) (Var R_CF))) $;
	Move (V_TEMP 0x2f300) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ef00)) (Var (V_TEMP 0x2f180)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2f280))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2f300)))))) $;
	Move (V_TEMP 0x2f480) (BinOp OP_EQ (Var (V_TEMP 0x68800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f500) (UnOp OP_NOT (Var (V_TEMP 0x2f480))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f500)) (Var R_OF)))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x68800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x00165eb1: POP R12 *)
(*    1466033: POP R12 *)
| 0x165eb1 => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00165eb3: RET *)
(*    1466035: RET *)
| 0x165eb3 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx wcscspn_amd64.
Proof. Picinae_typecheck. Qed.
