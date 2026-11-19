(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strncasecmp
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strncasecmp_amd64 : program := fun _ a => match a with

(* 0x00165ab9: TEST RDX,RDX *)
(*    1465017: TEST RDX,RDX *)
| 0x165ab9 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165abc: JZ 0x00165b31 *)
(*    1465020: JZ 0x00165b31 *)
| 0x165abc => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165b31 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165abe: PUSH R13 *)
(*    1465022: PUSH R13 *)
| 0x165abe => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R13) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165ac0: PUSH R12 *)
(*    1465024: PUSH R12 *)
| 0x165ac0 => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165ac2: LEA R12,[RDI + RDX*0x1 + -0x1] *)
(*    1465026: LEA R12,[RDI + RDX*0x1 + -0x1] *)
| 0x165ac2 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffff 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_R12 (Var (V_TEMP 0x5080))
)

(* 0x00165ac7: PUSH RBP *)
(*    1465031: PUSH RBP *)
| 0x165ac7 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165ac8: MOV RBP,RSI *)
(*    1465032: MOV RBP,RSI *)
| 0x165ac8 => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x00165acb: PUSH RBX *)
(*    1465035: PUSH RBX *)
| 0x165acb => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165acc: MOV RBX,RDI *)
(*    1465036: MOV RBX,RDI *)
| 0x165acc => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x00165acf: SUB RSP,0x8 *)
(*    1465039: SUB RSP,0x8 *)
| 0x165acf => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSP) (Word 0x8 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165ad3: JMP 0x00165add *)
(*    1465043: JMP 0x00165add *)
| 0x165ad3 => Some (2,
	Jmp (Word 0x165add 64)
)

(* 0x00165ad5: ADD RBX,0x1 *)
(*    1465045: ADD RBX,0x1 *)
| 0x165ad5 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) (Var R_RBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165ad9: ADD RBP,0x1 *)
(*    1465049: ADD RBP,0x1 *)
| 0x165ad9 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBP) (Word 0x1 64)) (Var R_RBP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBP) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBP (BinOp OP_PLUS (Var R_RBP) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165add: MOVZX EDI,byte ptr [RBX] *)
(*    1465053: MOVZX EDI,byte ptr [RBX] *)
| 0x165add => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165ae0: TEST DIL,DIL *)
(*    1465056: TEST DIL,DIL *)
| 0x165ae0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6ff80) (BinOp OP_AND (Extract 7 0 (Var R_RDI)) (Extract 7 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x6ff80)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x6ff80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x6ff80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165ae3: JZ 0x00165b10 *)
(*    1465059: JZ 0x00165b10 *)
| 0x165ae3 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165b10 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165ae5: MOVZX EAX,byte ptr [RBP] *)
(*    1465061: MOVZX EAX,byte ptr [RBP] *)
| 0x165ae5 => Some (4,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBP) LittleE 1) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00165ae9: CMP RBX,R12 *)
(*    1465065: CMP RBX,R12 *)
| 0x165ae9 => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RBX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R12))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R12)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R12)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R12)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165aec: JZ 0x00165b10 *)
(*    1465068: JZ 0x00165b10 *)
| 0x165aec => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165b10 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165aee: TEST AL,AL *)
(*    1465070: TEST AL,AL *)
| 0x165aee => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6ff80) (BinOp OP_AND (Extract 7 0 (Var R_RAX)) (Extract 7 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x6ff80)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x6ff80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x6ff80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165af0: JZ 0x00165b10 *)
(*    1465072: JZ 0x00165b10 *)
| 0x165af0 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165b10 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165af2: CMP DIL,AL *)
(*    1465074: CMP DIL,AL *)
| 0x165af2 => Some (3,
	Move (V_TEMP 0x3eb80) (Extract 7 0 (Var R_RDI)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3eb80)) (Extract 7 0 (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb80)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb80)) (Extract 7 0 (Var R_RAX))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb80)) (Extract 7 0 (Var R_RAX))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RAX)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3ec80) (BinOp OP_MINUS (Var (V_TEMP 0x3eb80)) (Extract 7 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3ec80)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3ec80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3ec80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165af5: JZ 0x00165ad5 *)
(*    1465077: JZ 0x00165ad5 *)
| 0x165af5 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165ad5 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165af7: CALL 0x00141924 *)
(*    1465079: CALL 0x00141924 *)
| 0x165af7 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165afc 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165afc: MOVZX EDI,byte ptr [RBP] *)
(*    1465084: MOVZX EDI,byte ptr [RBP] *)
| 0x165afc => Some (4,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBP) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165b00: MOV R13D,EAX *)
(*    1465088: MOV R13D,EAX *)
| 0x165b00 => Some (3,
	Move R_R13 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_R13) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_R13 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R13)))
)

(* 0x00165b03: CALL 0x00141924 *)
(*    1465091: CALL 0x00141924 *)
| 0x165b03 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165b08 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165b08: CMP R13D,EAX *)
(*    1465096: CMP R13D,EAX *)
| 0x165b08 => Some (3,
	Move (V_TEMP 0x3ee80) (Extract 31 0 (Var R_R13)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3ee80)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ee80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ee80)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ee80)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ef80) (BinOp OP_MINUS (Var (V_TEMP 0x3ee80)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3ef80)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3ef80)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3ef80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165b0b: JZ 0x00165ad5 *)
(*    1465099: JZ 0x00165ad5 *)
| 0x165b0b => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165ad5 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165b0d: MOVZX EDI,byte ptr [RBX] *)
(*    1465101: MOVZX EDI,byte ptr [RBX] *)
| 0x165b0d => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165b10: CALL 0x00141924 *)
(*    1465104: CALL 0x00141924 *)
| 0x165b10 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165b15 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165b15: MOVZX EDI,byte ptr [RBP] *)
(*    1465109: MOVZX EDI,byte ptr [RBP] *)
| 0x165b15 => Some (4,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBP) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165b19: MOV EBX,EAX *)
(*    1465113: MOV EBX,EAX *)
| 0x165b19 => Some (2,
	Move R_RBX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RBX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RBX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBX)))
)

(* 0x00165b1b: CALL 0x00141924 *)
(*    1465115: CALL 0x00141924 *)
| 0x165b1b => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165b20 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165b20: ADD RSP,0x8 *)
(*    1465120: ADD RSP,0x8 *)
| 0x165b20 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Var R_RSP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165b24: MOV EDX,EAX *)
(*    1465124: MOV EDX,EAX *)
| 0x165b24 => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00165b26: MOV EAX,EBX *)
(*    1465126: MOV EAX,EBX *)
| 0x165b26 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBX))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00165b28: POP RBX *)
(*    1465128: POP RBX *)
| 0x165b28 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165b29: POP RBP *)
(*    1465129: POP RBP *)
| 0x165b29 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00165b2a: SUB EAX,EDX *)
(*    1465130: SUB EAX,EDX *)
| 0x165b2a => Some (2,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165b2c: POP R12 *)
(*    1465132: POP R12 *)
| 0x165b2c => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00165b2e: POP R13 *)
(*    1465134: POP R13 *)
| 0x165b2e => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55200))
)

(* 0x00165b30: RET *)
(*    1465136: RET *)
| 0x165b30 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00165b31: XOR EAX,EAX *)
(*    1465137: XOR EAX,EAX *)
| 0x165b31 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165b33: RET *)
(*    1465139: RET *)
| 0x165b33 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strncasecmp_amd64.
Proof. Picinae_typecheck. Qed.
