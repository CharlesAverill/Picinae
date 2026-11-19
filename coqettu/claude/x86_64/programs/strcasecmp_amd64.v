(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strcasecmp
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcasecmp_amd64 : program := fun _ a => match a with

(* 0x001658e8: PUSH R12 *)
(*    1464552: PUSH R12 *)
| 0x1658e8 => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001658ea: PUSH RBP *)
(*    1464554: PUSH RBP *)
| 0x1658ea => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001658eb: MOV RBP,RDI *)
(*    1464555: MOV RBP,RDI *)
| 0x1658eb => Some (3,
	Move R_RBP (Var R_RDI)
)

(* 0x001658ee: PUSH RBX *)
(*    1464558: PUSH RBX *)
| 0x1658ee => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001658ef: MOV RBX,RSI *)
(*    1464559: MOV RBX,RSI *)
| 0x1658ef => Some (3,
	Move R_RBX (Var R_RSI)
)

(* 0x001658f2: JMP 0x001658fc *)
(*    1464562: JMP 0x001658fc *)
| 0x1658f2 => Some (2,
	Jmp (Word 0x1658fc 64)
)

(* 0x001658f4: ADD RBP,0x1 *)
(*    1464564: ADD RBP,0x1 *)
| 0x1658f4 => Some (4,
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

(* 0x001658f8: ADD RBX,0x1 *)
(*    1464568: ADD RBX,0x1 *)
| 0x1658f8 => Some (4,
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

(* 0x001658fc: MOVZX EDI,byte ptr [RBP] *)
(*    1464572: MOVZX EDI,byte ptr [RBP] *)
| 0x1658fc => Some (4,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBP) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165900: TEST DIL,DIL *)
(*    1464576: TEST DIL,DIL *)
| 0x165900 => Some (3,
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

(* 0x00165903: JZ 0x0016592a *)
(*    1464579: JZ 0x0016592a *)
| 0x165903 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x16592a 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165905: MOVZX EAX,byte ptr [RBX] *)
(*    1464581: MOVZX EAX,byte ptr [RBX] *)
| 0x165905 => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00165908: TEST AL,AL *)
(*    1464584: TEST AL,AL *)
| 0x165908 => Some (2,
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

(* 0x0016590a: JZ 0x0016592a *)
(*    1464586: JZ 0x0016592a *)
| 0x16590a => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x16592a 64)
	) (* else *) (
		Nop
	)
)

(* 0x0016590c: CMP DIL,AL *)
(*    1464588: CMP DIL,AL *)
| 0x16590c => Some (3,
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

(* 0x0016590f: JZ 0x001658f4 *)
(*    1464591: JZ 0x001658f4 *)
| 0x16590f => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x1658f4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165911: CALL 0x00141924 *)
(*    1464593: CALL 0x00141924 *)
| 0x165911 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165916 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165916: MOVZX EDI,byte ptr [RBX] *)
(*    1464598: MOVZX EDI,byte ptr [RBX] *)
| 0x165916 => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165919: MOV R12D,EAX *)
(*    1464601: MOV R12D,EAX *)
| 0x165919 => Some (3,
	Move R_R12 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_R12) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_R12 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R12)))
)

(* 0x0016591c: CALL 0x00141924 *)
(*    1464604: CALL 0x00141924 *)
| 0x16591c => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165921 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165921: CMP R12D,EAX *)
(*    1464609: CMP R12D,EAX *)
| 0x165921 => Some (3,
	Move (V_TEMP 0x3ee80) (Extract 31 0 (Var R_R12)) $;
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

(* 0x00165924: JZ 0x001658f4 *)
(*    1464612: JZ 0x001658f4 *)
| 0x165924 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x1658f4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165926: MOVZX EDI,byte ptr [RBP] *)
(*    1464614: MOVZX EDI,byte ptr [RBP] *)
| 0x165926 => Some (4,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBP) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x0016592a: CALL 0x00141924 *)
(*    1464618: CALL 0x00141924 *)
| 0x16592a => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x16592f 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x0016592f: MOVZX EDI,byte ptr [RBX] *)
(*    1464623: MOVZX EDI,byte ptr [RBX] *)
| 0x16592f => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00165932: MOV EBP,EAX *)
(*    1464626: MOV EBP,EAX *)
| 0x165932 => Some (2,
	Move R_RBP (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RBP) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RBP (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBP)))
)

(* 0x00165934: CALL 0x00141924 *)
(*    1464628: CALL 0x00141924 *)
| 0x165934 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165939 64)) LittleE 8) $;
	Jmp (Word 0x141924 64)
)

(* 0x00165939: POP RBX *)
(*    1464633: POP RBX *)
| 0x165939 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x0016593a: MOV EDX,EAX *)
(*    1464634: MOV EDX,EAX *)
| 0x16593a => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0016593c: MOV EAX,EBP *)
(*    1464636: MOV EAX,EBP *)
| 0x16593c => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBP))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0016593e: POP RBP *)
(*    1464638: POP RBP *)
| 0x16593e => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x0016593f: POP R12 *)
(*    1464639: POP R12 *)
| 0x16593f => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00165941: SUB EAX,EDX *)
(*    1464641: SUB EAX,EDX *)
| 0x165941 => Some (2,
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

(* 0x00165943: RET *)
(*    1464643: RET *)
| 0x165943 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strcasecmp_amd64.
Proof. Picinae_typecheck. Qed.
