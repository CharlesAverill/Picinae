(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strsep
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strsep_amd64 : program := fun _ a => match a with

(* 0x00165be8: PUSH RBP *)
(*    1465320: PUSH RBP *)
| 0x165be8 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165be9: PUSH RBX *)
(*    1465321: PUSH RBX *)
| 0x165be9 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165bea: SUB RSP,0x8 *)
(*    1465322: SUB RSP,0x8 *)
| 0x165bea => Some (4,
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

(* 0x00165bee: MOV RBX,qword ptr [RDI] *)
(*    1465326: MOV RBX,qword ptr [RDI] *)
| 0x165bee => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move R_RBX (Var (V_TEMP 0x11f00))
)

(* 0x00165bf1: TEST RBX,RBX *)
(*    1465329: TEST RBX,RBX *)
| 0x165bf1 => Some (3,
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

(* 0x00165bf4: JZ 0x00165c16 *)
(*    1465332: JZ 0x00165c16 *)
| 0x165bf4 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165c16 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165bf6: MOV RBP,RDI *)
(*    1465334: MOV RBP,RDI *)
| 0x165bf6 => Some (3,
	Move R_RBP (Var R_RDI)
)

(* 0x00165bf9: MOV RDI,RBX *)
(*    1465337: MOV RDI,RBX *)
| 0x165bf9 => Some (3,
	Move R_RDI (Var R_RBX)
)

(* 0x00165bfc: CALL 0x00124240 *)
(*    1465340: CALL 0x00124240 *)
| 0x165bfc => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165c01 64)) LittleE 8) $;
	Jmp (Word 0x124240 64)
)

(* 0x00165c01: XOR EDX,EDX *)
(*    1465345: XOR EDX,EDX *)
| 0x165c01 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165c03: ADD RAX,RBX *)
(*    1465347: ADD RAX,RBX *)
| 0x165c03 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RBX)) (Var R_RAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RBX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RBX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165c06: CMP byte ptr [RAX],0x0 *)
(*    1465350: CMP byte ptr [RAX],0x0 *)
| 0x165c06 => Some (3,
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var R_RAX) LittleE 1) $;
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

(* 0x00165c09: JZ 0x00165c12 *)
(*    1465353: JZ 0x00165c12 *)
| 0x165c09 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x165c12 64)
	) (* else *) (
		Nop
	)
)

(* 0x00165c0b: MOV byte ptr [RAX],0x0 *)
(*    1465355: MOV byte ptr [RAX],0x0 *)
| 0x165c0b => Some (3,
	Move (V_TEMP 0x6900) (Word 0x0 8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x6900))) LittleE 1)
)

(* 0x00165c0e: LEA RDX,[RAX + 0x1] *)
(*    1465358: LEA RDX,[RAX + 0x1] *)
| 0x165c0e => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x00165c12: MOV qword ptr [RBP],RDX *)
(*    1465362: MOV qword ptr [RBP],RDX *)
| 0x165c12 => Some (4,
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RBP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00165c16: ADD RSP,0x8 *)
(*    1465366: ADD RSP,0x8 *)
| 0x165c16 => Some (4,
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

(* 0x00165c1a: MOV RAX,RBX *)
(*    1465370: MOV RAX,RBX *)
| 0x165c1a => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x00165c1d: POP RBX *)
(*    1465373: POP RBX *)
| 0x165c1d => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165c1e: POP RBP *)
(*    1465374: POP RBP *)
| 0x165c1e => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00165c1f: RET *)
(*    1465375: RET *)
| 0x165c1f => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strsep_amd64.
Proof. Picinae_typecheck. Qed.
