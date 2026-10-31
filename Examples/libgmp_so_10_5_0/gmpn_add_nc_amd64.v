(* Automatically generated with pcode2coq
arch: amd64
file: libgmp.so.10.5.0
SHA256: 2d6d19962673262eba388911974a90de5b7ac14d4da32a1c9666264a4e0a71e3
function: __gmpn_add_nc
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition libgmp_so_10_5_0___gmpn_add_nc_amd64 : program := fun _ a => match a with

(* 0x001284e0: MOV EAX,ECX *)
(*    1213664: MOV EAX,ECX *)
| 0x1284e0 => Some (2,
	(* (register, 0x0, 4) COPY (register, 0x8, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001284e2: SHR RCX,0x2 *)
(*    1213666: SHR RCX,0x2 *)
| 0x1284e2 => Some (4,
	(* (unique, 0x6e500, 4) INT_AND (const, 0x2, 4) , (const, 0x3f, 4) *)
	Move (V_TEMP 0x6e500) (BinOp OP_AND (Word 0x2 32) (Word 0x3f 32)) $;
	(* (unique, 0x6e580, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x6e580) (Var R_RCX) $;
	(* (register, 0x8, 8) INT_RIGHT (register, 0x8, 8) , (unique, 0x6e500, 4) *)
	Move R_RCX (BinOp OP_RSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e500)))) $;
	(* (unique, 0x2f680, 1) INT_NOTEQUAL (unique, 0x6e500, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
	(* (unique, 0x2f700, 4) INT_SUB (unique, 0x6e500, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	(* (unique, 0x2f780, 8) INT_RIGHT (unique, 0x6e580, 8) , (unique, 0x2f700, 4) *)
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e580)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f700)))) $;
	(* (unique, 0x2f800, 8) INT_AND (unique, 0x2f780, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 64)) $;
	(* (unique, 0x2f900, 1) INT_NOTEQUAL (unique, 0x2f800, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 64)) $;
	(* (unique, 0x2f980, 1) BOOL_NEGATE (unique, 0x2f680, 1) *)
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	(* (unique, 0x2fa00, 1) INT_AND (unique, 0x2f980, 1) , (register, 0x200, 1) *)
	Move (V_TEMP 0x2fa00) (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF)) $;
	(* (unique, 0x2fa80, 1) INT_AND (unique, 0x2f680, 1) , (unique, 0x2f900, 1) *)
	Move (V_TEMP 0x2fa80) (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900))) $;
	(* (register, 0x200, 1) INT_OR (unique, 0x2fa00, 1) , (unique, 0x2fa80, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fa00)) (Var (V_TEMP 0x2fa80)))) $;
	(* (unique, 0x2fc00, 1) INT_EQUAL (unique, 0x6e500, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	(* (unique, 0x2fd00, 1) INT_SLESS (unique, 0x6e580, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e580)) (Word 0x0 64)) $;
	(* (unique, 0x2fd80, 1) BOOL_NEGATE (unique, 0x2fc00, 1) *)
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	(* (unique, 0x2fe00, 1) INT_AND (unique, 0x2fd80, 1) , (register, 0x20b, 1) *)
	Move (V_TEMP 0x2fe00) (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF)) $;
	(* (unique, 0x2fe80, 1) INT_AND (unique, 0x2fc00, 1) , (unique, 0x2fd00, 1) *)
	Move (V_TEMP 0x2fe80) (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00))) $;
	(* (register, 0x20b, 1) INT_OR (unique, 0x2fe00, 1) , (unique, 0x2fe80, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fe00)) (Var (V_TEMP 0x2fe80)))) $;
	(* (unique, 0x2c400, 1) INT_NOTEQUAL (unique, 0x6e500, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
	(* (unique, 0x2c500, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)) $;
	(* (unique, 0x2c580, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2c600, 1) INT_AND (unique, 0x2c580, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x2c600) (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF)) $;
	(* (unique, 0x2c680, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2c500, 1) *)
	Move (V_TEMP 0x2c680) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500))) $;
	(* (register, 0x207, 1) INT_OR (unique, 0x2c600, 1) , (unique, 0x2c680, 1) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c600)) (Var (V_TEMP 0x2c680)))) $;
	(* (unique, 0x2c800, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(* (unique, 0x2c880, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2c900, 1) INT_AND (unique, 0x2c880, 1) , (register, 0x206, 1) *)
	Move (V_TEMP 0x2c900) (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF)) $;
	(* (unique, 0x2c980, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2c800, 1) *)
	Move (V_TEMP 0x2c980) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800))) $;
	(* (register, 0x206, 1) INT_OR (unique, 0x2c900, 1) , (unique, 0x2c980, 1) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c900)) (Var (V_TEMP 0x2c980)))) $;
	(* (unique, 0x2ca80, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2cb00, 1) POPCOUNT (unique, 0x2ca80, 8) *)
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	(* (unique, 0x2cb80, 1) INT_AND (unique, 0x2cb00, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	(* (unique, 0x2cc80, 1) INT_EQUAL (unique, 0x2cb80, 1) , (const, 0x0, 1) *)
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	(* (unique, 0x2cd00, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2cd80, 1) INT_AND (unique, 0x2cd00, 1) , (register, 0x202, 1) *)
	Move (V_TEMP 0x2cd80) (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF)) $;
	(* (unique, 0x2ce00, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2cc80, 1) *)
	Move (V_TEMP 0x2ce00) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80))) $;
	(* (register, 0x202, 1) INT_OR (unique, 0x2cd80, 1) , (unique, 0x2ce00, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2cd80)) (Var (V_TEMP 0x2ce00))))
)

(* 0x001284e6: AND EAX,0x3 *)
(*    1213670: AND EAX,0x3 *)
| 0x1284e6 => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x0, 4) INT_AND (register, 0x0, 4) , (const, 0x3, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x3 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001284e9: BT R8,0x0 *)
(*    1213673: BT R8,0x0 *)
| 0x1284e9 => Some (5,
	(* (unique, 0x37a00, 4) INT_AND (const, 0x0, 4) , (const, 0x3f, 4) *)
	Move (V_TEMP 0x37a00) (BinOp OP_AND (Word 0x0 32) (Word 0x3f 32)) $;
	(* (unique, 0x37a80, 8) INT_RIGHT (register, 0x80, 8) , (unique, 0x37a00, 4) *)
	Move (V_TEMP 0x37a80) (BinOp OP_RSHIFT (Var R_R8) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x37a00)))) $;
	(* (unique, 0x37b00, 8) INT_AND (unique, 0x37a80, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x37b00) (BinOp OP_AND (Var (V_TEMP 0x37a80)) (Word 0x1 64)) $;
	(* (register, 0x200, 1) INT_NOTEQUAL (unique, 0x37b00, 8) , (const, 0x0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x37b00)) (Word 0x0 64)))
)

(* 0x001284ee: JRCXZ 0x00128517 *)
(*    1213678: JRCXZ 0x00128517 *)
| 0x1284ee => Some (2,
	(* (unique, 0x4e880, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x4e880) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(*  ---  CBRANCH (ram, 0x128517, 8) , (unique, 0x4e880, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x4e880))) (
		Jmp (Word 0x128517 64)
	) (* else *) (
		Nop
	)
)

(* 0x001284f0: MOV R8,qword ptr [RSI] *)
(*    1213680: MOV R8,qword ptr [RSI] *)
| 0x1284f0 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x001284f3: MOV R9,qword ptr [RSI + 0x8] *)
(*    1213683: MOV R9,qword ptr [RSI + 0x8] *)
| 0x1284f3 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x001284f7: DEC RCX *)
(*    1213687: DEC RCX *)
| 0x1284f7 => Some (3,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x8, 8) INT_SUB (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001284fa: JMP 0x00128594 *)
(*    1213690: JMP 0x00128594 *)
| 0x1284fa => Some (5,
	(*  ---  BRANCH (ram, 0x128594, 8) *)
	Jmp (Word 0x128594 64)
)

(* 0x00128500: MOV EAX,ECX *)
(*    1213696: MOV EAX,ECX *)
| 0x128500 => Some (2,
	(* (register, 0x0, 4) COPY (register, 0x8, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00128502: SHR RCX,0x2 *)
(*    1213698: SHR RCX,0x2 *)
| 0x128502 => Some (4,
	(* (unique, 0x6e500, 4) INT_AND (const, 0x2, 4) , (const, 0x3f, 4) *)
	Move (V_TEMP 0x6e500) (BinOp OP_AND (Word 0x2 32) (Word 0x3f 32)) $;
	(* (unique, 0x6e580, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x6e580) (Var R_RCX) $;
	(* (register, 0x8, 8) INT_RIGHT (register, 0x8, 8) , (unique, 0x6e500, 4) *)
	Move R_RCX (BinOp OP_RSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e500)))) $;
	(* (unique, 0x2f680, 1) INT_NOTEQUAL (unique, 0x6e500, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
	(* (unique, 0x2f700, 4) INT_SUB (unique, 0x6e500, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	(* (unique, 0x2f780, 8) INT_RIGHT (unique, 0x6e580, 8) , (unique, 0x2f700, 4) *)
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e580)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f700)))) $;
	(* (unique, 0x2f800, 8) INT_AND (unique, 0x2f780, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 64)) $;
	(* (unique, 0x2f900, 1) INT_NOTEQUAL (unique, 0x2f800, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 64)) $;
	(* (unique, 0x2f980, 1) BOOL_NEGATE (unique, 0x2f680, 1) *)
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	(* (unique, 0x2fa00, 1) INT_AND (unique, 0x2f980, 1) , (register, 0x200, 1) *)
	Move (V_TEMP 0x2fa00) (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF)) $;
	(* (unique, 0x2fa80, 1) INT_AND (unique, 0x2f680, 1) , (unique, 0x2f900, 1) *)
	Move (V_TEMP 0x2fa80) (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900))) $;
	(* (register, 0x200, 1) INT_OR (unique, 0x2fa00, 1) , (unique, 0x2fa80, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fa00)) (Var (V_TEMP 0x2fa80)))) $;
	(* (unique, 0x2fc00, 1) INT_EQUAL (unique, 0x6e500, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	(* (unique, 0x2fd00, 1) INT_SLESS (unique, 0x6e580, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e580)) (Word 0x0 64)) $;
	(* (unique, 0x2fd80, 1) BOOL_NEGATE (unique, 0x2fc00, 1) *)
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	(* (unique, 0x2fe00, 1) INT_AND (unique, 0x2fd80, 1) , (register, 0x20b, 1) *)
	Move (V_TEMP 0x2fe00) (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF)) $;
	(* (unique, 0x2fe80, 1) INT_AND (unique, 0x2fc00, 1) , (unique, 0x2fd00, 1) *)
	Move (V_TEMP 0x2fe80) (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00))) $;
	(* (register, 0x20b, 1) INT_OR (unique, 0x2fe00, 1) , (unique, 0x2fe80, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fe00)) (Var (V_TEMP 0x2fe80)))) $;
	(* (unique, 0x2c400, 1) INT_NOTEQUAL (unique, 0x6e500, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
	(* (unique, 0x2c500, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)) $;
	(* (unique, 0x2c580, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2c600, 1) INT_AND (unique, 0x2c580, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x2c600) (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF)) $;
	(* (unique, 0x2c680, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2c500, 1) *)
	Move (V_TEMP 0x2c680) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500))) $;
	(* (register, 0x207, 1) INT_OR (unique, 0x2c600, 1) , (unique, 0x2c680, 1) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c600)) (Var (V_TEMP 0x2c680)))) $;
	(* (unique, 0x2c800, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(* (unique, 0x2c880, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2c900, 1) INT_AND (unique, 0x2c880, 1) , (register, 0x206, 1) *)
	Move (V_TEMP 0x2c900) (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF)) $;
	(* (unique, 0x2c980, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2c800, 1) *)
	Move (V_TEMP 0x2c980) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800))) $;
	(* (register, 0x206, 1) INT_OR (unique, 0x2c900, 1) , (unique, 0x2c980, 1) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c900)) (Var (V_TEMP 0x2c980)))) $;
	(* (unique, 0x2ca80, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2cb00, 1) POPCOUNT (unique, 0x2ca80, 8) *)
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	(* (unique, 0x2cb80, 1) INT_AND (unique, 0x2cb00, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	(* (unique, 0x2cc80, 1) INT_EQUAL (unique, 0x2cb80, 1) , (const, 0x0, 1) *)
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	(* (unique, 0x2cd00, 1) BOOL_NEGATE (unique, 0x2c400, 1) *)
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	(* (unique, 0x2cd80, 1) INT_AND (unique, 0x2cd00, 1) , (register, 0x202, 1) *)
	Move (V_TEMP 0x2cd80) (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF)) $;
	(* (unique, 0x2ce00, 1) INT_AND (unique, 0x2c400, 1) , (unique, 0x2cc80, 1) *)
	Move (V_TEMP 0x2ce00) (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80))) $;
	(* (register, 0x202, 1) INT_OR (unique, 0x2cd80, 1) , (unique, 0x2ce00, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2cd80)) (Var (V_TEMP 0x2ce00))))
)

(* 0x00128506: AND EAX,0x3 *)
(*    1213702: AND EAX,0x3 *)
| 0x128506 => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x0, 4) INT_AND (register, 0x0, 4) , (const, 0x3, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x3 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128509: JRCXZ 0x00128517 *)
(*    1213705: JRCXZ 0x00128517 *)
| 0x128509 => Some (2,
	(* (unique, 0x4e880, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x4e880) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(*  ---  CBRANCH (ram, 0x128517, 8) , (unique, 0x4e880, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x4e880))) (
		Jmp (Word 0x128517 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012850b: MOV R8,qword ptr [RSI] *)
(*    1213707: MOV R8,qword ptr [RSI] *)
| 0x12850b => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0012850e: MOV R9,qword ptr [RSI + 0x8] *)
(*    1213710: MOV R9,qword ptr [RSI + 0x8] *)
| 0x12850e => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x00128512: DEC RCX *)
(*    1213714: DEC RCX *)
| 0x128512 => Some (3,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x8, 8) INT_SUB (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128515: JMP 0x00128594 *)
(*    1213717: JMP 0x00128594 *)
| 0x128515 => Some (2,
	(*  ---  BRANCH (ram, 0x128594, 8) *)
	Jmp (Word 0x128594 64)
)

(* 0x00128517: DEC EAX *)
(*    1213719: DEC EAX *)
| 0x128517 => Some (2,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (register, 0x0, 4) INT_SUB (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128519: MOV R8,qword ptr [RSI] *)
(*    1213721: MOV R8,qword ptr [RSI] *)
| 0x128519 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0012851c: JNZ 0x00128527 *)
(*    1213724: JNZ 0x00128527 *)
| 0x12851c => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128527, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128527 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012851e: ADC R8,qword ptr [RDX] *)
(*    1213726: ADC R8,qword ptr [RDX] *)
| 0x12851e => Some (3,
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Var R_R8))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x80, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R8 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x80, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128521: MOV qword ptr [RDI],R8 *)
(*    1213729: MOV qword ptr [RDI],R8 *)
| 0x128521 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128524: ADC EAX,EAX *)
(*    1213732: ADC EAX,EAX *)
| 0x128524 => Some (2,
	(* (unique, 0x2b600, 4) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Extract 31 0 (Var R_RAX)))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (unique, 0x2b800, 4) INT_ADD (register, 0x0, 4) , (register, 0x0, 4) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x0, 4) INT_ADD (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600)))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128526: RET *)
(*    1213734: RET *)
| 0x128526 => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x00128527: DEC EAX *)
(*    1213735: DEC EAX *)
| 0x128527 => Some (2,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (register, 0x0, 4) INT_SUB (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128529: MOV R9,qword ptr [RSI + 0x8] *)
(*    1213737: MOV R9,qword ptr [RSI + 0x8] *)
| 0x128529 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x0012852d: JNZ 0x00128540 *)
(*    1213741: JNZ 0x00128540 *)
| 0x12852d => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128540, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128540 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012852f: ADC R8,qword ptr [RDX] *)
(*    1213743: ADC R8,qword ptr [RDX] *)
| 0x12852f => Some (3,
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Var R_R8))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x80, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R8 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x80, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128532: ADC R9,qword ptr [RDX + 0x8] *)
(*    1213746: ADC R9,qword ptr [RDX + 0x8] *)
| 0x128532 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Var R_R9))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x88, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R9 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R9) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R9) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x88, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R9) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128536: MOV qword ptr [RDI],R8 *)
(*    1213750: MOV qword ptr [RDI],R8 *)
| 0x128536 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128539: MOV qword ptr [RDI + 0x8],R9 *)
(*    1213753: MOV qword ptr [RDI + 0x8],R9 *)
| 0x128539 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012853d: ADC EAX,EAX *)
(*    1213757: ADC EAX,EAX *)
| 0x12853d => Some (2,
	(* (unique, 0x2b600, 4) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Extract 31 0 (Var R_RAX)))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (unique, 0x2b800, 4) INT_ADD (register, 0x0, 4) , (register, 0x0, 4) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x0, 4) INT_ADD (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600)))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0012853f: RET *)
(*    1213759: RET *)
| 0x12853f => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x00128540: MOV R10,qword ptr [RSI + 0x10] *)
(*    1213760: MOV R10,qword ptr [RSI + 0x10] *)
| 0x128540 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x90, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R10 (Var (V_TEMP 0x11f00))
)

(* 0x00128544: ADC R8,qword ptr [RDX] *)
(*    1213764: ADC R8,qword ptr [RDX] *)
| 0x128544 => Some (3,
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Var R_R8))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x80, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R8 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x80, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128547: ADC R9,qword ptr [RDX + 0x8] *)
(*    1213767: ADC R9,qword ptr [RDX + 0x8] *)
| 0x128547 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Var R_R9))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x88, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R9 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R9) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R9) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x88, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R9) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0012854b: ADC R10,qword ptr [RDX + 0x10] *)
(*    1213771: ADC R10,qword ptr [RDX + 0x10] *)
| 0x12854b => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Var R_R10))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x90, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R10 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x90, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0012854f: MOV qword ptr [RDI],R8 *)
(*    1213775: MOV qword ptr [RDI],R8 *)
| 0x12854f => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128552: MOV qword ptr [RDI + 0x8],R9 *)
(*    1213778: MOV qword ptr [RDI + 0x8],R9 *)
| 0x128552 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128556: MOV qword ptr [RDI + 0x10],R10 *)
(*    1213782: MOV qword ptr [RDI + 0x10],R10 *)
| 0x128556 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012855a: SETC AL *)
(*    1213786: SETC AL *)
| 0x12855a => Some (3,
	(* (register, 0x0, 1) COPY (register, 0x200, 1) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Var R_CF))
)

(* 0x0012855d: RET *)
(*    1213789: RET *)
| 0x12855d => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x00128560: ADC R8,qword ptr [RDX] *)
(*    1213792: ADC R8,qword ptr [RDX] *)
| 0x128560 => Some (3,
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Var R_R8))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x80, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R8 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x80, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128563: ADC R9,qword ptr [RDX + 0x8] *)
(*    1213795: ADC R9,qword ptr [RDX + 0x8] *)
| 0x128563 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Var R_R9))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x88, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R9 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R9) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R9) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x88, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R9) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128567: ADC R10,qword ptr [RDX + 0x10] *)
(*    1213799: ADC R10,qword ptr [RDX + 0x10] *)
| 0x128567 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Var R_R10))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x90, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R10 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x90, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0012856b: ADC R11,qword ptr [RDX + 0x18] *)
(*    1213803: ADC R11,qword ptr [RDX + 0x18] *)
| 0x12856b => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x18 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Var R_R11))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x98, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R11 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x98, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R11) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x98, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R11) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x98, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R11) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0012856f: MOV qword ptr [RDI],R8 *)
(*    1213807: MOV qword ptr [RDI],R8 *)
| 0x12856f => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128572: LEA RSI,[RSI + 0x20] *)
(*    1213810: LEA RSI,[RSI + 0x20] *)
| 0x128572 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x00128576: MOV qword ptr [RDI + 0x8],R9 *)
(*    1213814: MOV qword ptr [RDI + 0x8],R9 *)
| 0x128576 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012857a: MOV qword ptr [RDI + 0x10],R10 *)
(*    1213818: MOV qword ptr [RDI + 0x10],R10 *)
| 0x12857a => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012857e: DEC RCX *)
(*    1213822: DEC RCX *)
| 0x12857e => Some (3,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x8, 8) INT_SUB (register, 0x8, 8) , (const, 0x1, 8) *)
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00128581: MOV qword ptr [RDI + 0x18],R11 *)
(*    1213825: MOV qword ptr [RDI + 0x18],R11 *)
| 0x128581 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x18 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x98, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R11) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128585: LEA RDX,[RDX + 0x20] *)
(*    1213829: LEA RDX,[RDX + 0x20] *)
| 0x128585 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	(* (register, 0x10, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x00128589: MOV R8,qword ptr [RSI] *)
(*    1213833: MOV R8,qword ptr [RSI] *)
| 0x128589 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0012858c: MOV R9,qword ptr [RSI + 0x8] *)
(*    1213836: MOV R9,qword ptr [RSI + 0x8] *)
| 0x12858c => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x00128590: LEA RDI,[RDI + 0x20] *)
(*    1213840: LEA RDI,[RDI + 0x20] *)
| 0x128590 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x00128594: MOV R10,qword ptr [RSI + 0x10] *)
(*    1213844: MOV R10,qword ptr [RSI + 0x10] *)
| 0x128594 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x90, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R10 (Var (V_TEMP 0x11f00))
)

(* 0x00128598: MOV R11,qword ptr [RSI + 0x18] *)
(*    1213848: MOV R11,qword ptr [RSI + 0x18] *)
| 0x128598 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x18 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x98, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R11 (Var (V_TEMP 0x11f00))
)

(* 0x0012859c: JNZ 0x00128560 *)
(*    1213852: JNZ 0x00128560 *)
| 0x12859c => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128560, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128560 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012859e: LEA RSI,[RSI + 0x20] *)
(*    1213854: LEA RSI,[RSI + 0x20] *)
| 0x12859e => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x001285a2: ADC R8,qword ptr [RDX] *)
(*    1213858: ADC R8,qword ptr [RDX] *)
| 0x1285a2 => Some (3,
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Var R_R8))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x80, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R8 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x80, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x80, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285a5: ADC R9,qword ptr [RDX + 0x8] *)
(*    1213861: ADC R9,qword ptr [RDX + 0x8] *)
| 0x1285a5 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Var R_R9))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x88, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R9 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R9) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x88, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R9) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x88, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R9) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285a9: ADC R10,qword ptr [RDX + 0x10] *)
(*    1213865: ADC R10,qword ptr [RDX + 0x10] *)
| 0x1285a9 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Var R_R10))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x90, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R10 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x90, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x90, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285ad: ADC R11,qword ptr [RDX + 0x18] *)
(*    1213869: ADC R11,qword ptr [RDX + 0x18] *)
| 0x1285ad => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x18 64)) $;
	(* (unique, 0x2b600, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Var R_R11))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2b800, 8) INT_ADD (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Var R_R11) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x98, 8) INT_ADD (unique, 0x2b800, 8) , (unique, 0x2b600, 8) *)
	Move R_R11 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x98, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R11) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x98, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R11) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x98, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R11) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285b1: LEA RDX,[RDX + 0x20] *)
(*    1213873: LEA RDX,[RDX + 0x20] *)
| 0x1285b1 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	(* (register, 0x10, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x001285b5: MOV qword ptr [RDI],R8 *)
(*    1213877: MOV qword ptr [RDI],R8 *)
| 0x1285b5 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001285b8: MOV qword ptr [RDI + 0x8],R9 *)
(*    1213880: MOV qword ptr [RDI + 0x8],R9 *)
| 0x1285b8 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001285bc: MOV qword ptr [RDI + 0x10],R10 *)
(*    1213884: MOV qword ptr [RDI + 0x10],R10 *)
| 0x1285bc => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001285c0: MOV qword ptr [RDI + 0x18],R11 *)
(*    1213888: MOV qword ptr [RDI + 0x18],R11 *)
| 0x1285c0 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x18 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x98, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R11) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001285c4: LEA RDI,[RDI + 0x20] *)
(*    1213892: LEA RDI,[RDI + 0x20] *)
| 0x1285c4 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x001285c8: INC EAX *)
(*    1213896: INC EAX *)
| 0x1285c8 => Some (2,
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (register, 0x0, 4) INT_ADD (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285ca: DEC EAX *)
(*    1213898: DEC EAX *)
| 0x1285ca => Some (2,
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (register, 0x0, 4) INT_SUB (register, 0x0, 4) , (const, 0x1, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285cc: JNZ 0x00128517 *)
(*    1213900: JNZ 0x00128517 *)
| 0x1285cc => Some (6,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128517, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128517 64)
	) (* else *) (
		Nop
	)
)

(* 0x001285d2: ADC EAX,EAX *)
(*    1213906: ADC EAX,EAX *)
| 0x1285d2 => Some (2,
	(* (unique, 0x2b600, 4) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2b600) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	(* (register, 0x200, 1) INT_CARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Extract 31 0 (Var R_RAX)))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	(* (unique, 0x2b800, 4) INT_ADD (register, 0x0, 4) , (register, 0x0, 4) *)
	Move (V_TEMP 0x2b800) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	(* (unique, 0x2b880, 1) INT_CARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Var (V_TEMP 0x2b800)))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2b880, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b880))))) $;
	(* (unique, 0x2b980, 1) INT_SCARRY (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move (V_TEMP 0x2b980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b800)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2b600)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2b980, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2b980))))) $;
	(* (register, 0x0, 4) INT_ADD (unique, 0x2b800, 4) , (unique, 0x2b600, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_PLUS (Var (V_TEMP 0x2b800)) (Var (V_TEMP 0x2b600)))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001285d4: RET *)
(*    1213908: RET *)
| 0x1285d4 => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx libgmp_so_10_5_0___gmpn_add_nc_amd64.
Proof. Picinae_typecheck. Qed.


(* BEGIN BIGSTEPS GENERATED LEMMAS *)
(* Generated by: bigsteps /home/ixb/research/picinae-llm/Examples/libgmp_so_10_5_0/gmpn_add_nc_amd64.v --backend compiler --timeout 600 --invariants 0x1284e0 0x128500 0x128517 0x12851e 0x128521 0x128524 0x128527 0x12852f 0x128532 0x128536 0x12853d 0x128540 0x128544 0x128547 0x12854b 0x12854f 0x12855a 0x128560 0x128563 0x128567 0x12856b 0x12856f 0x128594 0x12859e 0x1285a2 0x1285a5 0x1285a9 0x1285ad 0x1285b1 0x1285ca 0x1285d2 0x128526 0x12853f 0x12855d 0x1285d4 --exits 0x128526 0x12853f 0x12855d 0x1285d4 --ignore R_OF R_SF R_PF R_AF *)
Import X64Notations.
Local Ltac ignore_vars v ::= constr:(match v with R_OF | R_SF | R_PF | R_AF => true | _ => false end).

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213664:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284e0, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284e2, s[R_RAX := s R_RCX mod 2 ^ 32]) :: l) = None))
    (VC3: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284e6, s[R_RAX := s R_RCX mod 2 ^ 32][R_RCX := s R_RCX >> 2][R_CF := ((if negb (2 .& 63 =? 0) then 0 else s R_CF) .| (if negb (s R_RCX >> msub 32 (2 .& 63) 1 .& 1 =? 0) then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_OF := n1][R_SF := n0][R_ZF := ((if negb (2 .& 63 =? 0) then 0 else s R_ZF) .| (if s R_RCX >> 2 =? 0 then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_PF := n]) :: l) = None))
    (VC4: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284e9, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC5: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284ee, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l) = None))
    (VC6: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128517, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l)))
    (VC7: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284f0, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l) = None))
    (VC8: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284f3, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC9: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284f7, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC10: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001284fa, s[R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC11: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128594, s[R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213664, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
  1: solve [eapply VC9; first [eassumption | reflexivity]].
  1: solve [eapply VC10; first [eassumption | reflexivity]].
  1: solve [eapply VC11; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213696:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128500, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128502, s[R_RAX := s R_RCX mod 2 ^ 32]) :: l) = None))
    (VC3: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128506, s[R_RAX := s R_RCX mod 2 ^ 32][R_RCX := s R_RCX >> 2][R_CF := ((if negb (2 .& 63 =? 0) then 0 else s R_CF) .| (if negb (s R_RCX >> msub 32 (2 .& 63) 1 .& 1 =? 0) then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_OF := n1][R_SF := n0][R_ZF := ((if negb (2 .& 63 =? 0) then 0 else s R_ZF) .| (if s R_RCX >> 2 =? 0 then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_PF := n]) :: l) = None))
    (VC4: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128509, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC5: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128517, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l)))
    (VC6: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012850b, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC7: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012850e, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC8: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128512, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC9: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128515, s[R_CF := 0][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC10: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128594, s[R_CF := 0][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213696, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
  1: solve [eapply VC9; first [eassumption | reflexivity]].
  1: solve [eapply VC10; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213719:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128517, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128519, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012851c, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC4: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012851e, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l)))
    (VC5: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128527, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213719, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213726:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012851e, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128521, s[R_CF := (if s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_R8 then 1 else 0) .| (if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF <? s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0)][R_OF := n1][R_R8 := s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213726, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213729:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128521, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128524, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213729, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213732:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128524, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128526, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213732, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213735:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128527, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128529, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012852d, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC4: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012852f, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l)))
    (VC5: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128540, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213735, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213743:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012852f, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128532, s[R_CF := (if s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_R8 then 1 else 0) .| (if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF <? s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0)][R_OF := n1][R_R8 := s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213743, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213746:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128532, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128536, s[R_CF := (if s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_R9 then 1 else 0) .| (if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF <? s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R9 := s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213746, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213750:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128536, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128539, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012853d, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213750, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213757:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012853d, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012853f, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213757, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213760:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128540, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128544, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213760, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213764:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128544, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128547, s[R_CF := (if s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_R8 then 1 else 0) .| (if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF <? s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0)][R_OF := n1][R_R8 := s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213764, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213767:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128547, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012854b, s[R_CF := (if s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_R9 then 1 else 0) .| (if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF <? s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R9 := s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213767, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213771:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012854b, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012854f, s[R_CF := (if s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_R10 then 1 else 0) .| (if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF <? s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R10 := s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213771, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213775:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012854f, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128552, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128556, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012855a, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213775, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213786:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012855a, s) :: t) = None))
    (VC2: (forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012855d, s[R_RAX := s R_CF]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213786, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213792:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128560, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128563, s[R_CF := (if s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_R8 then 1 else 0) .| (if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF <? s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0)][R_OF := n1][R_R8 := s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213792, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213795:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128563, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128567, s[R_CF := (if s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_R9 then 1 else 0) .| (if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF <? s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R9 := s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213795, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213799:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128567, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012856b, s[R_CF := (if s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_R10 then 1 else 0) .| (if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF <? s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R10 := s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213799, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213803:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012856b, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (24 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012856f, s[R_CF := (if s R_R11 ⊕ s V_MEM64 Ⓠ[ 24 + s R_RDX ] <? s R_R11 then 1 else 0) .| (if s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF <? s R_R11 ⊕ s V_MEM64 Ⓠ[ 24 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R11 := s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213803, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213807:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012856f, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128572, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128576, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]][R_RSI := 32 ⊕ s R_RSI]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012857a, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC5: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012857e, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l) = None))
    (VC6: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128581, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC7: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128585, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]]) :: l) = None))
    (VC8: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128589, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX]) :: l) = None))
    (VC9: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012858c, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]]) :: l) = None))
    (VC10: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (40 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128590, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]][R_R9 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 40 + s R_RSI ]]) :: l) = None))
    (VC11: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (40 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128594, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]][R_R9 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 40 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213807, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
  1: solve [eapply VC9; first [eassumption | reflexivity]].
  1: solve [eapply VC10; first [eassumption | reflexivity]].
  1: solve [eapply VC11; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213844:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128594, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x00128598, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012859c, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> N.lnot (s R_ZF) 1 mod 2 = 0 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x0012859e, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l)))
    (VC5: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall p : positive, N.lnot (s R_ZF) 1 mod 2 = N.pos p -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128560, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213844, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213854:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x0012859e, s) :: t) = None))
    (VC2: (forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285a2, s[R_RSI := 32 ⊕ s R_RSI]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213854, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213858:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285a2, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285a5, s[R_CF := (if s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_R8 then 1 else 0) .| (if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF <? s R_R8 ⊕ s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0)][R_OF := n1][R_R8 := s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R8 + s V_MEM64 Ⓠ[ s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213858, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213861:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285a5, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285a9, s[R_CF := (if s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_R9 then 1 else 0) .| (if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF <? s R_R9 ⊕ s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R9 := s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R9 + s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213861, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213865:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285a9, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285ad, s[R_CF := (if s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_R10 then 1 else 0) .| (if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF <? s R_R10 ⊕ s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R10 := s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R10 + s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213865, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213869:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285ad, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (24 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285b1, s[R_CF := (if s R_R11 ⊕ s V_MEM64 Ⓠ[ 24 + s R_RDX ] <? s R_R11 then 1 else 0) .| (if s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF <? s R_R11 ⊕ s V_MEM64 Ⓠ[ 24 + s R_RDX ] then 1 else 0)][R_OF := n1][R_R11 := s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF][R_SF := n0][R_ZF := if s R_R11 + s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊕ s R_CF =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213869, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213873:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285b1, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285b5, s[R_RDX := 32 ⊕ s R_RDX]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285b8, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285bc, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC5: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285c0, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l) = None))
    (VC6: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285c4, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]]) :: l) = None))
    (VC7: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285c8, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDI := 32 ⊕ s R_RDI]) :: l) = None))
    (VC8: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285ca, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDI := 32 ⊕ s R_RDI][R_OF := n1][R_RAX := scast 32 64 (((s R_RAX >> 0) mod 2 ^ 32 + 1) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (((s R_RAX >> 0) mod 2 ^ 32 + 1) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213873, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213898:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285ca, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285cc, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285d2, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n]) :: l)))
    (VC4: (forall n n0 n1 : N, (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x00128517, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213898, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213906:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits ((Addr 0x001285d2, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits true ((Addr 0x001285d4, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_nc_amd64 invs exits false ((Addr 1213906, s)::t).
Proof.
  intros; find_vcs (1213664::1213696::1213719::1213726::1213729::1213732::1213735::1213743::1213746::1213750::1213757::1213760::1213764::1213767::1213771::1213775::1213786::1213792::1213795::1213799::1213803::1213807::1213844::1213854::1213858::1213861::1213865::1213869::1213873::1213898::1213906::1213734::1213759::1213789::1213908::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Ltac libgmp_so_10_5_0___gmpn_add_nc_amd64_bigstep := first [ apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213664 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213696 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213719 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213726 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213729 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213732 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213735 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213743 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213746 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213750 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213757 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213760 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213764 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213767 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213771 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213775 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213786 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213792 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213795 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213799 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213803 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213807 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213844 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213854 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213858 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213861 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213865 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213869 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213873 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213898 | apply libgmp_so_10_5_0___gmpn_add_nc_amd64_stepfrom_1213906 ]; intros; (reflexivity || ISA_invhere).
(* END BIGSTEPS GENERATED LEMMAS *)