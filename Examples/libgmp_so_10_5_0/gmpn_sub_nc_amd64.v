(* Automatically generated with pcode2coq
arch: amd64
file: libgmp.so.10.5.0
SHA256: 2d6d19962673262eba388911974a90de5b7ac14d4da32a1c9666264a4e0a71e3
function: __gmpn_sub_nc
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition libgmp_so_10_5_0___gmpn_sub_nc_amd64 : program := fun _ a => match a with

(* 0x00128740: MOV EAX,ECX *)
(*    1214272: MOV EAX,ECX *)
| 0x128740 => Some (2,
	(* (register, 0x0, 4) COPY (register, 0x8, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00128742: SHR RCX,0x2 *)
(*    1214274: SHR RCX,0x2 *)
| 0x128742 => Some (4,
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

(* 0x00128746: AND EAX,0x3 *)
(*    1214278: AND EAX,0x3 *)
| 0x128746 => Some (3,
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

(* 0x00128749: BT R8,0x0 *)
(*    1214281: BT R8,0x0 *)
| 0x128749 => Some (5,
	(* (unique, 0x37a00, 4) INT_AND (const, 0x0, 4) , (const, 0x3f, 4) *)
	Move (V_TEMP 0x37a00) (BinOp OP_AND (Word 0x0 32) (Word 0x3f 32)) $;
	(* (unique, 0x37a80, 8) INT_RIGHT (register, 0x80, 8) , (unique, 0x37a00, 4) *)
	Move (V_TEMP 0x37a80) (BinOp OP_RSHIFT (Var R_R8) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x37a00)))) $;
	(* (unique, 0x37b00, 8) INT_AND (unique, 0x37a80, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x37b00) (BinOp OP_AND (Var (V_TEMP 0x37a80)) (Word 0x1 64)) $;
	(* (register, 0x200, 1) INT_NOTEQUAL (unique, 0x37b00, 8) , (const, 0x0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x37b00)) (Word 0x0 64)))
)

(* 0x0012874e: JRCXZ 0x00128777 *)
(*    1214286: JRCXZ 0x00128777 *)
| 0x12874e => Some (2,
	(* (unique, 0x4e880, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x4e880) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(*  ---  CBRANCH (ram, 0x128777, 8) , (unique, 0x4e880, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x4e880))) (
		Jmp (Word 0x128777 64)
	) (* else *) (
		Nop
	)
)

(* 0x00128750: MOV R8,qword ptr [RSI] *)
(*    1214288: MOV R8,qword ptr [RSI] *)
| 0x128750 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x00128753: MOV R9,qword ptr [RSI + 0x8] *)
(*    1214291: MOV R9,qword ptr [RSI + 0x8] *)
| 0x128753 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x00128757: DEC RCX *)
(*    1214295: DEC RCX *)
| 0x128757 => Some (3,
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

(* 0x0012875a: JMP 0x001287f4 *)
(*    1214298: JMP 0x001287f4 *)
| 0x12875a => Some (5,
	(*  ---  BRANCH (ram, 0x1287f4, 8) *)
	Jmp (Word 0x1287f4 64)
)

(* 0x00128760: MOV EAX,ECX *)
(*    1214304: MOV EAX,ECX *)
| 0x128760 => Some (2,
	(* (register, 0x0, 4) COPY (register, 0x8, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00128762: SHR RCX,0x2 *)
(*    1214306: SHR RCX,0x2 *)
| 0x128762 => Some (4,
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

(* 0x00128766: AND EAX,0x3 *)
(*    1214310: AND EAX,0x3 *)
| 0x128766 => Some (3,
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

(* 0x00128769: JRCXZ 0x00128777 *)
(*    1214313: JRCXZ 0x00128777 *)
| 0x128769 => Some (2,
	(* (unique, 0x4e880, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x4e880) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	(*  ---  CBRANCH (ram, 0x128777, 8) , (unique, 0x4e880, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x4e880))) (
		Jmp (Word 0x128777 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012876b: MOV R8,qword ptr [RSI] *)
(*    1214315: MOV R8,qword ptr [RSI] *)
| 0x12876b => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0012876e: MOV R9,qword ptr [RSI + 0x8] *)
(*    1214318: MOV R9,qword ptr [RSI + 0x8] *)
| 0x12876e => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x00128772: DEC RCX *)
(*    1214322: DEC RCX *)
| 0x128772 => Some (3,
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

(* 0x00128775: JMP 0x001287f4 *)
(*    1214325: JMP 0x001287f4 *)
| 0x128775 => Some (2,
	(*  ---  BRANCH (ram, 0x1287f4, 8) *)
	Jmp (Word 0x1287f4 64)
)

(* 0x00128777: DEC EAX *)
(*    1214327: DEC EAX *)
| 0x128777 => Some (2,
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

(* 0x00128779: MOV R8,qword ptr [RSI] *)
(*    1214329: MOV R8,qword ptr [RSI] *)
| 0x128779 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0012877c: JNZ 0x00128787 *)
(*    1214332: JNZ 0x00128787 *)
| 0x12877c => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128787, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128787 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012877e: SBB R8,qword ptr [RDX] *)
(*    1214334: SBB R8,qword ptr [RDX] *)
| 0x12877e => Some (3,
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R8) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x80, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R8 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128781: MOV qword ptr [RDI],R8 *)
(*    1214337: MOV qword ptr [RDI],R8 *)
| 0x128781 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128784: ADC EAX,EAX *)
(*    1214340: ADC EAX,EAX *)
| 0x128784 => Some (2,
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

(* 0x00128786: RET *)
(*    1214342: RET *)
| 0x128786 => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x00128787: DEC EAX *)
(*    1214343: DEC EAX *)
| 0x128787 => Some (2,
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

(* 0x00128789: MOV R9,qword ptr [RSI + 0x8] *)
(*    1214345: MOV R9,qword ptr [RSI + 0x8] *)
| 0x128789 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x0012878d: JNZ 0x001287a0 *)
(*    1214349: JNZ 0x001287a0 *)
| 0x12878d => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x1287a0, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1287a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0012878f: SBB R8,qword ptr [RDX] *)
(*    1214351: SBB R8,qword ptr [RDX] *)
| 0x12878f => Some (3,
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R8) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x80, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R8 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128792: SBB R9,qword ptr [RDX + 0x8] *)
(*    1214354: SBB R9,qword ptr [RDX + 0x8] *)
| 0x128792 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R9) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x88, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R9 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128796: MOV qword ptr [RDI],R8 *)
(*    1214358: MOV qword ptr [RDI],R8 *)
| 0x128796 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128799: MOV qword ptr [RDI + 0x8],R9 *)
(*    1214361: MOV qword ptr [RDI + 0x8],R9 *)
| 0x128799 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012879d: ADC EAX,EAX *)
(*    1214365: ADC EAX,EAX *)
| 0x12879d => Some (2,
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

(* 0x0012879f: RET *)
(*    1214367: RET *)
| 0x12879f => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x001287a0: MOV R10,qword ptr [RSI + 0x10] *)
(*    1214368: MOV R10,qword ptr [RSI + 0x10] *)
| 0x1287a0 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x90, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R10 (Var (V_TEMP 0x11f00))
)

(* 0x001287a4: SBB R8,qword ptr [RDX] *)
(*    1214372: SBB R8,qword ptr [RDX] *)
| 0x1287a4 => Some (3,
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R8) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x80, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R8 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287a7: SBB R9,qword ptr [RDX + 0x8] *)
(*    1214375: SBB R9,qword ptr [RDX + 0x8] *)
| 0x1287a7 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R9) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x88, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R9 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287ab: SBB R10,qword ptr [RDX + 0x10] *)
(*    1214379: SBB R10,qword ptr [RDX + 0x10] *)
| 0x1287ab => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R10) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x90, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R10 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287af: MOV qword ptr [RDI],R8 *)
(*    1214383: MOV qword ptr [RDI],R8 *)
| 0x1287af => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287b2: MOV qword ptr [RDI + 0x8],R9 *)
(*    1214386: MOV qword ptr [RDI + 0x8],R9 *)
| 0x1287b2 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287b6: MOV qword ptr [RDI + 0x10],R10 *)
(*    1214390: MOV qword ptr [RDI + 0x10],R10 *)
| 0x1287b6 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287ba: SETC AL *)
(*    1214394: SETC AL *)
| 0x1287ba => Some (3,
	(* (register, 0x0, 1) COPY (register, 0x200, 1) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Var R_CF))
)

(* 0x001287bd: RET *)
(*    1214397: RET *)
| 0x1287bd => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x001287c0: SBB R8,qword ptr [RDX] *)
(*    1214400: SBB R8,qword ptr [RDX] *)
| 0x1287c0 => Some (3,
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R8) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x80, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R8 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287c3: SBB R9,qword ptr [RDX + 0x8] *)
(*    1214403: SBB R9,qword ptr [RDX + 0x8] *)
| 0x1287c3 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R9) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x88, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R9 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287c7: SBB R10,qword ptr [RDX + 0x10] *)
(*    1214407: SBB R10,qword ptr [RDX + 0x10] *)
| 0x1287c7 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R10) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x90, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R10 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287cb: SBB R11,qword ptr [RDX + 0x18] *)
(*    1214411: SBB R11,qword ptr [RDX + 0x18] *)
| 0x1287cb => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x18 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R11) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x98, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R11 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x001287cf: MOV qword ptr [RDI],R8 *)
(*    1214415: MOV qword ptr [RDI],R8 *)
| 0x1287cf => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287d2: LEA RSI,[RSI + 0x20] *)
(*    1214418: LEA RSI,[RSI + 0x20] *)
| 0x1287d2 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x001287d6: MOV qword ptr [RDI + 0x8],R9 *)
(*    1214422: MOV qword ptr [RDI + 0x8],R9 *)
| 0x1287d6 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287da: MOV qword ptr [RDI + 0x10],R10 *)
(*    1214426: MOV qword ptr [RDI + 0x10],R10 *)
| 0x1287da => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287de: DEC RCX *)
(*    1214430: DEC RCX *)
| 0x1287de => Some (3,
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

(* 0x001287e1: MOV qword ptr [RDI + 0x18],R11 *)
(*    1214433: MOV qword ptr [RDI + 0x18],R11 *)
| 0x1287e1 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x18 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x98, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R11) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001287e5: LEA RDX,[RDX + 0x20] *)
(*    1214437: LEA RDX,[RDX + 0x20] *)
| 0x1287e5 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	(* (register, 0x10, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x001287e9: MOV R8,qword ptr [RSI] *)
(*    1214441: MOV R8,qword ptr [RSI] *)
| 0x1287e9 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x001287ec: MOV R9,qword ptr [RSI + 0x8] *)
(*    1214444: MOV R9,qword ptr [RSI + 0x8] *)
| 0x1287ec => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x001287f0: LEA RDI,[RDI + 0x20] *)
(*    1214448: LEA RDI,[RDI + 0x20] *)
| 0x1287f0 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x001287f4: MOV R10,qword ptr [RSI + 0x10] *)
(*    1214452: MOV R10,qword ptr [RSI + 0x10] *)
| 0x1287f4 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x90, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R10 (Var (V_TEMP 0x11f00))
)

(* 0x001287f8: MOV R11,qword ptr [RSI + 0x18] *)
(*    1214456: MOV R11,qword ptr [RSI + 0x18] *)
| 0x1287f8 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x18 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x98, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R11 (Var (V_TEMP 0x11f00))
)

(* 0x001287fc: JNZ 0x001287c0 *)
(*    1214460: JNZ 0x001287c0 *)
| 0x1287fc => Some (2,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x1287c0, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1287c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001287fe: LEA RSI,[RSI + 0x20] *)
(*    1214462: LEA RSI,[RSI + 0x20] *)
| 0x1287fe => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x00128802: SBB R8,qword ptr [RDX] *)
(*    1214466: SBB R8,qword ptr [RDX] *)
| 0x128802 => Some (3,
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R8) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x10, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x80, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R8) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x80, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R8 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128805: SBB R9,qword ptr [RDX + 0x8] *)
(*    1214469: SBB R9,qword ptr [RDX + 0x8] *)
| 0x128805 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R9) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x88, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R9) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x88, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R9 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128809: SBB R10,qword ptr [RDX + 0x10] *)
(*    1214473: SBB R10,qword ptr [RDX + 0x10] *)
| 0x128809 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R10) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x90, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x90, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R10 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x0012880d: SBB R11,qword ptr [RDX + 0x18] *)
(*    1214477: SBB R11,qword ptr [RDX + 0x18] *)
| 0x12880d => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x18 64)) $;
	(* (unique, 0x2bb80, 8) INT_ZEXT (register, 0x200, 1) *)
	Move (V_TEMP 0x2bb80) (Cast CAST_UNSIGNED 64 (Var R_CF)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x200, 1) INT_LESS (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R11) (Var (V_TEMP 0x11f00)))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R11) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f00)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (unique, 0x2bd80, 8) INT_SUB (register, 0x98, 8) , (unique, 0x11f00, 8) *)
	Move (V_TEMP 0x2bd80) (BinOp OP_MINUS (Var R_R11) (Var (V_TEMP 0x11f00))) $;
	(* (unique, 0x2be00, 1) INT_LESS (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2be00) (BinOp OP_LT (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
	(* (register, 0x200, 1) BOOL_OR (register, 0x200, 1) , (unique, 0x2be00, 1) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x2be00)))) $;
	(* (unique, 0x2bf00, 1) INT_SBORROW (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move (V_TEMP 0x2bf00) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bd80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x2bb80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (register, 0x20b, 1) BOOL_XOR (register, 0x20b, 1) , (unique, 0x2bf00, 1) *)
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x2bf00))))) $;
	(* (register, 0x98, 8) INT_SUB (unique, 0x2bd80, 8) , (unique, 0x2bb80, 8) *)
	Move R_R11 (BinOp OP_MINUS (Var (V_TEMP 0x2bd80)) (Var (V_TEMP 0x2bb80))) $;
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

(* 0x00128811: LEA RDX,[RDX + 0x20] *)
(*    1214481: LEA RDX,[RDX + 0x20] *)
| 0x128811 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x10, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	(* (register, 0x10, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x00128815: MOV qword ptr [RDI],R8 *)
(*    1214485: MOV qword ptr [RDI],R8 *)
| 0x128815 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x80, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128818: MOV qword ptr [RDI + 0x8],R9 *)
(*    1214488: MOV qword ptr [RDI + 0x8],R9 *)
| 0x128818 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0012881c: MOV qword ptr [RDI + 0x10],R10 *)
(*    1214492: MOV qword ptr [RDI + 0x10],R10 *)
| 0x12881c => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128820: MOV qword ptr [RDI + 0x18],R11 *)
(*    1214496: MOV qword ptr [RDI + 0x18],R11 *)
| 0x128820 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x18 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x98, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R11) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00128824: LEA RDI,[RDI + 0x20] *)
(*    1214500: LEA RDI,[RDI + 0x20] *)
| 0x128824 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x00128828: INC EAX *)
(*    1214504: INC EAX *)
| 0x128828 => Some (2,
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

(* 0x0012882a: DEC EAX *)
(*    1214506: DEC EAX *)
| 0x12882a => Some (2,
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

(* 0x0012882c: JNZ 0x00128777 *)
(*    1214508: JNZ 0x00128777 *)
| 0x12882c => Some (6,
	(* (unique, 0x12780, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	(*  ---  CBRANCH (ram, 0x128777, 8) , (unique, 0x12780, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x128777 64)
	) (* else *) (
		Nop
	)
)

(* 0x00128832: ADC EAX,EAX *)
(*    1214514: ADC EAX,EAX *)
| 0x128832 => Some (2,
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

(* 0x00128834: RET *)
(*    1214516: RET *)
| 0x128834 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx libgmp_so_10_5_0___gmpn_sub_nc_amd64.
Proof. Picinae_typecheck. Qed.


(* BEGIN BIGSTEPS GENERATED LEMMAS *)
(* Generated by: bigsteps /home/ixb/research/picinae-llm/Examples/libgmp_so_10_5_0/gmpn_sub_nc_amd64.v --backend compiler --timeout 600 --invariants 0x128740 0x128760 0x128777 0x12877e 0x128781 0x128784 0x128787 0x12878f 0x128792 0x128796 0x12879d 0x1287a0 0x1287a4 0x1287a7 0x1287ab 0x1287af 0x1287ba 0x1287c0 0x1287c3 0x1287c7 0x1287cb 0x1287cf 0x1287f4 0x1287fe 0x128802 0x128805 0x128809 0x12880d 0x128811 0x12882a 0x128832 0x128786 0x12879f 0x1287bd 0x128834 --exits 0x128786 0x12879f 0x1287bd 0x128834 --ignore R_OF R_SF R_PF R_AF *)
Import X64Notations.
Local Ltac ignore_vars v ::= constr:(match v with R_OF | R_SF | R_PF | R_AF => true | _ => false end).

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214272:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128740, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128742, s[R_RAX := s R_RCX mod 2 ^ 32]) :: l) = None))
    (VC3: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128746, s[R_RAX := s R_RCX mod 2 ^ 32][R_RCX := s R_RCX >> 2][R_CF := ((if negb (2 .& 63 =? 0) then 0 else s R_CF) .| (if negb (s R_RCX >> msub 32 (2 .& 63) 1 .& 1 =? 0) then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_OF := n1][R_SF := n0][R_ZF := ((if negb (2 .& 63 =? 0) then 0 else s R_ZF) .| (if s R_RCX >> 2 =? 0 then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_PF := n]) :: l) = None))
    (VC4: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128749, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC5: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012874e, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l) = None))
    (VC6: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128777, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l)))
    (VC7: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128750, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0]) :: l) = None))
    (VC8: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128753, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC9: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128757, s[R_RCX := s R_RCX >> 2][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC10: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012875a, s[R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC11: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287f4, s[R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_CF := if negb (s R_R8 >> (0 .& 63) .& 1 =? 0) then 1 else 0][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214272, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
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

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214304:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128760, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128762, s[R_RAX := s R_RCX mod 2 ^ 32]) :: l) = None))
    (VC3: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128766, s[R_RAX := s R_RCX mod 2 ^ 32][R_RCX := s R_RCX >> 2][R_CF := ((if negb (2 .& 63 =? 0) then 0 else s R_CF) .| (if negb (s R_RCX >> msub 32 (2 .& 63) 1 .& 1 =? 0) then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_OF := n1][R_SF := n0][R_ZF := ((if negb (2 .& 63 =? 0) then 0 else s R_ZF) .| (if s R_RCX >> 2 =? 0 then if negb (2 .& 63 =? 0) then 1 else 0 else 0)) mod 2][R_PF := n]) :: l) = None))
    (VC4: (forall (n2 n3 n4 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128769, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC5: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128777, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l)))
    (VC6: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012876b, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2]) :: l) = None))
    (VC7: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012876e, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC8: (forall n2 n3 n4 : N, (s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128772, s[R_RCX := s R_RCX >> 2][R_CF := 0][R_OF := n4][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_SF := n3][R_ZF := if scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n2][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC9: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128775, s[R_CF := 0][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC10: ((s R_RCX >> 2 =? 0) = false -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287f4, s[R_CF := 0][R_RAX := scast 32 64 ((s R_RCX mod 2 ^ 32 >> 0) mod 2 ^ 32 .& 3) mod 2 ^ 32][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_OF := n1][R_RCX := (s R_RCX >> 2) ⊖ 1][R_SF := n0][R_ZF := if (s R_RCX >> 2) mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214304, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
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

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214327:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128777, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128779, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012877c, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC4: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012877e, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l)))
    (VC5: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128787, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n][R_R8 := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214327, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214334:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012877e, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128781, s[R_CF := (if s R_R8 <? s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0) .| (if s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R8 := s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214334, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214337:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128781, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128784, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214337, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214340:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128784, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128786, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214340, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214343:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128787, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128789, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012878d, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC4: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012878f, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l)))
    (VC5: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287a0, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214343, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214351:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012878f, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128792, s[R_CF := (if s R_R8 <? s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0) .| (if s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R8 := s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214351, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214354:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128792, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128796, s[R_CF := (if s R_R9 <? s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0) .| (if s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R9 := s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214354, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214358:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128796, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128799, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012879d, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214358, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214365:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012879d, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012879f, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214365, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214368:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287a0, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287a4, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214368, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214372:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287a4, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287a7, s[R_CF := (if s R_R8 <? s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0) .| (if s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R8 := s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214372, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214375:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287a7, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287ab, s[R_CF := (if s R_R9 <? s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0) .| (if s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R9 := s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214375, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214379:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287ab, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287af, s[R_CF := (if s R_R10 <? s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0) .| (if s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R10 := s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214379, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214383:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287af, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287b2, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287b6, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287ba, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214383, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214394:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287ba, s) :: t) = None))
    (VC2: (forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287bd, s[R_RAX := s R_CF]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214394, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214400:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287c0, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287c3, s[R_CF := (if s R_R8 <? s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0) .| (if s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R8 := s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214400, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214403:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287c3, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287c7, s[R_CF := (if s R_R9 <? s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0) .| (if s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R9 := s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214403, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214407:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287c7, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287cb, s[R_CF := (if s R_R10 <? s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0) .| (if s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R10 := s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214407, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214411:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287cb, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (24 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287cf, s[R_CF := (if s R_R11 <? s V_MEM64 Ⓠ[ 24 + s R_RDX ] then 1 else 0) .| (if s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R11 := s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214411, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214415:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287cf, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287d2, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287d6, s[V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]][R_RSI := 32 ⊕ s R_RSI]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287da, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC5: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287de, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l) = None))
    (VC6: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287e1, s[R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC7: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287e5, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]]) :: l) = None))
    (VC8: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287e9, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX]) :: l) = None))
    (VC9: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287ec, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]]) :: l) = None))
    (VC10: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (40 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287f0, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]][R_R9 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 40 + s R_RSI ]]) :: l) = None))
    (VC11: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall n n0 n1 : N, MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_readable s (32 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (40 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287f4, s[R_RSI := 32 ⊕ s R_RSI][R_OF := n1][R_RCX := s R_RCX ⊖ 1][R_SF := n0][R_ZF := if s R_RCX mod 2 ^ 64 =? 1 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDX := 32 ⊕ s R_RDX][R_R8 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 32 + s R_RSI ]][R_R9 := (s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]) Ⓠ[ 40 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214415, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
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

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214452:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287f4, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287f8, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287fc, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> N.lnot (s R_ZF) 1 mod 2 = 0 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287fe, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l)))
    (VC5: (MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall p : positive, N.lnot (s R_ZF) 1 mod 2 = N.pos p -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x001287c0, s[R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214452, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214462:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x001287fe, s) :: t) = None))
    (VC2: (forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128802, s[R_RSI := 32 ⊕ s R_RSI]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214462, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214466:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128802, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128805, s[R_CF := (if s R_R8 <? s V_MEM64 Ⓠ[ s R_RDX ] then 1 else 0) .| (if s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R8 := s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R8 ⊖ s V_MEM64 Ⓠ[ s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214466, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214469:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128805, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (8 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128809, s[R_CF := (if s R_R9 <? s V_MEM64 Ⓠ[ 8 + s R_RDX ] then 1 else 0) .| (if s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R9 := s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R9 ⊖ s V_MEM64 Ⓠ[ 8 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214469, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214473:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128809, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (16 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012880d, s[R_CF := (if s R_R10 <? s V_MEM64 Ⓠ[ 16 + s R_RDX ] then 1 else 0) .| (if s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R10 := s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R10 ⊖ s V_MEM64 Ⓠ[ 16 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214473, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214477:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012880d, s) :: t) = None))
    (VC2: (forall n n0 n1 : N, MemAcc mem_readable s (24 ⊕ s R_RDX) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128811, s[R_CF := (if s R_R11 <? s V_MEM64 Ⓠ[ 24 + s R_RDX ] then 1 else 0) .| (if s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ] <? s R_CF then 1 else 0)][R_OF := n1][R_R11 := s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ] ⊖ s R_CF][R_SF := n0][R_ZF := if (s R_R11 ⊖ s V_MEM64 Ⓠ[ 24 + s R_RDX ]) mod 2 ^ 64 =? s R_CF mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214477, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214481:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128811, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128815, s[R_RDX := 32 ⊕ s R_RDX]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128818, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ]]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012881c, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ]]) :: l) = None))
    (VC5: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128820, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ]]) :: l) = None))
    (VC6: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128824, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]]) :: l) = None))
    (VC7: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128828, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDI := 32 ⊕ s R_RDI]) :: l) = None))
    (VC8: (MemAcc mem_writable s (s R_RDI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x0012882a, s[R_RDX := 32 ⊕ s R_RDX][V_MEM64 := s V_MEM64 [Ⓠs R_RDI := s R_R8 ] [Ⓠ8 + s R_RDI := s R_R9 ] [Ⓠ16 + s R_RDI := s R_R10 ] [Ⓠ24 + s R_RDI := s R_R11 ]][R_RDI := 32 ⊕ s R_RDI][R_OF := n1][R_RAX := scast 32 64 (((s R_RAX >> 0) mod 2 ^ 32 + 1) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (((s R_RAX >> 0) mod 2 ^ 32 + 1) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214481, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
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

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214506:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012882a, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x0012882c, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n n0 n1 : N, (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128832, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 1][R_PF := n]) :: l)))
    (VC4: (forall n n0 n1 : N, (scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128777, s[R_OF := n1][R_RAX := scast 32 64 (msub 32 ((s R_RAX >> 0) mod 2 ^ 32) 1) mod 2 ^ 32][R_SF := n0][R_ZF := 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214506, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214514:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits ((Addr 0x00128832, s) :: t) = None))
    (VC2: (forall (n n0 n1 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits true ((Addr 0x00128834, s[R_CF := (if (s R_RAX + s R_RAX) mod 2 ^ 32 <? s R_RAX mod 2 ^ 32 then 1 else 0) .| (if (s R_RAX + s R_RAX + s R_CF) mod 2 ^ 32 <? (s R_RAX + s R_RAX) mod 2 ^ 32 then 1 else 0)][R_OF := n1][R_RAX := scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32][R_SF := n0][R_ZF := if scast 32 64 ((((s R_RAX >> 0) mod 2 ^ 32 + (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 + s R_CF) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_sub_nc_amd64 invs exits false ((Addr 1214514, s)::t).
Proof.
  intros; find_vcs (1214272::1214304::1214327::1214334::1214337::1214340::1214343::1214351::1214354::1214358::1214365::1214368::1214372::1214375::1214379::1214383::1214394::1214400::1214403::1214407::1214411::1214415::1214452::1214462::1214466::1214469::1214473::1214477::1214481::1214506::1214514::1214342::1214367::1214397::1214516::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
Qed.

Ltac libgmp_so_10_5_0___gmpn_sub_nc_amd64_bigstep := first [ apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214272 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214304 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214327 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214334 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214337 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214340 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214343 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214351 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214354 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214358 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214365 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214368 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214372 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214375 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214379 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214383 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214394 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214400 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214403 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214407 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214411 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214415 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214452 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214462 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214466 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214469 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214473 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214477 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214481 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214506 | apply libgmp_so_10_5_0___gmpn_sub_nc_amd64_stepfrom_1214514 ]; intros; (reflexivity || ISA_invhere).
(* END BIGSTEPS GENERATED LEMMAS *)