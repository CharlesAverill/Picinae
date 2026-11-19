(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: iswcntrl
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswcntrl_amd64 : program := fun _ a => match a with

(* 0x00141708: LEA EAX,[RDI + -0x7f] *)
(*    1316616: LEA EAX,[RDI + -0x7f] *)
| 0x141708 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff81 64)) $;
	Move R_RAX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4780)) (Word 0 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0014170b: CMP EAX,0x20 *)
(*    1316619: CMP EAX,0x20 *)
| 0x14170b => Some (3,
	Move (V_TEMP 0x3e880) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e880)) (Word 0x20 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e880)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e980) (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x20 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e980)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0014170e: JBE 0x00141734 *)
(*    1316622: JBE 0x00141734 *)
| 0x14170e => Some (2,
	Move (V_TEMP 0x12880) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x141734 64)
	) (* else *) (
		Nop
	)
)

(* 0x00141710: CMP EDI,0x1f *)
(*    1316624: CMP EDI,0x1f *)
| 0x141710 => Some (3,
	Move (V_TEMP 0x3e880) (Extract 31 0 (Var R_RDI)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e880)) (Word 0x1f 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e880)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1f 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e980) (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1f 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e980)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00141713: JBE 0x00141734 *)
(*    1316627: JBE 0x00141734 *)
| 0x141713 => Some (2,
	Move (V_TEMP 0x12880) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x141734 64)
	) (* else *) (
		Nop
	)
)

(* 0x00141715: LEA EDX,[RDI + -0x2028] *)
(*    1316629: LEA EDX,[RDI + -0x2028] *)
| 0x141715 => Some (6,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffdfd8 64)) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4880)) (Word 0 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0014171b: MOV EAX,0x1 *)
(*    1316635: MOV EAX,0x1 *)
| 0x14171b => Some (5,
	Move R_RAX (Word 0x1 64)
)

(* 0x00141720: CMP EDX,0x1 *)
(*    1316640: CMP EDX,0x1 *)
| 0x141720 => Some (3,
	Move (V_TEMP 0x3e880) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e880)) (Word 0x1 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e880)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e980) (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e980)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00141723: JBE 0x00141739 *)
(*    1316643: JBE 0x00141739 *)
| 0x141723 => Some (2,
	Move (V_TEMP 0x12880) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x141739 64)
	) (* else *) (
		Nop
	)
)

(* 0x00141725: SUB EDI,0xfff9 *)
(*    1316645: SUB EDI,0xfff9 *)
| 0x141725 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Extract 31 0 (Var R_RDI)) (Word 0xfff9 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Word 0xfff9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Word 0xfff9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfff9 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Word 0xfff9 32))) (Word 0 64)) (BinOp OP_AND (Var R_RDI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0014172b: XOR EAX,EAX *)
(*    1316651: XOR EAX,EAX *)
| 0x14172b => Some (2,
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

(* 0x0014172d: CMP EDI,0x2 *)
(*    1316653: CMP EDI,0x2 *)
| 0x14172d => Some (3,
	Move (V_TEMP 0x3e880) (Extract 31 0 (Var R_RDI)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e880)) (Word 0x2 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e880)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e980) (BinOp OP_MINUS (Var (V_TEMP 0x3e880)) (Word 0x2 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e980)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e980)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00141730: SETBE AL *)
(*    1316656: SETBE AL *)
| 0x141730 => Some (3,
	Move (V_TEMP 0x12880) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12880))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFFFFFFFF00 64)))
)

(* 0x00141733: RET *)
(*    1316659: RET *)
| 0x141733 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00141734: MOV EAX,0x1 *)
(*    1316660: MOV EAX,0x1 *)
| 0x141734 => Some (5,
	Move R_RAX (Word 0x1 64)
)

(* 0x00141739: RET *)
(*    1316665: RET *)
| 0x141739 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx iswcntrl_amd64.
Proof. Picinae_typecheck. Qed.
