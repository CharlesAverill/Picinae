(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: inet_netof
entry: 0x2366b0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition inet_netof_amd64 : program := fun _ a => match a with

(* 0x002366b0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x002366b4: BSWAP EDI *)
(*          4: BSWAP EDI *)
| 0x4 => Some (2,
	Move (V_TEMP 0x35200) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff000000 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_RSHIFT (Var (V_TEMP 0x35200)) (Word 24 32)) $;
	Move (V_TEMP 0x35380) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff0000 32)) $;
	Move (V_TEMP 0x35400) (BinOp OP_RSHIFT (Var (V_TEMP 0x35380)) (Word 8 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35400))) $;
	Move (V_TEMP 0x35500) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff00 32)) $;
	Move (V_TEMP 0x35580) (BinOp OP_LSHIFT (Var (V_TEMP 0x35500)) (Word 8 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35580))) $;
	Move (V_TEMP 0x35680) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x35700) (BinOp OP_LSHIFT (Var (V_TEMP 0x35680)) (Word 24 32)) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35700)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x002366b6: TEST EDI,EDI *)
(*          6: TEST EDI,EDI *)
| 0x6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002366b8: JNS 0x002366d8 *)
(*          8: JNS 0x002366d8 *)
| 0x8 => Some (2,
	Move (V_TEMP 0x12c00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12c00))) (
		Jmp (Word 0x28 64)
	) (* else *) (
		Nop
	)
)

(* 0x002366ba: MOV EDX,EDI *)
(*         10: MOV EDX,EDI *)
| 0xa => Some (2,
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x002366bc: MOV EAX,EDI *)
(*         12: MOV EAX,EDI *)
| 0xc => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x002366be: SHR EDI,0x8 *)
(*         14: SHR EDI,0x8 *)
| 0xe => Some (3,
	Move (V_TEMP 0x6e280) (BinOp OP_AND (Word 0x8 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e300) (Extract 31 0 (Var R_RDI)) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Var (V_TEMP 0x6e280)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e280)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e300)) (Var (V_TEMP 0x2f800))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e280)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e300)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x002366c1: AND EDX,0xc0000000 *)
(*         17: AND EDX,0xc0000000 *)
| 0x11 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xc0000000 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002366c7: SHR EAX,0x10 *)
(*         23: SHR EAX,0x10 *)
| 0x17 => Some (3,
	Move (V_TEMP 0x6e280) (BinOp OP_AND (Word 0x10 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e300) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x6e280)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e280)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e300)) (Var (V_TEMP 0x2f800))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e280)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e300)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x002366ca: CMP EDX,0x80000000 *)
(*         26: CMP EDX,0x80000000 *)
| 0x1a => Some (6,
	Move (V_TEMP 0x3e500) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e500)) (Word 0x80000000 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x80000000 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x80000000 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80000000 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e600) (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x80000000 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002366d0: CMOVNZ EAX,EDI *)
(*         32: CMOVNZ EAX,EDI *)
| 0x20 => Some (3,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 0x3dc00) (Extract 31 0 (Var R_RDI)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3dc80) (BinOp OP_XOR (Var (V_TEMP 0x12880)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x23 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x3dc00)))
)

(* 0x002366d3: RET *)
(*         35: RET *)
| 0x23 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002366d8: MOV EAX,EDI *)
(*         40: MOV EAX,EDI *)
| 0x28 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x002366da: SHR EAX,0x18 *)
(*         42: SHR EAX,0x18 *)
| 0x2a => Some (3,
	Move (V_TEMP 0x6e280) (BinOp OP_AND (Word 0x18 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e300) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x6e280)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e280)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e300)) (Var (V_TEMP 0x2f800))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e280)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e300)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x002366dd: RET *)
(*         45: RET *)
| 0x2d => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx inet_netof_amd64.
Proof. Picinae_typecheck. Qed.

