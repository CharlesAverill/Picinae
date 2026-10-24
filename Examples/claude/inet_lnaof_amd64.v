(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: inet_lnaof
entry: 0x236630 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition inet_lnaof_amd64 : program := fun _ a => match a with

(* 0x00236630: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00236634: BSWAP EDI *)
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

(* 0x00236636: TEST EDI,EDI *)
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

(* 0x00236638: JNS 0x00236658 *)
(*          8: JNS 0x00236658 *)
| 0x8 => Some (2,
	Move (V_TEMP 0x12c00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12c00))) (
		Jmp (Word 0x28 64)
	) (* else *) (
		Nop
	)
)

(* 0x0023663a: MOV EDX,EDI *)
(*         10: MOV EDX,EDI *)
| 0xa => Some (2,
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0023663c: MOVZX EAX,DI *)
(*         12: MOVZX EAX,DI *)
| 0xc => Some (3,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Extract 15 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0023663f: MOVZX EDI,DIL *)
(*         15: MOVZX EDI,DIL *)
| 0xf => Some (4,
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Cast CAST_UNSIGNED 32 (Extract 7 0 (Var R_RDI)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00236643: AND EDX,0xc0000000 *)
(*         19: AND EDX,0xc0000000 *)
| 0x13 => Some (6,
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

(* 0x00236649: CMP EDX,0x80000000 *)
(*         25: CMP EDX,0x80000000 *)
| 0x19 => Some (6,
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

(* 0x0023664f: CMOVNZ EAX,EDI *)
(*         31: CMOVNZ EAX,EDI *)
| 0x1f => Some (3,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 0x3dc00) (Extract 31 0 (Var R_RDI)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3dc80) (BinOp OP_XOR (Var (V_TEMP 0x12880)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x22 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x3dc00)))
)

(* 0x00236652: RET *)
(*         34: RET *)
| 0x22 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00236658: MOV EAX,EDI *)
(*         40: MOV EAX,EDI *)
| 0x28 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0023665a: AND EAX,0xffffff *)
(*         42: AND EAX,0xffffff *)
| 0x2a => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xffffff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0023665f: RET *)
(*         47: RET *)
| 0x2f => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx inet_lnaof_amd64.
Proof. Picinae_typecheck. Qed.

