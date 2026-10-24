(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: gnu_dev_major
entry: 0x2254c0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition gnu_dev_major_amd64 : program := fun _ a => match a with

(* 0x002254c0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x002254c4: MOV RDX,RDI *)
(*          4: MOV RDX,RDI *)
| 0x4 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x002254c7: MOV RAX,RDI *)
(*          7: MOV RAX,RDI *)
| 0x7 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x002254ca: SHR RDX,0x8 *)
(*         10: SHR RDX,0x8 *)
| 0xa => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0x8 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_RDX) $;
	Move R_RDX (BinOp OP_RSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x002254ce: SHR RAX,0x20 *)
(*         14: SHR RAX,0x20 *)
| 0xe => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_RAX) $;
	Move R_RAX (BinOp OP_RSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x002254d2: AND EDX,0xfff *)
(*         18: AND EDX,0xfff *)
| 0x12 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xfff 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002254d8: AND EAX,0xfffff000 *)
(*         24: AND EAX,0xfffff000 *)
| 0x18 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xfffff000 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002254dd: OR EAX,EDX *)
(*         29: OR EAX,EDX *)
| 0x1d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002254df: RET *)
(*         31: RET *)
| 0x1f => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx gnu_dev_major_amd64.
Proof. Picinae_typecheck. Qed.

