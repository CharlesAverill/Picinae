(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: __sigaddset
entry: 0x275ce0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition sigaddset_internal_amd64 : program := fun _ a => match a with

(* 0x00275ce0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00275ce4: MOV ECX,ESI *)
(*          4: MOV ECX,ESI *)
| 0x4 => Some (2,
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Extract 31 0 (Var R_RSI))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00275ce6: LEA EAX,[RSI + 0x3e] *)
(*          6: LEA EAX,[RSI + 0x3e] *)
| 0x6 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x3e 64)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var (V_TEMP 0x4780)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00275ce9: MOV EDX,0x1 *)
(*          9: MOV EDX,0x1 *)
| 0x9 => Some (5,
	Move R_RDX (Word 0x1 64)
)

(* 0x00275cee: SUB ECX,0x1 *)
(*         14: SUB ECX,0x1 *)
| 0xe => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RCX)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00275cf1: CMOVNS EAX,ECX *)
(*         17: CMOVNS EAX,ECX *)
| 0x11 => Some (3,
	Move (V_TEMP 0x12c00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 1 8)) $;
	Move (V_TEMP 0x3dc00) (Extract 31 0 (Var R_RCX)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3dc80) (BinOp OP_XOR (Var (V_TEMP 0x12c00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x14 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x3dc00)))
)

(* 0x00275cf4: SHL RDX,CL *)
(*         20: SHL RDX,CL *)
| 0x14 => Some (3,
	Move (V_TEMP 0x6a680) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x6a700) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a680)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a680)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a680)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a700)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a680)) (Word 0x0 8))) $;
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

(* 0x00275cf7: SAR EAX,0x6 *)
(*         23: SAR EAX,0x6 *)
| 0x17 => Some (3,
	Move (V_TEMP 0x68580) (BinOp OP_AND (Word 0x6 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x68600) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x68580)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68580)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68580)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68600)) (Var (V_TEMP 0x2f080))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68580)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68580)) (Word 0x0 32))) $;
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

(* 0x00275cfa: CDQE *)
(*         26: CDQE *)
| 0x1a => Some (2,
	Move R_RAX (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00275cfc: OR qword ptr [RDI + RAX*0x8],RDX *)
(*         28: OR qword ptr [RDI + RAX*0x8],RDX *)
| 0x1c => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x8 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move (V_TEMP 0x6b80) (BinOp OP_OR (Var (V_TEMP 0x6b80)) (Var R_RDX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Var (V_TEMP 0x6b80)) LittleE 8) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6b80)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6b80)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6b80)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00275d00: XOR EAX,EAX *)
(*         32: XOR EAX,EAX *)
| 0x20 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00275d02: RET *)
(*         34: RET *)
| 0x22 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx sigaddset_internal_amd64.
Proof. Picinae_typecheck. Qed.

