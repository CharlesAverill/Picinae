(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: lcong48_r
entry: 0x146bb0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition lcong48_r_amd64 : program := fun _ a => match a with

(* 0x00146bb0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00146bb4: MOV EAX,dword ptr [RDI] *)
(*          4: MOV EAX,dword ptr [RDI] *)
| 0x4 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146bb6: MOV dword ptr [RSI],EAX *)
(*          6: MOV dword ptr [RSI],EAX *)
| 0x6 => Some (2,
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00146bb8: MOVZX EAX,word ptr [RDI + 0x4] *)
(*          8: MOVZX EAX,word ptr [RDI + 0x4] *)
| 0x8 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146bbc: MOV word ptr [RSI + 0x4],AX *)
(*         12: MOV word ptr [RSI + 0x4],AX *)
| 0xc => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x4 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146bc0: MOVZX EAX,word ptr [RDI + 0xa] *)
(*         16: MOVZX EAX,word ptr [RDI + 0xa] *)
| 0x10 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xa 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146bc4: MOVZX EDX,word ptr [RDI + 0x6] *)
(*         20: MOVZX EDX,word ptr [RDI + 0x6] *)
| 0x14 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x6 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00146bc8: SHL RAX,0x20 *)
(*         24: SHL RAX,0x20 *)
| 0x18 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RAX) $;
	Move R_RAX (BinOp OP_LSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
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

(* 0x00146bcc: OR RAX,RDX *)
(*         28: OR RAX,RDX *)
| 0x1c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00146bcf: MOVZX EDX,word ptr [RDI + 0x8] *)
(*         31: MOVZX EDX,word ptr [RDI + 0x8] *)
| 0x1f => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00146bd3: SHL EDX,0x10 *)
(*         35: SHL EDX,0x10 *)
| 0x23 => Some (3,
	Move (V_TEMP 0x6a280) (BinOp OP_AND (Word 0x10 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6a300) (Extract 31 0 (Var R_RDX)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_LSHIFT (Extract 31 0 (Var R_RDX)) (Var (V_TEMP 0x6a280)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a280)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a300)) (Var (V_TEMP 0x2e700))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a280)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a280)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x00146bd6: OR RAX,RDX *)
(*         38: OR RAX,RDX *)
| 0x26 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00146bd9: MOV qword ptr [RSI + 0x10],RAX *)
(*         41: MOV qword ptr [RSI + 0x10],RAX *)
| 0x29 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00146bdd: MOVZX EAX,word ptr [RDI + 0xc] *)
(*         45: MOVZX EAX,word ptr [RDI + 0xc] *)
| 0x2d => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xc 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146be1: MOV word ptr [RSI + 0xc],AX *)
(*         49: MOV word ptr [RSI + 0xc],AX *)
| 0x31 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0xc 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146be5: MOV EAX,0x1 *)
(*         53: MOV EAX,0x1 *)
| 0x35 => Some (5,
	Move R_RAX (Word 0x1 64)
)

(* 0x00146bea: MOV word ptr [RSI + 0xe],AX *)
(*         58: MOV word ptr [RSI + 0xe],AX *)
| 0x3a => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0xe 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146bee: XOR EAX,EAX *)
(*         62: XOR EAX,EAX *)
| 0x3e => Some (2,
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

(* 0x00146bf0: RET *)
(*         64: RET *)
| 0x40 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx lcong48_r_amd64.
Proof. Picinae_typecheck. Qed.

