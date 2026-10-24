(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: seed48 at 0x1469c0
function: seed48_r at 0x146b70
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition seed48_amd64 : program := fun _ a => match a with

(* ---- seed48 ---- *)

(* 0x001469c0: ENDBR64 *)
(*    1337792: ENDBR64 *)
| 0x1469c0 => Some (4,
	Nop
)

(* 0x001469c4: SUB RSP,0x8 *)
(*    1337796: SUB RSP,0x8 *)
| 0x1469c4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSP) (Word 0x8 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001469c8: LEA RSI,[0x31c750] *)
(*    1337800: LEA RSI,[0x31c750] *)
| 0x1469c8 => Some (7,
	Move R_RSI (Word 0x31c750 64)
)

(* 0x001469cf: CALL 0x00146b70 *)
(*    1337807: CALL 0x00146b70 *)
| 0x1469cf => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1469d4 64) LittleE 8) $;
	Jmp (Word 0x146b70 64)
)

(* 0x001469d4: LEA RAX,[0x31c756] *)
(*    1337812: LEA RAX,[0x31c756] *)
| 0x1469d4 => Some (7,
	Move R_RAX (Word 0x31c756 64)
)

(* 0x001469db: ADD RSP,0x8 *)
(*    1337819: ADD RSP,0x8 *)
| 0x1469db => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001469df: RET *)
(*    1337823: RET *)
| 0x1469df => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* ---- seed48_r ---- *)

(* 0x00146b70: ENDBR64 *)
(*    1338224: ENDBR64 *)
| 0x146b70 => Some (4,
	Nop
)

(* 0x00146b74: MOV EAX,dword ptr [RSI] *)
(*    1338228: MOV EAX,dword ptr [RSI] *)
| 0x146b74 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RSI) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146b76: MOV dword ptr [RSI + 0x6],EAX *)
(*    1338230: MOV dword ptr [RSI + 0x6],EAX *)
| 0x146b76 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x6 64)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00146b79: MOVZX EAX,word ptr [RSI + 0x4] *)
(*    1338233: MOVZX EAX,word ptr [RSI + 0x4] *)
| 0x146b79 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146b7d: MOV word ptr [RSI + 0xa],AX *)
(*    1338237: MOV word ptr [RSI + 0xa],AX *)
| 0x146b7d => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0xa 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146b81: MOVZX EAX,word ptr [RDI + 0x4] *)
(*    1338241: MOVZX EAX,word ptr [RDI + 0x4] *)
| 0x146b81 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146b85: MOV word ptr [RSI + 0x4],AX *)
(*    1338245: MOV word ptr [RSI + 0x4],AX *)
| 0x146b85 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x4 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146b89: MOVZX EAX,word ptr [RDI + 0x2] *)
(*    1338249: MOVZX EAX,word ptr [RDI + 0x2] *)
| 0x146b89 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146b8d: MOV word ptr [RSI + 0x2],AX *)
(*    1338253: MOV word ptr [RSI + 0x2],AX *)
| 0x146b8d => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x2 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146b91: MOVZX EAX,word ptr [RDI] *)
(*    1338257: MOVZX EAX,word ptr [RDI] *)
| 0x146b91 => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDI) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00146b94: MOV dword ptr [RSI + 0xc],0x1000b *)
(*    1338260: MOV dword ptr [RSI + 0xc],0x1000b *)
| 0x146b94 => Some (7,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0xc 64)) $;
	Move (V_TEMP 0x6b00) (Word 0x1000b 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00146b9b: MOV word ptr [RSI],AX *)
(*    1338267: MOV word ptr [RSI],AX *)
| 0x146b9b => Some (3,
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146b9e: MOV RAX,0x5deece66d *)
(*    1338270: MOV RAX,0x5deece66d *)
| 0x146b9e => Some (10,
	Move R_RAX (Word 0x5deece66d 64)
)

(* 0x00146ba8: MOV qword ptr [RSI + 0x10],RAX *)
(*    1338280: MOV qword ptr [RSI + 0x10],RAX *)
| 0x146ba8 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00146bac: XOR EAX,EAX *)
(*    1338284: XOR EAX,EAX *)
| 0x146bac => Some (2,
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

(* 0x00146bae: RET *)
(*    1338286: RET *)
| 0x146bae => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem seed48_welltyped_lifted: welltyped_prog x64typctx seed48_amd64.
Proof. Picinae_typecheck. Qed.
