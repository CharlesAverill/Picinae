(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: srand48_r
entry: 0x146b40 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition srand48_r_amd64 : program := fun _ a => match a with

(* 0x00146b40: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00146b44: MOV EAX,0x330e *)
(*          4: MOV EAX,0x330e *)
| 0x4 => Some (5,
	Move R_RAX (Word 0x330e 64)
)

(* 0x00146b49: MOV dword ptr [RSI + 0x2],EDI *)
(*          9: MOV dword ptr [RSI + 0x2],EDI *)
| 0x9 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x2 64)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00146b4c: MOV word ptr [RSI],AX *)
(*         12: MOV word ptr [RSI],AX *)
| 0xc => Some (3,
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x00146b4f: MOV RAX,0x5deece66d *)
(*         15: MOV RAX,0x5deece66d *)
| 0xf => Some (10,
	Move R_RAX (Word 0x5deece66d 64)
)

(* 0x00146b59: MOV qword ptr [RSI + 0x10],RAX *)
(*         25: MOV qword ptr [RSI + 0x10],RAX *)
| 0x19 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00146b5d: XOR EAX,EAX *)
(*         29: XOR EAX,EAX *)
| 0x1d => Some (2,
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

(* 0x00146b5f: MOV dword ptr [RSI + 0xc],0x1000b *)
(*         31: MOV dword ptr [RSI + 0xc],0x1000b *)
| 0x1f => Some (7,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0xc 64)) $;
	Move (V_TEMP 0x6b00) (Word 0x1000b 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00146b66: RET *)
(*         38: RET *)
| 0x26 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx srand48_r_amd64.
Proof. Picinae_typecheck. Qed.

