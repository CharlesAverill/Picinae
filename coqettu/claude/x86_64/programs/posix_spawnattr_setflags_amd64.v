(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: posix_spawnattr_setflags
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_setflags_amd64 : program := fun _ a => match a with

(* 0x0015cda3: MOVSX ESI,SI *)
(*    1428899: MOVSX ESI,SI *)
| 0x15cda3 => Some (3,
	Move R_RSI (Cast CAST_SIGNED 64 (Extract 15 0 (Var R_RSI))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x0015cda6: MOV EAX,0x16 *)
(*    1428902: MOV EAX,0x16 *)
| 0x15cda6 => Some (5,
	Move R_RAX (Word 0x16 64)
)

(* 0x0015cdab: CMP ESI,0xff *)
(*    1428907: CMP ESI,0xff *)
| 0x15cdab => Some (6,
	Move (V_TEMP 0x3e400) (Extract 31 0 (Var R_RSI)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e400)) (Word 0xff 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e500) (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xff 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e500)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e500)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e500)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015cdb1: JA 0x0015cdb7 *)
(*    1428913: JA 0x0015cdb7 *)
| 0x15cdb1 => Some (2,
	Move (V_TEMP 0x12900) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move (V_TEMP 0x12a00) (UnOp OP_NOT (Var (V_TEMP 0x12900))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12a00))) (
		Jmp (Word 0x15cdb7 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015cdb3: MOV dword ptr [RDI],ESI *)
(*    1428915: MOV dword ptr [RDI],ESI *)
| 0x15cdb3 => Some (2,
	Move (V_TEMP 0x6a00) (Extract 31 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x0015cdb5: XOR EAX,EAX *)
(*    1428917: XOR EAX,EAX *)
| 0x15cdb5 => Some (2,
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

(* 0x0015cdb7: RET *)
(*    1428919: RET *)
| 0x15cdb7 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx posix_spawnattr_setflags_amd64.
Proof. Picinae_typecheck. Qed.
