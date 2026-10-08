(* Automatically generated with pcode2coq
arch: amd64
file: while_true_break
function: while_true_break
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition while_true_break_amd64 : program := fun _ a => match a with

(* 0x001011a0: MOV RDX,RDI *)
(*          0: MOV RDX,RDI *)
| 0x0 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x001011a3: LEA RCX,[RDI + RDI*0x1] *)
(*          3: LEA RCX,[RDI + RDI*0x1] *)
| 0x3 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move R_RCX (Var (V_TEMP 0x4a80))
)

(* 0x001011a7: MOV RAX,RDI *)
(*          7: MOV RAX,RDI *)
| 0x7 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001011aa: IMUL RDX,RDI *)
(*         10: IMUL RDX,RDI *)
| 0xa => Some (4,
	Move (V_TEMP 0x4b500) (Cast CAST_SIGNED 128 (Var R_RDX)) $;
	Move (V_TEMP 0x4b580) (Cast CAST_SIGNED 128 (Var R_RDI)) $;
	Move (V_TEMP 0x4b680) (BinOp OP_TIMES (Var (V_TEMP 0x4b500)) (Var (V_TEMP 0x4b580))) $;
	Move R_RDX (BinOp OP_TIMES (Var R_RDX) (Var R_RDI)) $;
	Move (V_TEMP 0x4b800) (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4b680)) (Word 64 128))) $;
	Move (V_TEMP 0x2d200) (Cast CAST_SIGNED 128 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x2d200)) (Var (V_TEMP 0x4b680)))) $;
	Move R_OF (Cast CAST_LOW 1 (Var R_CF))
)

(* 0x001011ae: CMP RCX,RDX *)
(*         14: CMP RCX,RDX *)
| 0xe => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x001011b1: JNC 0x001011d4 *)
(*         17: JNC 0x001011d4 *)
| 0x11 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_CF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x34 64)
	) (* else *) (
		Nop
	)
)

(* 0x001011b3: NOP dword ptr CS:[RAX + RAX*0x1] *)
(*         19: NOP dword ptr CS:[RAX + RAX*0x1] *)
| 0x13 => Some (11,
	Move (V_TEMP 0x5580) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5680) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5580)))
)

(* 0x001011be: NOP *)
(*         30: NOP *)
| 0x1e => Some (2,
	Nop
)

(* 0x001011c0: SUB RAX,0x1 *)
(*         32: SUB RAX,0x1 *)
| 0x20 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x001011c4: MOV RDX,RAX *)
(*         36: MOV RDX,RAX *)
| 0x24 => Some (3,
	Move R_RDX (Var R_RAX)
)

(* 0x001011c7: LEA RCX,[RAX + RAX*0x1] *)
(*         39: LEA RCX,[RAX + RAX*0x1] *)
| 0x27 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	Move R_RCX (Var (V_TEMP 0x4a80))
)

(* 0x001011cb: IMUL RDX,RAX *)
(*         43: IMUL RDX,RAX *)
| 0x2b => Some (4,
	Move (V_TEMP 0x4b500) (Cast CAST_SIGNED 128 (Var R_RDX)) $;
	Move (V_TEMP 0x4b580) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move (V_TEMP 0x4b680) (BinOp OP_TIMES (Var (V_TEMP 0x4b500)) (Var (V_TEMP 0x4b580))) $;
	Move R_RDX (BinOp OP_TIMES (Var R_RDX) (Var R_RAX)) $;
	Move (V_TEMP 0x4b800) (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4b680)) (Word 64 128))) $;
	Move (V_TEMP 0x2d200) (Cast CAST_SIGNED 128 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x2d200)) (Var (V_TEMP 0x4b680)))) $;
	Move R_OF (Cast CAST_LOW 1 (Var R_CF))
)

(* 0x001011cf: CMP RCX,RDX *)
(*         47: CMP RCX,RDX *)
| 0x2f => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))
)

(* 0x001011d2: JC 0x001011c0 *)
(*         50: JC 0x001011c0 *)
| 0x32 => Some (2,
	If (Cast CAST_LOW 1 (Var R_CF)) (
		Jmp (Word 0x20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001011d4: RET *)
(*         52: RET *)
| 0x34 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx while_true_break_amd64.
Proof. Picinae_typecheck. Qed.
