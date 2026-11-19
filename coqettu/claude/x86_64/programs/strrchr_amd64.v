(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strrchr
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strrchr_amd64 : program := fun _ a => match a with

(* 0x00165bc2: SUB RSP,0x18 *)
(*    1465282: SUB RSP,0x18 *)
| 0x165bc2 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSP) (Word 0x18 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165bc6: MOV dword ptr [RSP + 0xc],ESI *)
(*    1465286: MOV dword ptr [RSP + 0xc],ESI *)
| 0x165bc6 => Some (4,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0xc 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6a00) (Extract 31 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x00165bca: MOV qword ptr [RSP],RDI *)
(*    1465290: MOV qword ptr [RSP],RDI *)
| 0x165bca => Some (4,
	Move (V_TEMP 0x6a80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00165bce: CALL 0x001348c0 *)
(*    1465294: CALL 0x001348c0 *)
| 0x165bce => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165bd3 64)) LittleE 8) $;
	Jmp (Word 0x1348c0 64)
)

(* 0x00165bd3: MOV ESI,dword ptr [RSP + 0xc] *)
(*    1465299: MOV ESI,dword ptr [RSP + 0xc] *)
| 0x165bd3 => Some (4,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0xc 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 4) $;
	Move R_RSI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RSI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00165bd7: MOV RDI,qword ptr [RSP] *)
(*    1465303: MOV RDI,qword ptr [RSP] *)
| 0x165bd7 => Some (4,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x11f00))
)

(* 0x00165bdb: ADD RSP,0x18 *)
(*    1465307: ADD RSP,0x18 *)
| 0x165bdb => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Var R_RSP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165bdf: LEA RDX,[RAX + 0x1] *)
(*    1465311: LEA RDX,[RAX + 0x1] *)
| 0x165bdf => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x00165be3: JMP 0x001347a0 *)
(*    1465315: JMP 0x001347a0 *)
| 0x165be3 => Some (5,
	Jmp (Word 0x1347a0 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx strrchr_amd64.
Proof. Picinae_typecheck. Qed.
