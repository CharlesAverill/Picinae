(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strxfrm_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strxfrm_l_amd64 : program := fun _ a => match a with

(* 0x001462ed: PUSH R14 *)
(*    1336045: PUSH R14 *)
| 0x1462ed => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R14) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001462ef: MOV R14,RDI *)
(*    1336047: MOV R14,RDI *)
| 0x1462ef => Some (3,
	Move R_R14 (Var R_RDI)
)

(* 0x001462f2: MOV RDI,RSI *)
(*    1336050: MOV RDI,RSI *)
| 0x1462f2 => Some (3,
	Move R_RDI (Var R_RSI)
)

(* 0x001462f5: PUSH RBP *)
(*    1336053: PUSH RBP *)
| 0x1462f5 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001462f6: MOV RBP,RDX *)
(*    1336054: MOV RBP,RDX *)
| 0x1462f6 => Some (3,
	Move R_RBP (Var R_RDX)
)

(* 0x001462f9: PUSH RBX *)
(*    1336057: PUSH RBX *)
| 0x1462f9 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001462fa: MOV RBX,RSI *)
(*    1336058: MOV RBX,RSI *)
| 0x1462fa => Some (3,
	Move R_RBX (Var R_RSI)
)

(* 0x001462fd: SUB RSP,0x10 *)
(*    1336061: SUB RSP,0x10 *)
| 0x1462fd => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSP) (Word 0x10 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00146301: CALL 0x001348c0 *)
(*    1336065: CALL 0x001348c0 *)
| 0x146301 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x146306 64)) LittleE 8) $;
	Jmp (Word 0x1348c0 64)
)

(* 0x00146306: MOV RDX,RAX *)
(*    1336070: MOV RDX,RAX *)
| 0x146306 => Some (3,
	Move R_RDX (Var R_RAX)
)

(* 0x00146309: CMP RAX,RBP *)
(*    1336073: CMP RAX,RBP *)
| 0x146309 => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RBP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBP)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBP)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBP)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0014630c: JC 0x0014631a *)
(*    1336076: JC 0x0014631a *)
| 0x14630c => Some (2,
	If (Cast CAST_LOW 1 (Var R_CF)) (
		Jmp (Word 0x14631a 64)
	) (* else *) (
		Nop
	)
)

(* 0x0014630e: ADD RSP,0x10 *)
(*    1336078: ADD RSP,0x10 *)
| 0x14630e => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Var R_RSP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00146312: MOV RAX,RDX *)
(*    1336082: MOV RAX,RDX *)
| 0x146312 => Some (3,
	Move R_RAX (Var R_RDX)
)

(* 0x00146315: POP RBX *)
(*    1336085: POP RBX *)
| 0x146315 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00146316: POP RBP *)
(*    1336086: POP RBP *)
| 0x146316 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00146317: POP R14 *)
(*    1336087: POP R14 *)
| 0x146317 => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R14 (Var (V_TEMP 0x55200))
)

(* 0x00146319: RET *)
(*    1336089: RET *)
| 0x146319 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0014631a: MOV RSI,RBX *)
(*    1336090: MOV RSI,RBX *)
| 0x14631a => Some (3,
	Move R_RSI (Var R_RBX)
)

(* 0x0014631d: MOV RDI,R14 *)
(*    1336093: MOV RDI,R14 *)
| 0x14631d => Some (3,
	Move R_RDI (Var R_R14)
)

(* 0x00146320: MOV qword ptr [RSP + 0x8],RAX *)
(*    1336096: MOV qword ptr [RSP + 0x8],RAX *)
| 0x146320 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00146325: CALL 0x001659c7 *)
(*    1336101: CALL 0x001659c7 *)
| 0x146325 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x14632a 64)) LittleE 8) $;
	Jmp (Word 0x1659c7 64)
)

(* 0x0014632a: MOV RDX,qword ptr [RSP + 0x8] *)
(*    1336106: MOV RDX,qword ptr [RSP + 0x8] *)
| 0x14632a => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0x11f00))
)

(* 0x0014632f: JMP 0x0014630e *)
(*    1336111: JMP 0x0014630e *)
| 0x14632f => Some (2,
	Jmp (Word 0x14630e 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx strxfrm_l_amd64.
Proof. Picinae_typecheck. Qed.
