(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcsxfrm_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsxfrm_l_amd64 : program := fun _ a => match a with

(* 0x00146447: PUSH R12 *)
(*    1336391: PUSH R12 *)
| 0x146447 => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00146449: MOV R12,RDI *)
(*    1336393: MOV R12,RDI *)
| 0x146449 => Some (3,
	Move R_R12 (Var R_RDI)
)

(* 0x0014644c: MOV RDI,RSI *)
(*    1336396: MOV RDI,RSI *)
| 0x14644c => Some (3,
	Move R_RDI (Var R_RSI)
)

(* 0x0014644f: PUSH RBP *)
(*    1336399: PUSH RBP *)
| 0x14644f => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00146450: MOV RBP,RSI *)
(*    1336400: MOV RBP,RSI *)
| 0x146450 => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x00146453: PUSH RBX *)
(*    1336403: PUSH RBX *)
| 0x146453 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00146454: MOV RBX,RDX *)
(*    1336404: MOV RBX,RDX *)
| 0x146454 => Some (3,
	Move R_RBX (Var R_RDX)
)

(* 0x00146457: SUB RSP,0x10 *)
(*    1336407: SUB RSP,0x10 *)
| 0x146457 => Some (4,
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

(* 0x0014645b: CALL 0x0013c380 *)
(*    1336411: CALL 0x0013c380 *)
| 0x14645b => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x146460 64)) LittleE 8) $;
	Jmp (Word 0x13c380 64)
)

(* 0x00146460: MOV RCX,RAX *)
(*    1336416: MOV RCX,RAX *)
| 0x146460 => Some (3,
	Move R_RCX (Var R_RAX)
)

(* 0x00146463: CMP RAX,RBX *)
(*    1336419: CMP RAX,RBX *)
| 0x146463 => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RBX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00146466: JC 0x00146479 *)
(*    1336422: JC 0x00146479 *)
| 0x146466 => Some (2,
	If (Cast CAST_LOW 1 (Var R_CF)) (
		Jmp (Word 0x146479 64)
	) (* else *) (
		Nop
	)
)

(* 0x00146468: TEST RBX,RBX *)
(*    1336424: TEST RBX,RBX *)
| 0x146468 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RBX) (Var R_RBX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0014646b: JNZ 0x00146494 *)
(*    1336427: JNZ 0x00146494 *)
| 0x14646b => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x146494 64)
	) (* else *) (
		Nop
	)
)

(* 0x0014646d: ADD RSP,0x10 *)
(*    1336429: ADD RSP,0x10 *)
| 0x14646d => Some (4,
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

(* 0x00146471: MOV RAX,RCX *)
(*    1336433: MOV RAX,RCX *)
| 0x146471 => Some (3,
	Move R_RAX (Var R_RCX)
)

(* 0x00146474: POP RBX *)
(*    1336436: POP RBX *)
| 0x146474 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00146475: POP RBP *)
(*    1336437: POP RBP *)
| 0x146475 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00146476: POP R12 *)
(*    1336438: POP R12 *)
| 0x146476 => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00146478: RET *)
(*    1336440: RET *)
| 0x146478 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00146479: LEA RDX,[RAX + 0x1] *)
(*    1336441: LEA RDX,[RAX + 0x1] *)
| 0x146479 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x0014647d: MOV RSI,RBP *)
(*    1336445: MOV RSI,RBP *)
| 0x14647d => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x00146480: MOV RDI,R12 *)
(*    1336448: MOV RDI,R12 *)
| 0x146480 => Some (3,
	Move R_RDI (Var R_R12)
)

(* 0x00146483: MOV qword ptr [RSP + 0x8],RAX *)
(*    1336451: MOV qword ptr [RSP + 0x8],RAX *)
| 0x146483 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00146488: CALL 0x0013c3f0 *)
(*    1336456: CALL 0x0013c3f0 *)
| 0x146488 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x14648d 64)) LittleE 8) $;
	Jmp (Word 0x13c3f0 64)
)

(* 0x0014648d: MOV RCX,qword ptr [RSP + 0x8] *)
(*    1336461: MOV RCX,qword ptr [RSP + 0x8] *)
| 0x14648d => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RCX (Var (V_TEMP 0x11f00))
)

(* 0x00146492: JMP 0x0014646d *)
(*    1336466: JMP 0x0014646d *)
| 0x146492 => Some (2,
	Jmp (Word 0x14646d 64)
)

(* 0x00146494: SUB RBX,0x1 *)
(*    1336468: SUB RBX,0x1 *)
| 0x146494 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RBX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RBX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RBX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBX (BinOp OP_MINUS (Var R_RBX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00146498: MOV RSI,RBP *)
(*    1336472: MOV RSI,RBP *)
| 0x146498 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x0014649b: MOV RDI,R12 *)
(*    1336475: MOV RDI,R12 *)
| 0x14649b => Some (3,
	Move R_RDI (Var R_R12)
)

(* 0x0014649e: MOV qword ptr [RSP + 0x8],RAX *)
(*    1336478: MOV qword ptr [RSP + 0x8],RAX *)
| 0x14649e => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x001464a3: MOV RDX,RBX *)
(*    1336483: MOV RDX,RBX *)
| 0x1464a3 => Some (3,
	Move R_RDX (Var R_RBX)
)

(* 0x001464a6: CALL 0x0013c3f0 *)
(*    1336486: CALL 0x0013c3f0 *)
| 0x1464a6 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x1464ab 64)) LittleE 8) $;
	Jmp (Word 0x13c3f0 64)
)

(* 0x001464ab: MOV dword ptr [R12 + RBX*0x4],0x0 *)
(*    1336491: MOV dword ptr [R12 + RBX*0x4],0x0 *)
| 0x1464ab => Some (8,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RBX) (Word 0x4 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_R12) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a00) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x001464b3: MOV RCX,qword ptr [RSP + 0x8] *)
(*    1336499: MOV RCX,qword ptr [RSP + 0x8] *)
| 0x1464b3 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RCX (Var (V_TEMP 0x11f00))
)

(* 0x001464b8: JMP 0x0014646d *)
(*    1336504: JMP 0x0014646d *)
| 0x1464b8 => Some (2,
	Jmp (Word 0x14646d 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx wcsxfrm_l_amd64.
Proof. Picinae_typecheck. Qed.
