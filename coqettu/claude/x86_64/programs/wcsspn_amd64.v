(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcsspn
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsspn_amd64 : program := fun _ a => match a with

(* 0x00165fec: PUSH R12 *)
(*    1466348: PUSH R12 *)
| 0x165fec => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165fee: MOV R12,RDI *)
(*    1466350: MOV R12,RDI *)
| 0x165fee => Some (3,
	Move R_R12 (Var R_RDI)
)

(* 0x00165ff1: PUSH RBP *)
(*    1466353: PUSH RBP *)
| 0x165ff1 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165ff2: MOV RBP,RSI *)
(*    1466354: MOV RBP,RSI *)
| 0x165ff2 => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x00165ff5: PUSH RBX *)
(*    1466357: PUSH RBX *)
| 0x165ff5 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165ff6: MOV RBX,RDI *)
(*    1466358: MOV RBX,RDI *)
| 0x165ff6 => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x00165ff9: JMP 0x00165fff *)
(*    1466361: JMP 0x00165fff *)
| 0x165ff9 => Some (2,
	Jmp (Word 0x165fff 64)
)

(* 0x00165ffb: ADD RBX,0x4 *)
(*    1466363: ADD RBX,0x4 *)
| 0x165ffb => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) (Var R_RBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x4 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00165fff: MOV ESI,dword ptr [RBX] *)
(*    1466367: MOV ESI,dword ptr [RBX] *)
| 0x165fff => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RBX) LittleE 4) $;
	Move R_RSI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RSI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00166001: TEST ESI,ESI *)
(*    1466369: TEST ESI,ESI *)
| 0x166001 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166003: JZ 0x00166012 *)
(*    1466371: JZ 0x00166012 *)
| 0x166003 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x166012 64)
	) (* else *) (
		Nop
	)
)

(* 0x00166005: MOV RDI,RBP *)
(*    1466373: MOV RDI,RBP *)
| 0x166005 => Some (3,
	Move R_RDI (Var R_RBP)
)

(* 0x00166008: CALL 0x0013c310 *)
(*    1466376: CALL 0x0013c310 *)
| 0x166008 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x16600d 64)) LittleE 8) $;
	Jmp (Word 0x13c310 64)
)

(* 0x0016600d: TEST RAX,RAX *)
(*    1466381: TEST RAX,RAX *)
| 0x16600d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00166010: JNZ 0x00165ffb *)
(*    1466384: JNZ 0x00165ffb *)
| 0x166010 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x165ffb 64)
	) (* else *) (
		Nop
	)
)

(* 0x00166012: MOV RAX,RBX *)
(*    1466386: MOV RAX,RBX *)
| 0x166012 => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x00166015: POP RBX *)
(*    1466389: POP RBX *)
| 0x166015 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00166016: POP RBP *)
(*    1466390: POP RBP *)
| 0x166016 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00166017: SUB RAX,R12 *)
(*    1466391: SUB RAX,R12 *)
| 0x166017 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RAX) (Var R_R12))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_R12)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_R12)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_R12)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0016601a: POP R12 *)
(*    1466394: POP R12 *)
| 0x16601a => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x0016601c: SAR RAX,0x2 *)
(*    1466396: SAR RAX,0x2 *)
| 0x16601c => Some (4,
	Move (V_TEMP 0x68800) (BinOp OP_AND (Word 0x2 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x68880) (Var R_RAX) $;
	Move R_RAX (BinOp OP_ARSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68800)))) $;
	Move (V_TEMP 0x2ef00) (BinOp OP_NEQ (Var (V_TEMP 0x68800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2ef80) (BinOp OP_MINUS (Var (V_TEMP 0x68800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f000) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2ef80)))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f180) (BinOp OP_NEQ (Var (V_TEMP 0x2f080)) (Word 0x0 64)) $;
	Move (V_TEMP 0x2f200) (UnOp OP_NOT (Var (V_TEMP 0x2ef00))) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f200)) (Var R_CF))) $;
	Move (V_TEMP 0x2f300) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ef00)) (Var (V_TEMP 0x2f180)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2f280))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2f300)))))) $;
	Move (V_TEMP 0x2f480) (BinOp OP_EQ (Var (V_TEMP 0x68800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f500) (UnOp OP_NOT (Var (V_TEMP 0x2f480))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f500)) (Var R_OF)))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x68800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x00166020: RET *)
(*    1466400: RET *)
| 0x166020 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx wcsspn_amd64.
Proof. Picinae_typecheck. Qed.
