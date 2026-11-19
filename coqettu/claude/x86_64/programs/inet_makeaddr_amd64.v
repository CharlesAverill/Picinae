(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: inet_makeaddr
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_makeaddr_amd64 : program := fun _ a => match a with

(* 0x0015a11b: CMP EDI,0xff *)
(*    1417499: CMP EDI,0xff *)
| 0x15a11b => Some (6,
	Move (V_TEMP 0x3e400) (Extract 31 0 (Var R_RDI)) $;
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

(* 0x0015a121: JA 0x0015a12b *)
(*    1417505: JA 0x0015a12b *)
| 0x15a121 => Some (2,
	Move (V_TEMP 0x12900) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move (V_TEMP 0x12a00) (UnOp OP_NOT (Var (V_TEMP 0x12900))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12a00))) (
		Jmp (Word 0x15a12b 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015a123: SHL EDI,0x18 *)
(*    1417507: SHL EDI,0x18 *)
| 0x15a123 => Some (3,
	Move (V_TEMP 0x69f80) (BinOp OP_AND (Word 0x18 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6a000) (Extract 31 0 (Var R_RDI)) $;
	Move R_RDI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_LSHIFT (Extract 31 0 (Var R_RDI)) (Var (V_TEMP 0x69f80)))) (Word 0 64)) (BinOp OP_AND (Var R_RDI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move (V_TEMP 0x2e580) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e600) (BinOp OP_MINUS (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e680) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a000)) (Var (V_TEMP 0x2e600))) $;
	Move (V_TEMP 0x2e780) (BinOp OP_SLT (Var (V_TEMP 0x2e680)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e800) (UnOp OP_NOT (Var (V_TEMP 0x2e580))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e800)) (Var R_CF))) $;
	Move (V_TEMP 0x2e900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e580)) (Var (V_TEMP 0x2e780)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2e880))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2e900)))))) $;
	Move (V_TEMP 0x2ea80) (BinOp OP_EQ (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2eb00) (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x2eb00)))) $;
	Move (V_TEMP 0x2ec80) (UnOp OP_NOT (Var (V_TEMP 0x2ea80))) $;
	Move (V_TEMP 0x2ed00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ec80)) (Var R_OF))) $;
	Move (V_TEMP 0x2ed80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ea80)) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ec00))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x0015a126: MOV EAX,EDI *)
(*    1417510: MOV EAX,EDI *)
| 0x15a126 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a128: OR EAX,ESI *)
(*    1417512: OR EAX,ESI *)
| 0x15a128 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RSI)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a12a: RET *)
(*    1417514: RET *)
| 0x15a12a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0015a12b: MOV EAX,EDI *)
(*    1417515: MOV EAX,EDI *)
| 0x15a12b => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a12d: MOV EDX,EDI *)
(*    1417517: MOV EDX,EDI *)
| 0x15a12d => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015a12f: SHL EAX,0x10 *)
(*    1417519: SHL EAX,0x10 *)
| 0x15a12f => Some (3,
	Move (V_TEMP 0x69f80) (BinOp OP_AND (Word 0x10 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6a000) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_LSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x69f80)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2e580) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e600) (BinOp OP_MINUS (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e680) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a000)) (Var (V_TEMP 0x2e600))) $;
	Move (V_TEMP 0x2e780) (BinOp OP_SLT (Var (V_TEMP 0x2e680)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e800) (UnOp OP_NOT (Var (V_TEMP 0x2e580))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e800)) (Var R_CF))) $;
	Move (V_TEMP 0x2e900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e580)) (Var (V_TEMP 0x2e780)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2e880))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2e900)))))) $;
	Move (V_TEMP 0x2ea80) (BinOp OP_EQ (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2eb00) (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x2eb00)))) $;
	Move (V_TEMP 0x2ec80) (UnOp OP_NOT (Var (V_TEMP 0x2ea80))) $;
	Move (V_TEMP 0x2ed00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ec80)) (Var R_OF))) $;
	Move (V_TEMP 0x2ed80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ea80)) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ec00))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x0015a132: SHL EDX,0x8 *)
(*    1417522: SHL EDX,0x8 *)
| 0x15a132 => Some (3,
	Move (V_TEMP 0x69f80) (BinOp OP_AND (Word 0x8 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6a000) (Extract 31 0 (Var R_RDX)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_LSHIFT (Extract 31 0 (Var R_RDX)) (Var (V_TEMP 0x69f80)))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x2e580) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e600) (BinOp OP_MINUS (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e680) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a000)) (Var (V_TEMP 0x2e600))) $;
	Move (V_TEMP 0x2e780) (BinOp OP_SLT (Var (V_TEMP 0x2e680)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e800) (UnOp OP_NOT (Var (V_TEMP 0x2e580))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e800)) (Var R_CF))) $;
	Move (V_TEMP 0x2e900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e580)) (Var (V_TEMP 0x2e780)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2e880))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2e900)))))) $;
	Move (V_TEMP 0x2ea80) (BinOp OP_EQ (Var (V_TEMP 0x69f80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2eb00) (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x2eb00)))) $;
	Move (V_TEMP 0x2ec80) (UnOp OP_NOT (Var (V_TEMP 0x2ea80))) $;
	Move (V_TEMP 0x2ed00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ec80)) (Var R_OF))) $;
	Move (V_TEMP 0x2ed80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ea80)) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ec00))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x69f80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x0015a135: OR EAX,ESI *)
(*    1417525: OR EAX,ESI *)
| 0x15a135 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RSI)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a137: OR EDX,ESI *)
(*    1417527: OR EDX,ESI *)
| 0x15a137 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RSI)))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a139: CMP EDI,0xffff *)
(*    1417529: CMP EDI,0xffff *)
| 0x15a139 => Some (6,
	Move (V_TEMP 0x3e400) (Extract 31 0 (Var R_RDI)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3e400)) (Word 0xffff 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e500) (BinOp OP_MINUS (Var (V_TEMP 0x3e400)) (Word 0xffff 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3e500)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3e500)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3e500)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a13f: CMOVA EAX,EDX *)
(*    1417535: CMOVA EAX,EDX *)
| 0x15a13f => Some (3,
	Move (V_TEMP 0x12900) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move (V_TEMP 0x12a00) (UnOp OP_NOT (Var (V_TEMP 0x12900))) $;
	Move (V_TEMP 0x3db00) (Extract 31 0 (Var R_RDX)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3db80) (UnOp OP_NOT (Var (V_TEMP 0x12a00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3db80))) (
		Jmp (Word 0x15a142 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3db00))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64)))
)

(* 0x0015a142: RET *)
(*    1417538: RET *)
| 0x15a142 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx inet_makeaddr_amd64.
Proof. Picinae_typecheck. Qed.
