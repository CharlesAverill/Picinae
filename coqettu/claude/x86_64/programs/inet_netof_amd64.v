(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: inet_netof
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_netof_amd64 : program := fun _ a => match a with

(* 0x0015a166: MOV EAX,EDI *)
(*    1417574: MOV EAX,EDI *)
| 0x15a166 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a168: SHR EAX,0x18 *)
(*    1417576: SHR EAX,0x18 *)
| 0x15a168 => Some (3,
	Move (V_TEMP 0x6df80) (BinOp OP_AND (Word 0x18 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e000) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x6df80)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e000)) (Var (V_TEMP 0x2f700))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF))) $;
	Move (V_TEMP 0x2fa80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa80)))))) $;
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e000)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF))) $;
	Move (V_TEMP 0x2fe80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
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

(* 0x0015a16b: TEST EDI,EDI *)
(*    1417579: TEST EDI,EDI *)
| 0x15a16b => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a16d: JNS 0x0015a181 *)
(*    1417581: JNS 0x0015a181 *)
| 0x15a16d => Some (2,
	Move (V_TEMP 0x12b00) (UnOp OP_NOT (Var R_SF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x15a181 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015a16f: MOV EDX,EDI *)
(*    1417583: MOV EDX,EDI *)
| 0x15a16f => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015a171: SHR EDI,0x8 *)
(*    1417585: SHR EDI,0x8 *)
| 0x15a171 => Some (3,
	Move (V_TEMP 0x6df80) (BinOp OP_AND (Word 0x8 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e000) (Extract 31 0 (Var R_RDI)) $;
	Move R_RDI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Var (V_TEMP 0x6df80)))) (Word 0 64)) (BinOp OP_AND (Var R_RDI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e000)) (Var (V_TEMP 0x2f700))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF))) $;
	Move (V_TEMP 0x2fa80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa80)))))) $;
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e000)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF))) $;
	Move (V_TEMP 0x2fe80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
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

(* 0x0015a174: SHR EDX,0x10 *)
(*    1417588: SHR EDX,0x10 *)
| 0x15a174 => Some (3,
	Move (V_TEMP 0x6df80) (BinOp OP_AND (Word 0x10 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x6e000) (Extract 31 0 (Var R_RDX)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Var (V_TEMP 0x6df80)))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e000)) (Var (V_TEMP 0x2f700))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF))) $;
	Move (V_TEMP 0x2fa80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa80)))))) $;
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6df80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e000)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF))) $;
	Move (V_TEMP 0x2fe80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6df80)) (Word 0x0 32)) $;
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

(* 0x0015a177: CMP EAX,0xbf *)
(*    1417591: CMP EAX,0xbf *)
| 0x15a177 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xbf 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xbf 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3df80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xbf 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3df80)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3df80)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3df80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a17c: MOV EAX,EDX *)
(*    1417596: MOV EAX,EDX *)
| 0x15a17c => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a17e: CMOVA EAX,EDI *)
(*    1417598: CMOVA EAX,EDI *)
| 0x15a17e => Some (3,
	Move (V_TEMP 0x12900) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move (V_TEMP 0x12a00) (UnOp OP_NOT (Var (V_TEMP 0x12900))) $;
	Move (V_TEMP 0x3db00) (Extract 31 0 (Var R_RDI)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3db80) (UnOp OP_NOT (Var (V_TEMP 0x12a00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3db80))) (
		Jmp (Word 0x15a181 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3db00))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64)))
)

(* 0x0015a181: RET *)
(*    1417601: RET *)
| 0x15a181 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx inet_netof_amd64.
Proof. Picinae_typecheck. Qed.
