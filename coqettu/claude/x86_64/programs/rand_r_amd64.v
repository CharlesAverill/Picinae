(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: rand_r
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition rand_r_amd64 : program := fun _ a => match a with

(* 0x0015c29b: IMUL EDX,dword ptr [RDI],0x41c64e6d *)
(*    1426075: IMUL EDX,dword ptr [RDI],0x41c64e6d *)
| 0x15c29b => Some (6,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0x4c580) (Cast CAST_SIGNED 64 (Var (V_TEMP 0x11e80))) $;
	Move (V_TEMP 0x4c600) (Cast CAST_SIGNED 64 (Word 0x41c64e6d 32)) $;
	Move (V_TEMP 0x4c700) (BinOp OP_TIMES (Var (V_TEMP 0x4c580)) (Var (V_TEMP 0x4c600))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4c700)) (Word 0 64))) $;
	Move (V_TEMP 0x4c880) (Cast CAST_LOW 32 (BinOp OP_RSHIFT (Var (V_TEMP 0x4c700)) (Word 32 64))) $;
	Move (V_TEMP 0x2d100) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x2d100)) (Var (V_TEMP 0x4c700)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015c2a1: ADD EDX,0x3039 *)
(*    1426081: ADD EDX,0x3039 *)
| 0x15c2a1 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x3039 32)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x3039 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3039 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x3039 32))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2a7: MOV EAX,EDX *)
(*    1426087: MOV EAX,EDX *)
| 0x15c2a7 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015c2a9: MOV dword ptr [RDI],EDX *)
(*    1426089: MOV dword ptr [RDI],EDX *)
| 0x15c2a9 => Some (2,
	Move (V_TEMP 0x6a00) (Extract 31 0 (Var R_RDX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x0015c2ab: SHR EAX,0xb *)
(*    1426091: SHR EAX,0xb *)
| 0x15c2ab => Some (3,
	Move (V_TEMP 0x6df80) (BinOp OP_AND (Word 0xb 32) (Word 0x1f 32)) $;
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

(* 0x0015c2ae: XOR EAX,EDX *)
(*    1426094: XOR EAX,EDX *)
| 0x15c2ae => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2b0: MOV EDX,EAX *)
(*    1426096: MOV EDX,EAX *)
| 0x15c2b0 => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015c2b2: SHL EDX,0x7 *)
(*    1426098: SHL EDX,0x7 *)
| 0x15c2b2 => Some (3,
	Move (V_TEMP 0x69f80) (BinOp OP_AND (Word 0x7 32) (Word 0x1f 32)) $;
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

(* 0x0015c2b5: AND EDX,0x9d2c5680 *)
(*    1426101: AND EDX,0x9d2c5680 *)
| 0x15c2b5 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x9d2c5680 32))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2bb: XOR EAX,EDX *)
(*    1426107: XOR EAX,EDX *)
| 0x15c2bb => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2bd: MOV EDX,EAX *)
(*    1426109: MOV EDX,EAX *)
| 0x15c2bd => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015c2bf: SHL EDX,0xf *)
(*    1426111: SHL EDX,0xf *)
| 0x15c2bf => Some (3,
	Move (V_TEMP 0x69f80) (BinOp OP_AND (Word 0xf 32) (Word 0x1f 32)) $;
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

(* 0x0015c2c2: AND EDX,0xefc60000 *)
(*    1426114: AND EDX,0xefc60000 *)
| 0x15c2c2 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xefc60000 32))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2c8: XOR EAX,EDX *)
(*    1426120: XOR EAX,EDX *)
| 0x15c2c8 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2ca: MOV EDX,EAX *)
(*    1426122: MOV EDX,EAX *)
| 0x15c2ca => Some (2,
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015c2cc: SHR EDX,0x12 *)
(*    1426124: SHR EDX,0x12 *)
| 0x15c2cc => Some (3,
	Move (V_TEMP 0x6df80) (BinOp OP_AND (Word 0x12 32) (Word 0x1f 32)) $;
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

(* 0x0015c2cf: XOR EAX,EDX *)
(*    1426127: XOR EAX,EDX *)
| 0x15c2cf => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2d1: SHR EAX,0x1 *)
(*    1426129: SHR EAX,0x1 *)
| 0x15c2d1 => Some (2,
	Move (V_TEMP 0x6db80) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x6db80)) (Word 0x0 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c2d3: RET *)
(*    1426131: RET *)
| 0x15c2d3 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx rand_r_amd64.
Proof. Picinae_typecheck. Qed.
