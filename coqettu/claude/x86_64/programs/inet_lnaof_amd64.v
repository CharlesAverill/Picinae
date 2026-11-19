(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: inet_lnaof
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_lnaof_amd64 : program := fun _ a => match a with

(* 0x0015a143: MOV EAX,EDI *)
(*    1417539: MOV EAX,EDI *)
| 0x15a143 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a145: SHR EAX,0x18 *)
(*    1417541: SHR EAX,0x18 *)
| 0x15a145 => Some (3,
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

(* 0x0015a148: TEST EDI,EDI *)
(*    1417544: TEST EDI,EDI *)
| 0x15a148 => Some (2,
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

(* 0x0015a14a: JNS 0x0015a15e *)
(*    1417546: JNS 0x0015a15e *)
| 0x15a14a => Some (2,
	Move (V_TEMP 0x12b00) (UnOp OP_NOT (Var R_SF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x15a15e 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015a14c: MOVZX EDX,DI *)
(*    1417548: MOVZX EDX,DI *)
| 0x15a14c => Some (3,
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 15 0 (Var R_RDI))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0015a14f: CMP EAX,0xbf *)
(*    1417551: CMP EAX,0xbf *)
| 0x15a14f => Some (5,
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

(* 0x0015a154: MOVZX EDI,DIL *)
(*    1417556: MOVZX EDI,DIL *)
| 0x15a154 => Some (4,
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 7 0 (Var R_RDI))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x0015a158: MOV EAX,EDX *)
(*    1417560: MOV EAX,EDX *)
| 0x15a158 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a15a: CMOVA EAX,EDI *)
(*    1417562: CMOVA EAX,EDI *)
| 0x15a15a => Some (3,
	Move (V_TEMP 0x12900) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move (V_TEMP 0x12a00) (UnOp OP_NOT (Var (V_TEMP 0x12900))) $;
	Move (V_TEMP 0x3db00) (Extract 31 0 (Var R_RDI)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x3db80) (UnOp OP_NOT (Var (V_TEMP 0x12a00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3db80))) (
		Jmp (Word 0x15a15d 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3db00))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64)))
)

(* 0x0015a15d: RET *)
(*    1417565: RET *)
| 0x15a15d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0015a15e: MOV EAX,EDI *)
(*    1417566: MOV EAX,EDI *)
| 0x15a15e => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015a160: AND EAX,0xffffff *)
(*    1417568: AND EAX,0xffffff *)
| 0x15a160 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xffffff 32))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015a165: RET *)
(*    1417573: RET *)
| 0x15a165 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx inet_lnaof_amd64.
Proof. Picinae_typecheck. Qed.
