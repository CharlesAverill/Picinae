(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: rand
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition rand_amd64 : program := fun _ a => match a with

(* 0x0015c279: MOV RAX,0x5851f42d4c957f2d *)
(*    1426041: MOV RAX,0x5851f42d4c957f2d *)
| 0x15c279 => Some (10,
	Move R_RAX (Word 0x5851f42d4c957f2d 64)
)

(* 0x0015c283: IMUL RAX,qword ptr [0x001a6e78] *)
(*    1426051: IMUL RAX,qword ptr [0x001a6e78] *)
| 0x15c283 => Some (8,
	Move (V_TEMP 0x4b400) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move (V_TEMP 0x4b480) (Cast CAST_SIGNED 128 (Load (Var V_MEM64) (Word 0x1a6e78 64) LittleE 8)) $;
	Move (V_TEMP 0x4b580) (BinOp OP_TIMES (Var (V_TEMP 0x4b400)) (Var (V_TEMP 0x4b480))) $;
	Move R_RAX (BinOp OP_TIMES (Var R_RAX) (Load (Var V_MEM64) (Word 0x1a6e78 64) LittleE 8)) $;
	Move (V_TEMP 0x4b700) (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4b580)) (Word 64 128))) $;
	Move (V_TEMP 0x2d100) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x2d100)) (Var (V_TEMP 0x4b580)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF)))
)

(* 0x0015c28b: ADD RAX,0x1 *)
(*    1426059: ADD RAX,0x1 *)
| 0x15c28b => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Var R_RAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c28f: MOV qword ptr [0x001a6e78],RAX *)
(*    1426063: MOV qword ptr [0x001a6e78],RAX *)
| 0x15c28f => Some (7,
	Move V_MEM64 (Store (Var V_MEM64) (Word 0x1a6e78 64) (Cast CAST_UNSIGNED 64 (Var R_RAX)) LittleE 8)
)

(* 0x0015c296: SHR RAX,0x21 *)
(*    1426070: SHR RAX,0x21 *)
| 0x15c296 => Some (4,
	Move (V_TEMP 0x6e500) (BinOp OP_AND (Word 0x21 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e580) (Var R_RAX) $;
	Move R_RAX (BinOp OP_RSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e500)))) $;
	Move (V_TEMP 0x2f680) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2f700) (BinOp OP_MINUS (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f780) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e580)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f700)))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_NEQ (Var (V_TEMP 0x2f800)) (Word 0x0 64)) $;
	Move (V_TEMP 0x2f980) (UnOp OP_NOT (Var (V_TEMP 0x2f680))) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f980)) (Var R_CF))) $;
	Move (V_TEMP 0x2fa80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2f680)) (Var (V_TEMP 0x2f900)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fa80)))))) $;
	Move (V_TEMP 0x2fc00) (BinOp OP_EQ (Var (V_TEMP 0x6e500)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2fd00) (BinOp OP_SLT (Var (V_TEMP 0x6e580)) (Word 0x0 64)) $;
	Move (V_TEMP 0x2fd80) (UnOp OP_NOT (Var (V_TEMP 0x2fc00))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fd80)) (Var R_OF))) $;
	Move (V_TEMP 0x2fe80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2fc00)) (Var (V_TEMP 0x2fd00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2fe80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6e500)) (Word 0x0 32)) $;
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

(* 0x0015c29a: RET *)
(*    1426074: RET *)
| 0x15c29a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx rand_amd64.
Proof. Picinae_typecheck. Qed.
