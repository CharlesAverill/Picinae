(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: div
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition div_amd64 : program := fun _ a => match a with

(* 0x00164ef8: MOV EAX,EDI *)
(*    1462008: MOV EAX,EDI *)
| 0x164ef8 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00164efa: CDQ *)
(*    1462010: CDQ *)
| 0x164efa => Some (1,
	Move (V_TEMP 0x3d600) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x3d600)) (Word 32 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00164efb: IDIV ESI *)
(*    1462011: IDIV ESI *)
| 0x164efb => Some (2,
	Move (V_TEMP 0x49600) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move (V_TEMP 0x49680) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x49700) (BinOp OP_LSHIFT (Var (V_TEMP 0x49680)) (Word 0x20 64)) $;
	Move (V_TEMP 0x49780) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49880) (BinOp OP_OR (Var (V_TEMP 0x49700)) (Var (V_TEMP 0x49780))) $;
	Move (V_TEMP 0x49980) (BinOp OP_SDIVIDE (Var (V_TEMP 0x49880)) (Var (V_TEMP 0x49600))) $;
	Move R_RAX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x49980)) (Word 0 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49b00) (BinOp OP_SMOD (Var (V_TEMP 0x49880)) (Var (V_TEMP 0x49600))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x49b00)) (Word 0 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00164efd: SHL RDX,0x20 *)
(*    1462013: SHL RDX,0x20 *)
| 0x164efd => Some (4,
	Move (V_TEMP 0x6a580) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a600) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a580)))) $;
	Move (V_TEMP 0x2e580) (BinOp OP_NEQ (Var (V_TEMP 0x6a580)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2e600) (BinOp OP_MINUS (Var (V_TEMP 0x6a580)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e680) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a600)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e600)))) $;
	Move (V_TEMP 0x2e780) (BinOp OP_SLT (Var (V_TEMP 0x2e680)) (Word 0x0 64)) $;
	Move (V_TEMP 0x2e800) (UnOp OP_NOT (Var (V_TEMP 0x2e580))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e800)) (Var R_CF))) $;
	Move (V_TEMP 0x2e900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2e580)) (Var (V_TEMP 0x2e780)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2e880))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2e900)))))) $;
	Move (V_TEMP 0x2ea80) (BinOp OP_EQ (Var (V_TEMP 0x6a580)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2eb00) (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x2eb00)))) $;
	Move (V_TEMP 0x2ec80) (UnOp OP_NOT (Var (V_TEMP 0x2ea80))) $;
	Move (V_TEMP 0x2ed00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ec80)) (Var R_OF))) $;
	Move (V_TEMP 0x2ed80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2ea80)) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ec00))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ed80)))))) $;
	Move (V_TEMP 0x2c400) (BinOp OP_NEQ (Var (V_TEMP 0x6a580)) (Word 0x0 32)) $;
	Move (V_TEMP 0x2c500) (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c580) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c580)) (Var R_SF))) $;
	Move (V_TEMP 0x2c680) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c500)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c680)))))) $;
	Move (V_TEMP 0x2c800) (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)) $;
	Move (V_TEMP 0x2c880) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c880)) (Var R_ZF))) $;
	Move (V_TEMP 0x2c980) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2c800)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2c980)))))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cb00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var (V_TEMP 0x2cb00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_EQ (Var (V_TEMP 0x2cb80)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2cd00) (UnOp OP_NOT (Var (V_TEMP 0x2c400))) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2cd00)) (Var R_PF))) $;
	Move (V_TEMP 0x2ce00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2c400)) (Var (V_TEMP 0x2cc80)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2cd80))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2ce00))))))
)

(* 0x00164f01: OR RAX,RDX *)
(*    1462017: OR RAX,RDX *)
| 0x164f01 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00164f04: RET *)
(*    1462020: RET *)
| 0x164f04 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx div_amd64.
Proof. Picinae_typecheck. Qed.
