(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: posix_spawnattr_init
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_init_amd64 : program := fun _ a => match a with

(* 0x0015cd80: XOR EAX,EAX *)
(*    1428864: XOR EAX,EAX *)
| 0x15cd80 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015cd82: MOV ECX,0x2a *)
(*    1428866: MOV ECX,0x2a *)
| 0x15cd82 => Some (5,
	Move R_RCX (Word 0x2a 64)
)

(* 0x0015cd87: STOSQ.REP RDI *)
(*    1428871: STOSQ.REP RDI *)
| 0x15cd87 => Some (3,
	Move (V_TEMP 0x13400) (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13400))) (
		Jmp (Word 0x15cd8a 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11a80) (Var R_RDI) $;
	Move (V_TEMP 0x11b00) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11b80) (Cast CAST_UNSIGNED 64 (Var R_DF)) $;
	Move (V_TEMP 0x11c00) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 0x11b80))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 0x11b00)) (Var (V_TEMP 0x11c00))) $;
	Move (V_TEMP 0x11d00) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x11a80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d00))) LittleE 8) $;
	Jmp (Word 0x15cd87 64)
)

(* 0x0015cd8a: RET *)
(*    1428874: RET *)
| 0x15cd8a => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx posix_spawnattr_init_amd64.
Proof. Picinae_typecheck. Qed.
