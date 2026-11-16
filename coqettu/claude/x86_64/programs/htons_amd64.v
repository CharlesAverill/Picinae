(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: htons
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition htons_amd64 : program := fun _ a => match a with

(* 0x00159dec: MOV EAX,EDI *)
(*    1416684: MOV EAX,EDI *)
| 0x159dec => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00159dee: ROL AX,0x8 *)
(*    1416686: ROL AX,0x8 *)
| 0x159dee => Some (4,
	Move (V_TEMP 0x62a80) (BinOp OP_AND (Word 0x8 32) (Word 0xf 32)) $;
	Move (V_TEMP 0x62b00) (BinOp OP_LSHIFT (Extract 15 0 (Var R_RAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x62a80)))) $;
	Move (V_TEMP 0x62b80) (BinOp OP_MINUS (Word 0x10 32) (Var (V_TEMP 0x62a80))) $;
	Move (V_TEMP 0x62c00) (BinOp OP_RSHIFT (Extract 15 0 (Var R_RAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x62b80)))) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Var (V_TEMP 0x62b00)) (Var (V_TEMP 0x62c00)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFFFFFF0000 64))) $;
	Move (V_TEMP 0x62d00) (BinOp OP_AND (Word 0x8 8) (Word 0x1f 8)) $;
	Move (V_TEMP 0x2d300) (BinOp OP_NEQ (Var (V_TEMP 0x62d00)) (Word 0x0 8)) $;
	Move (V_TEMP 0x2d380) (BinOp OP_AND (Extract 15 0 (Var R_RAX)) (Word 0x1 16)) $;
	Move (V_TEMP 0x2d480) (BinOp OP_NEQ (Var (V_TEMP 0x2d380)) (Word 0x0 16)) $;
	Move (V_TEMP 0x2d500) (UnOp OP_NOT (Var (V_TEMP 0x2d300))) $;
	Move (V_TEMP 0x2d580) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2d500)) (Var R_CF))) $;
	Move (V_TEMP 0x2d600) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2d300)) (Var (V_TEMP 0x2d480)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2d580))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2d600)))))) $;
	Move (V_TEMP 0x2d780) (BinOp OP_EQ (Var (V_TEMP 0x62d00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2d800) (BinOp OP_SLT (Extract 15 0 (Var R_RAX)) (Word 0x0 16)) $;
	Move (V_TEMP 0x2d900) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x2d800)))) $;
	Move (V_TEMP 0x2d980) (UnOp OP_NOT (Var (V_TEMP 0x2d780))) $;
	Move (V_TEMP 0x2da00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2d980)) (Var R_OF))) $;
	Move (V_TEMP 0x2da80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x2d780)) (Cast CAST_LOW 1 (Var (V_TEMP 0x2d900))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x2da00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x2da80))))))
)

(* 0x00159df2: RET *)
(*    1416690: RET *)
| 0x159df2 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx htons_amd64.
Proof. Picinae_typecheck. Qed.
