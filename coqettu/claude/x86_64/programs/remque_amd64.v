(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: remque
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition remque_amd64 : program := fun _ a => match a with

(* 0x0015e979: MOV RAX,qword ptr [RDI] *)
(*    1436025: MOV RAX,qword ptr [RDI] *)
| 0x15e979 => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015e97c: TEST RAX,RAX *)
(*    1436028: TEST RAX,RAX *)
| 0x15e97c => Some (3,
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

(* 0x0015e97f: JZ 0x0015e989 *)
(*    1436031: JZ 0x0015e989 *)
| 0x15e97f => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15e989 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e981: MOV RDX,qword ptr [RDI + 0x8] *)
(*    1436033: MOV RDX,qword ptr [RDI + 0x8] *)
| 0x15e981 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0x11f00))
)

(* 0x0015e985: MOV qword ptr [RAX + 0x8],RDX *)
(*    1436037: MOV qword ptr [RAX + 0x8],RDX *)
| 0x15e985 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x8 64)) $;
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015e989: MOV RAX,qword ptr [RDI + 0x8] *)
(*    1436041: MOV RAX,qword ptr [RDI + 0x8] *)
| 0x15e989 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015e98d: TEST RAX,RAX *)
(*    1436045: TEST RAX,RAX *)
| 0x15e98d => Some (3,
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

(* 0x0015e990: JZ 0x0015e998 *)
(*    1436048: JZ 0x0015e998 *)
| 0x15e990 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15e998 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e992: MOV RDX,qword ptr [RDI] *)
(*    1436050: MOV RDX,qword ptr [RDI] *)
| 0x15e992 => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0x11f00))
)

(* 0x0015e995: MOV qword ptr [RAX],RDX *)
(*    1436053: MOV qword ptr [RAX],RDX *)
| 0x15e995 => Some (3,
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015e998: RET *)
(*    1436056: RET *)
| 0x15e998 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx remque_amd64.
Proof. Picinae_typecheck. Qed.
