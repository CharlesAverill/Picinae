(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: setjmp
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition setjmp_amd64 : program := fun _ a => match a with

(* 0x0015eeed: MOV qword ptr [RDI],RBX *)
(*    1437421: MOV qword ptr [RDI],RBX *)
| 0x15eeed => Some (3,
	Move (V_TEMP 0x6a80) (Var R_RBX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015eef0: MOV qword ptr [RDI + 0x8],RBP *)
(*    1437424: MOV qword ptr [RDI + 0x8],RBP *)
| 0x15eef0 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6a80) (Var R_RBP) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015eef4: MOV qword ptr [RDI + 0x10],R12 *)
(*    1437428: MOV qword ptr [RDI + 0x10],R12 *)
| 0x15eef4 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6a80) (Var R_R12) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015eef8: MOV qword ptr [RDI + 0x18],R13 *)
(*    1437432: MOV qword ptr [RDI + 0x18],R13 *)
| 0x15eef8 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x18 64)) $;
	Move (V_TEMP 0x6a80) (Var R_R13) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015eefc: MOV qword ptr [RDI + 0x20],R14 *)
(*    1437436: MOV qword ptr [RDI + 0x20],R14 *)
| 0x15eefc => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6a80) (Var R_R14) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015ef00: MOV qword ptr [RDI + 0x28],R15 *)
(*    1437440: MOV qword ptr [RDI + 0x28],R15 *)
| 0x15ef00 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x28 64)) $;
	Move (V_TEMP 0x6a80) (Var R_R15) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015ef04: LEA RDX,[RSP + 0x8] *)
(*    1437444: LEA RDX,[RSP + 0x8] *)
| 0x15ef04 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move R_RDX (Var (V_TEMP 0x4e80))
)

(* 0x0015ef09: MOV qword ptr [RDI + 0x30],RDX *)
(*    1437449: MOV qword ptr [RDI + 0x30],RDX *)
| 0x15ef09 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015ef0d: MOV RDX,qword ptr [RSP] *)
(*    1437453: MOV RDX,qword ptr [RSP] *)
| 0x15ef0d => Some (4,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0x11f00))
)

(* 0x0015ef11: MOV qword ptr [RDI + 0x38],RDX *)
(*    1437457: MOV qword ptr [RDI + 0x38],RDX *)
| 0x15ef11 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x38 64)) $;
	Move (V_TEMP 0x6a80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015ef15: XOR EAX,EAX *)
(*    1437461: XOR EAX,EAX *)
| 0x15ef15 => Some (2,
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

(* 0x0015ef17: RET *)
(*    1437463: RET *)
| 0x15ef17 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx setjmp_amd64.
Proof. Picinae_typecheck. Qed.
