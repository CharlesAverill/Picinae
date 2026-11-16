(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: srand
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition srand_amd64 : program := fun _ a => match a with

(* 0x0015c26e: LEA EAX,[RDI + -0x1] *)
(*    1426030: LEA EAX,[RDI + -0x1] *)
| 0x15c26e => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffff 64)) $;
	Move R_RAX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4780)) (Word 0 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0015c271: MOV qword ptr [0x001a6e78],RAX *)
(*    1426033: MOV qword ptr [0x001a6e78],RAX *)
| 0x15c271 => Some (7,
	Move V_MEM64 (Store (Var V_MEM64) (Word 0x1a6e78 64) (Cast CAST_UNSIGNED 64 (Var R_RAX)) LittleE 8)
)

(* 0x0015c278: RET *)
(*    1426040: RET *)
| 0x15c278 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx srand_amd64.
Proof. Picinae_typecheck. Qed.
