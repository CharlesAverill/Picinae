(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: telldir
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition telldir_amd64 : program := fun _ a => match a with

(* 0x00142022: MOV RAX,qword ptr [RDI] *)
(*    1318946: MOV RAX,qword ptr [RDI] *)
| 0x142022 => Some (3,
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x00142025: RET *)
(*    1318949: RET *)
| 0x142025 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx telldir_amd64.
Proof. Picinae_typecheck. Qed.
