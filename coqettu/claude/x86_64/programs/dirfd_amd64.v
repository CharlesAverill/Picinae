(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: dirfd
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition dirfd_amd64 : program := fun _ a => match a with

(* 0x00141c0f: MOV EAX,dword ptr [RDI + 0x8] *)
(*    1317903: MOV EAX,dword ptr [RDI + 0x8] *)
| 0x141c0f => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00141c12: RET *)
(*    1317906: RET *)
| 0x141c12 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx dirfd_amd64.
Proof. Picinae_typecheck. Qed.
