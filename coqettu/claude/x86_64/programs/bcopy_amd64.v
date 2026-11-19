(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: bcopy
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition bcopy_amd64 : program := fun _ a => match a with

(* 0x001658a5: MOV RAX,RDI *)
(*    1464485: MOV RAX,RDI *)
| 0x1658a5 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001658a8: MOV RDI,RSI *)
(*    1464488: MOV RDI,RSI *)
| 0x1658a8 => Some (3,
	Move R_RDI (Var R_RSI)
)

(* 0x001658ab: MOV RSI,RAX *)
(*    1464491: MOV RSI,RAX *)
| 0x1658ab => Some (3,
	Move R_RSI (Var R_RAX)
)

(* 0x001658ae: JMP 0x00134680 *)
(*    1464494: JMP 0x00134680 *)
| 0x1658ae => Some (5,
	Jmp (Word 0x134680 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx bcopy_amd64.
Proof. Picinae_typecheck. Qed.
