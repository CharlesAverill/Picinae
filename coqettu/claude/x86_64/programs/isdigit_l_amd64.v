(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: isdigit_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition isdigit_l_amd64 : program := fun _ a => match a with

(* 0x00141605: JMP 0x001415f9 *)
(*    1316357: JMP 0x001415f9 *)
| 0x141605 => Some (5,
	Jmp (Word 0x1415f9 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx isdigit_l_amd64.
Proof. Picinae_typecheck. Qed.
