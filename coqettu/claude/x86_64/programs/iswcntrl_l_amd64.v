(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: iswcntrl_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswcntrl_l_amd64 : program := fun _ a => match a with

(* 0x0014173a: JMP 0x00141708 *)
(*    1316666: JMP 0x00141708 *)
| 0x14173a => Some (5,
	Jmp (Word 0x141708 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx iswcntrl_l_amd64.
Proof. Picinae_typecheck. Qed.
