(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcscoll_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcscoll_l_amd64 : program := fun _ a => match a with

(* 0x0014642d: JMP 0x00134b20 *)
(*    1336365: JMP 0x00134b20 *)
| 0x14642d => Some (5,
	Jmp (Word 0x134b20 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx wcscoll_l_amd64.
Proof. Picinae_typecheck. Qed.
