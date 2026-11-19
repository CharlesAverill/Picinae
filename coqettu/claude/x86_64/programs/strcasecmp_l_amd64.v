(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strcasecmp_l
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcasecmp_l_amd64 : program := fun _ a => match a with

(* 0x00165944: JMP 0x001658e8 *)
(*    1464644: JMP 0x001658e8 *)
| 0x165944 => Some (5,
	Jmp (Word 0x1658e8 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx strcasecmp_l_amd64.
Proof. Picinae_typecheck. Qed.
