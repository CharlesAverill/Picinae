(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strcoll_l
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __strcoll_l_armv8 : program := fun _ a => match a with

(* 0x00128060: b 0x0015eca4 *)
(*    1212512: b 0x0015eca4 *)
| 0x128060 => Some (4,
	Jmp (Word 0x15eca4 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __strcoll_l_armv8.
Proof. Picinae_typecheck. Qed.
