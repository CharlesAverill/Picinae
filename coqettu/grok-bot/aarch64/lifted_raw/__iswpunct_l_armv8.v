(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: iswpunct_l
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __iswpunct_l_armv8 : program := fun _ a => match a with

(* 0x0011f20c: b 0x0011f1cc *)
(*    1176076: b 0x0011f1cc *)
| 0x11f20c => Some (4,
	Jmp (Word 0x11f1cc 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __iswpunct_l_armv8.
Proof. Picinae_typecheck. Qed.
