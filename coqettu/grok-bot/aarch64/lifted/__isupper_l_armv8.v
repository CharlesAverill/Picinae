(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: isupper_l
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __isupper_l_armv8 : program := fun _ a => match a with

(* 0x0011ef10: b 0x0011ef00 *)
(*    1175312: b 0x0011ef00 *)
| 0x11ef10 => Some (4,
	Jmp (Word 0x11ef00 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __isupper_l_armv8.
Proof. Picinae_typecheck. Qed.
