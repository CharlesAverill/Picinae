(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_barrierattr_destroy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_barrierattr_destroy_armv8 : program := fun _ a => match a with

(* 0x00161714: mov w0,#0x0 *)
(*    1447700: mov w0,#0x0 *)
| 0x161714 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161718: ret *)
(*    1447704: ret *)
| 0x161718 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_barrierattr_destroy_armv8.
Proof. Picinae_typecheck. Qed.
