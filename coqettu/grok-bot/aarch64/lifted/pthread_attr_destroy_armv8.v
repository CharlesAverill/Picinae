(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_destroy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_destroy_armv8 : program := fun _ a => match a with

(* 0x00160fb8: mov w0,#0x0 *)
(*    1445816: mov w0,#0x0 *)
| 0x160fb8 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00160fbc: ret *)
(*    1445820: ret *)
| 0x160fbc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_destroy_armv8.
Proof. Picinae_typecheck. Qed.
