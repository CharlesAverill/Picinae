(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: bzero
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition bzero_armv8 : program := fun _ a => match a with

(* 0x0015e0fc: mov x2,x1 *)
(*    1433852: mov x2,x1 *)
| 0x15e0fc => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0015e100: mov w1,#0x0 *)
(*    1433856: mov w1,#0x0 *)
| 0x15e100 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015e104: b 0x00118400 *)
(*    1433860: b 0x00118400 *)
| 0x15e104 => Some (4,
	Jmp (Word 0x118400 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx bzero_armv8.
Proof. Picinae_typecheck. Qed.
