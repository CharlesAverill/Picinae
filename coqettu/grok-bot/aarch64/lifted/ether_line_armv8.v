(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ether_line
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ether_line_armv8 : program := fun _ a => match a with

(* 0x0014021c: mov w0,#0xffffffff *)
(*    1311260: mov w0,#0xffffffff *)
| 0x14021c => Some (4,
	Move R_X0 (Word 0xffffffff 64)
)

(* 0x00140220: ret *)
(*    1311264: ret *)
| 0x140220 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ether_line_armv8.
Proof. Picinae_typecheck. Qed.
