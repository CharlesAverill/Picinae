(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __libc_current_sigrtmax
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __libc_current_sigrtmax_armv8 : program := fun _ a => match a with

(* 0x00152540: mov w0,#0x40 *)
(*    1385792: mov w0,#0x40 *)
| 0x152540 => Some (4,
	Move R_X0 (Word 0x40 64)
)

(* 0x00152544: ret *)
(*    1385796: ret *)
| 0x152544 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx __libc_current_sigrtmax_armv8.
Proof. Picinae_typecheck. Qed.
