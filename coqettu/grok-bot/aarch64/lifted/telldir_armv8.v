(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: telldir
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition telldir_armv8 : program := fun _ a => match a with

(* 0x0011faa4: ldr x0,[x0] *)
(*    1178276: ldr x0,[x0] *)
| 0x11faa4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0011faa8: ret *)
(*    1178280: ret *)
| 0x11faa8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx telldir_armv8.
Proof. Picinae_typecheck. Qed.
