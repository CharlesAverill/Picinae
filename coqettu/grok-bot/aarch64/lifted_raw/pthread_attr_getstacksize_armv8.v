(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_getstacksize
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_getstacksize_armv8 : program := fun _ a => match a with

(* 0x00161044: ldr x0,[x0] *)
(*    1445956: ldr x0,[x0] *)
| 0x161044 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00161048: str x0,[x1] *)
(*    1445960: str x0,[x1] *)
| 0x161048 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0016104c: mov w0,#0x0 *)
(*    1445964: mov w0,#0x0 *)
| 0x16104c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161050: ret *)
(*    1445968: ret *)
| 0x161050 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_getstacksize_armv8.
Proof. Picinae_typecheck. Qed.
