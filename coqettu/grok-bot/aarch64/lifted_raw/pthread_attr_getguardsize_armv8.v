(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_getguardsize
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_getguardsize_armv8 : program := fun _ a => match a with

(* 0x00160fd0: ldr x0,[x0, #0x8] *)
(*    1445840: ldr x0,[x0, #0x8] *)
| 0x160fd0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00160fd4: str x0,[x1] *)
(*    1445844: str x0,[x1] *)
| 0x160fd4 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00160fd8: mov w0,#0x0 *)
(*    1445848: mov w0,#0x0 *)
| 0x160fd8 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00160fdc: ret *)
(*    1445852: ret *)
| 0x160fdc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_getguardsize_armv8.
Proof. Picinae_typecheck. Qed.
