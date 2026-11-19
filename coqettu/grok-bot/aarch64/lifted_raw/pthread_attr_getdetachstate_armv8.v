(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_getdetachstate
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_getdetachstate_armv8 : program := fun _ a => match a with

(* 0x00160fc0: ldr w0,[x0, #0x18] *)
(*    1445824: ldr w0,[x0, #0x18] *)
| 0x160fc0 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x18 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00160fc4: str w0,[x1] *)
(*    1445828: str w0,[x1] *)
| 0x160fc4 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X0))) LittleE 4)
)

(* 0x00160fc8: mov w0,#0x0 *)
(*    1445832: mov w0,#0x0 *)
| 0x160fc8 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00160fcc: ret *)
(*    1445836: ret *)
| 0x160fcc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_getdetachstate_armv8.
Proof. Picinae_typecheck. Qed.
