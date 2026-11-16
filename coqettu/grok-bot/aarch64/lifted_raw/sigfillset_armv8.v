(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: sigfillset
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition sigfillset_armv8 : program := fun _ a => match a with

(* 0x00152228: orr x1,xzr,#-0x380000001 *)
(*    1385000: orr x1,xzr,#-0x380000001 *)
| 0x152228 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X1 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfffffffc7fffffff 64))
)

(* 0x0015222c: str x1,[x0] *)
(*    1385004: str x1,[x0] *)
| 0x15222c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x00152230: mov w0,#0x0 *)
(*    1385008: mov w0,#0x0 *)
| 0x152230 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00152234: ret *)
(*    1385012: ret *)
| 0x152234 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx sigfillset_armv8.
Proof. Picinae_typecheck. Qed.
