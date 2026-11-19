(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: mtx_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition mtx_init_armv8 : program := fun _ a => match a with

(* 0x00160d88: stp xzr,xzr,[x0] *)
(*    1445256: stp xzr,xzr,[x0] *)
| 0x160d88 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00160d8c: and w1,w1,#0x1 *)
(*    1445260: and w1,w1,#0x1 *)
| 0x160d8c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0x1 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00160d90: str w1,[x0] *)
(*    1445264: str w1,[x0] *)
| 0x160d90 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00160d94: stp xzr,xzr,[x0, #0x10] *)
(*    1445268: stp xzr,xzr,[x0, #0x10] *)
| 0x160d94 => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00160d98: str xzr,[x0, #0x20] *)
(*    1445272: str xzr,[x0, #0x20] *)
| 0x160d98 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x00160d9c: mov w0,#0x0 *)
(*    1445276: mov w0,#0x0 *)
| 0x160d9c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00160da0: ret *)
(*    1445280: ret *)
| 0x160da0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx mtx_init_armv8.
Proof. Picinae_typecheck. Qed.
