(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: sigorset
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition sigorset_armv8 : program := fun _ a => match a with

(* 0x001523ac: ldr x1,[x1] *)
(*    1385388: ldr x1,[x1] *)
| 0x1523ac => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x001523b0: ldr x2,[x2] *)
(*    1385392: ldr x2,[x2] *)
| 0x1523b0 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x001523b4: orr x1,x1,x2 *)
(*    1385396: orr x1,x1,x2 *)
| 0x1523b4 => Some (4,
	Move R_X1 (BinOp OP_OR (Var R_X1) (Var R_X2))
)

(* 0x001523b8: str x1,[x0] *)
(*    1385400: str x1,[x0] *)
| 0x1523b8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x001523bc: mov w0,#0x0 *)
(*    1385404: mov w0,#0x0 *)
| 0x1523bc => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001523c0: ret *)
(*    1385408: ret *)
| 0x1523c0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx sigorset_armv8.
Proof. Picinae_typecheck. Qed.
