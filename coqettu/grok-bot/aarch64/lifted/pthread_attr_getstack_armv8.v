(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_getstack
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_getstack_armv8 : program := fun _ a => match a with

(* 0x0016101c: ldr x3,[x0, #0x10] *)
(*    1445916: ldr x3,[x0, #0x10] *)
| 0x16101c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00161020: cbz x3,0x0016103c *)
(*    1445920: cbz x3,0x0016103c *)
| 0x161020 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x16103c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161024: ldr x0,[x0] *)
(*    1445924: ldr x0,[x0] *)
| 0x161024 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00161028: str x0,[x2] *)
(*    1445928: str x0,[x2] *)
| 0x161028 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0016102c: sub x3,x3,x0 *)
(*    1445932: sub x3,x3,x0 *)
| 0x16102c => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Var R_X0))
)

(* 0x00161030: mov w0,#0x0 *)
(*    1445936: mov w0,#0x0 *)
| 0x161030 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161034: str x3,[x1] *)
(*    1445940: str x3,[x1] *)
| 0x161034 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X3)) LittleE 8)
)

(* 0x00161038: ret *)
(*    1445944: ret *)
| 0x161038 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0016103c: mov w0,#0x16 *)
(*    1445948: mov w0,#0x16 *)
| 0x16103c => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00161040: b 0x00161038 *)
(*    1445952: b 0x00161038 *)
| 0x161040 => Some (4,
	Jmp (Word 0x161038 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_getstack_armv8.
Proof. Picinae_typecheck. Qed.
