(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: insque
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition insque_armv8 : program := fun _ a => match a with

(* 0x001513fc: cbz x1,0x0015141c *)
(*    1381372: cbz x1,0x0015141c *)
| 0x1513fc => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15141c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00151400: ldr x2,[x1] *)
(*    1381376: ldr x2,[x1] *)
| 0x151400 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151404: stp x2,x1,[x0] *)
(*    1381380: stp x2,x1,[x0] *)
| 0x151404 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X2) $;
	Move (V_TEMP 0x39f80) (Var R_X1) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151408: str x0,[x1] *)
(*    1381384: str x0,[x1] *)
| 0x151408 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0015140c: ldr x1,[x0] *)
(*    1381388: ldr x1,[x0] *)
| 0x15140c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00151410: cbz x1,0x00151418 *)
(*    1381392: cbz x1,0x00151418 *)
| 0x151410 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x151418 64)
	) (* else *) (
		Nop
	)
)

(* 0x00151414: str x0,[x1, #0x8] *)
(*    1381396: str x0,[x1, #0x8] *)
| 0x151414 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00151418: ret *)
(*    1381400: ret *)
| 0x151418 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015141c: stp xzr,xzr,[x0] *)
(*    1381404: stp xzr,xzr,[x0] *)
| 0x15141c => Some (4,
	Move (V_TEMP 0x500) (Word 0x0 64) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move (V_TEMP 0x39f00) (Var (V_TEMP 0x600)) $;
	Move (V_TEMP 0x39f80) (Var (V_TEMP 0x500)) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00151420: b 0x00151418 *)
(*    1381408: b 0x00151418 *)
| 0x151420 => Some (4,
	Jmp (Word 0x151418 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx insque_armv8.
Proof. Picinae_typecheck. Qed.
