(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: cfmakeraw
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfmakeraw_armv8 : program := fun _ a => match a with

(* 0x001605c8: ldr x1,[x0] *)
(*    1443272: ldr x1,[x0] *)
| 0x1605c8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x001605cc: mov x2,#-0x5ec *)
(*    1443276: mov x2,#-0x5ec *)
| 0x1605cc => Some (4,
	Move R_X2 (Word 0xfffffffffffffa14 64)
)

(* 0x001605d0: movk x2,#0xfffe, LSL #32 *)
(*    1443280: movk x2,#0xfffe, LSL #32 *)
| 0x1605d0 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffff0000ffffffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0xfffe00000000 64))
)

(* 0x001605d4: mov w3,#0xffff7fb4 *)
(*    1443284: mov w3,#0xffff7fb4 *)
| 0x1605d4 => Some (4,
	Move R_X3 (Word 0xffff7fb4 64)
)

(* 0x001605d8: and x1,x1,x2 *)
(*    1443288: and x1,x1,x2 *)
| 0x1605d8 => Some (4,
	Move R_X1 (BinOp OP_AND (Var R_X1) (Var R_X2))
)

(* 0x001605dc: str x1,[x0] *)
(*    1443292: str x1,[x0] *)
| 0x1605dc => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x001605e0: ldp w1,w2,[x0, #0x8] *)
(*    1443296: ldp w1,w2,[x0, #0x8] *)
| 0x1605e0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 0x23d80) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 4) $;
	Move (V_TEMP 0x23e80) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x23d80))) $;
	Move (V_TEMP 0x23f00) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x4 64)) $;
	Move (V_TEMP 0x23f80) (Load (Var V_MEM64) (Var (V_TEMP 0x23f00)) LittleE 4) $;
	Move (V_TEMP 0x24080) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x23f80))) $;
	Move R_X1 (Var (V_TEMP 0x23e80)) $;
	Move R_X2 (Var (V_TEMP 0x24080))
)

(* 0x001605e4: and w2,w2,w3 *)
(*    1443300: and w2,w2,w3 *)
| 0x1605e4 => Some (4,
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x001605e8: mov w3,#0xfffffecf *)
(*    1443304: mov w3,#0xfffffecf *)
| 0x1605e8 => Some (4,
	Move R_X3 (Word 0xfffffecf 64)
)

(* 0x001605ec: and w1,w1,w3 *)
(*    1443308: and w1,w1,w3 *)
| 0x1605ec => Some (4,
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X3))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x001605f0: orr w1,w1,#0x30 *)
(*    1443312: orr w1,w1,#0x30 *)
| 0x1605f0 => Some (4,
	Move (V_TEMP 0x2cd00) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Word 0x30 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2cd00)))
)

(* 0x001605f4: stp w1,w2,[x0, #0x8] *)
(*    1443316: stp w1,w2,[x0, #0x8] *)
| 0x1605f4 => Some (4,
	Move (V_TEMP 0x39d80) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x39e00) (Extract 31 0 (Var R_X2)) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x39d80))) LittleE 4) $;
	Move (V_TEMP 0x39e80) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x4 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x39e80)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x39e00))) LittleE 4)
)

(* 0x001605f8: mov w1,#0x100 *)
(*    1443320: mov w1,#0x100 *)
| 0x1605f8 => Some (4,
	Move R_X1 (Word 0x100 64)
)

(* 0x001605fc: strh w1,[x0, #0x16] *)
(*    1443324: strh w1,[x0, #0x16] *)
| 0x1605fc => Some (4,
	Move (V_TEMP 0x5f00) (BinOp OP_PLUS (Var R_X0) (Word 0x16 64)) $;
	Move (V_TEMP 0x3a480) (Extract 31 0 (Var R_X1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5f00)) (Cast CAST_UNSIGNED 16 (Extract 15 0 (Var (V_TEMP 0x3a480)))) LittleE 2)
)

(* 0x00160600: ret *)
(*    1443328: ret *)
| 0x160600 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx cfmakeraw_armv8.
Proof. Picinae_typecheck. Qed.
