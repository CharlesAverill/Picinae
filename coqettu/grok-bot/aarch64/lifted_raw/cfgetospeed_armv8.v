(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: cfgetospeed
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfgetospeed_armv8 : program := fun _ a => match a with

(* 0x001605a8: ldr w1,[x0, #0x8] *)
(*    1443240: ldr w1,[x0, #0x8] *)
| 0x1605a8 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x001605ac: mov w0,#0x100f *)
(*    1443244: mov w0,#0x100f *)
| 0x1605ac => Some (4,
	Move R_X0 (Word 0x100f 64)
)

(* 0x001605b0: and w0,w1,w0 *)
(*    1443248: and w0,w1,w0 *)
| 0x1605b0 => Some (4,
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x001605b4: ret *)
(*    1443252: ret *)
| 0x1605b4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx cfgetospeed_armv8.
Proof. Picinae_typecheck. Qed.
