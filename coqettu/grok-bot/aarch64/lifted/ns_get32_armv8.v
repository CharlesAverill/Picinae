(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ns_get32
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ns_get32_armv8 : program := fun _ a => match a with

(* 0x00143f5c: ldr w0,[x0] *)
(*    1326940: ldr w0,[x0] *)
| 0x143f5c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00143f60: rev w0,w0 *)
(*    1326944: rev w0,w0 *)
| 0x143f60 => Some (4,
	Move (V_TEMP 0x2f800) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x2f900) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f880)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f980) (BinOp OP_AND (Var (V_TEMP 0x2f800)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x2fa00) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f980)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2f900)) (Var (V_TEMP 0x2fa00))) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_RSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_LSHIFT (Var (V_TEMP 0x2f800)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2f800) (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))
)

(* 0x00143f64: ret *)
(*    1326948: ret *)
| 0x143f64 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ns_get32_armv8.
Proof. Picinae_typecheck. Qed.
