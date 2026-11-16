(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strrchr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strrchr_armv8 : program := fun _ a => match a with

(* 0x0015f228: stp x29,x30,[sp, #-0x30]! *)
(*    1438248: stp x29,x30,[sp, #-0x30]! *)
| 0x15f228 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f22c: mov x29,sp *)
(*    1438252: mov x29,sp *)
| 0x15f22c => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f230: str x19,[sp, #0x10] *)
(*    1438256: str x19,[sp, #0x10] *)
| 0x15f230 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015f234: mov x19,x0 *)
(*    1438260: mov x19,x0 *)
| 0x15f234 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f238: str w1,[sp, #0x2c] *)
(*    1438264: str w1,[sp, #0x2c] *)
| 0x15f238 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_SP) (Word 0x2c 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x0015f23c: bl 0x0015efa8 *)
(*    1438268: bl 0x0015efa8 *)
| 0x15f23c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f23c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15efa8 64)
)

(* 0x0015f240: ldr w1,[sp, #0x2c] *)
(*    1438272: ldr w1,[sp, #0x2c] *)
| 0x15f240 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_SP) (Word 0x2c 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015f244: add x2,x0,#0x1 *)
(*    1438276: add x2,x0,#0x1 *)
| 0x15f244 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015f248: mov x0,x19 *)
(*    1438280: mov x0,x19 *)
| 0x15f248 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015f24c: ldr x19,[sp, #0x10] *)
(*    1438284: ldr x19,[sp, #0x10] *)
| 0x15f24c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f250: ldp x29,x30,[sp], #0x30 *)
(*    1438288: ldp x29,x30,[sp], #0x30 *)
| 0x15f250 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f254: b 0x0015e83c *)
(*    1438292: b 0x0015e83c *)
| 0x15f254 => Some (4,
	Jmp (Word 0x15e83c 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx strrchr_armv8.
Proof. Picinae_typecheck. Qed.
