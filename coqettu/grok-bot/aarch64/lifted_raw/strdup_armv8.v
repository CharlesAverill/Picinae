(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strdup
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strdup_armv8 : program := fun _ a => match a with

(* 0x0015eda0: stp x29,x30,[sp, #-0x30]! *)
(*    1437088: stp x29,x30,[sp, #-0x30]! *)
| 0x15eda0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015eda4: mov x29,sp *)
(*    1437092: mov x29,sp *)
| 0x15eda4 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015eda8: str x19,[sp, #0x10] *)
(*    1437096: str x19,[sp, #0x10] *)
| 0x15eda8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015edac: mov x19,x0 *)
(*    1437100: mov x19,x0 *)
| 0x15edac => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015edb0: bl 0x0015efa8 *)
(*    1437104: bl 0x0015efa8 *)
| 0x15edb0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15edb0 64) (Word 0x4 64)) $;
	Jmp (Word 0x15efa8 64)
)

(* 0x0015edb4: add x2,x0,#0x1 *)
(*    1437108: add x2,x0,#0x1 *)
| 0x15edb4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015edb8: mov x0,x2 *)
(*    1437112: mov x0,x2 *)
| 0x15edb8 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015edbc: str x2,[sp, #0x28] *)
(*    1437116: str x2,[sp, #0x28] *)
| 0x15edbc => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x0015edc0: bl 0x001135d0 *)
(*    1437120: bl 0x001135d0 *)
| 0x15edc0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15edc0 64) (Word 0x4 64)) $;
	Jmp (Word 0x1135d0 64)
)

(* 0x0015edc4: cbz x0,0x0015eddc *)
(*    1437124: cbz x0,0x0015eddc *)
| 0x15edc4 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15eddc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015edc8: ldr x2,[sp, #0x28] *)
(*    1437128: ldr x2,[sp, #0x28] *)
| 0x15edc8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015edcc: mov x1,x19 *)
(*    1437132: mov x1,x19 *)
| 0x15edcc => Some (4,
	Move R_X1 (Var R_X19)
)

(* 0x0015edd0: ldr x19,[sp, #0x10] *)
(*    1437136: ldr x19,[sp, #0x10] *)
| 0x15edd0 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015edd4: ldp x29,x30,[sp], #0x30 *)
(*    1437140: ldp x29,x30,[sp], #0x30 *)
| 0x15edd4 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015edd8: b 0x00118270 *)
(*    1437144: b 0x00118270 *)
| 0x15edd8 => Some (4,
	Jmp (Word 0x118270 64)
)

(* 0x0015eddc: ldr x19,[sp, #0x10] *)
(*    1437148: ldr x19,[sp, #0x10] *)
| 0x15eddc => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ede0: ldp x29,x30,[sp], #0x30 *)
(*    1437152: ldp x29,x30,[sp], #0x30 *)
| 0x15ede0 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ede4: ret *)
(*    1437156: ret *)
| 0x15ede4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strdup_armv8.
Proof. Picinae_typecheck. Qed.
