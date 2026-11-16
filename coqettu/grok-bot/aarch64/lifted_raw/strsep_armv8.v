(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strsep
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strsep_armv8 : program := fun _ a => match a with

(* 0x0015f258: ldr x2,[x0] *)
(*    1438296: ldr x2,[x0] *)
| 0x15f258 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015f25c: cbz x2,0x0015f2a4 *)
(*    1438300: cbz x2,0x0015f2a4 *)
| 0x15f25c => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15f2a4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f260: stp x29,x30,[sp, #-0x20]! *)
(*    1438304: stp x29,x30,[sp, #-0x20]! *)
| 0x15f260 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f264: mov x3,x0 *)
(*    1438308: mov x3,x0 *)
| 0x15f264 => Some (4,
	Move R_X3 (Var R_X0)
)

(* 0x0015f268: mov x0,x2 *)
(*    1438312: mov x0,x2 *)
| 0x15f268 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f26c: mov x29,sp *)
(*    1438316: mov x29,sp *)
| 0x15f26c => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f270: stp x2,x3,[sp, #0x10] *)
(*    1438320: stp x2,x3,[sp, #0x10] *)
| 0x15f270 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X2) $;
	Move (V_TEMP 0x39f80) (Var R_X3) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f274: bl 0x0015ecf0 *)
(*    1438324: bl 0x0015ecf0 *)
| 0x15f274 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f274 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ecf0 64)
)

(* 0x0015f278: mov x1,#0x0 *)
(*    1438328: mov x1,#0x0 *)
| 0x15f278 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015f27c: ldp x2,x3,[sp, #0x10] *)
(*    1438332: ldp x2,x3,[sp, #0x10] *)
| 0x15f27c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X2 (Var (V_TEMP 0x24180)) $;
	Move R_X3 (Var (V_TEMP 0x24300))
)

(* 0x0015f280: ldrb w4,[x2, x0, LSL ] *)
(*    1438336: ldrb w4,[x2, x0, LSL ] *)
| 0x15f280 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015f284: add x5,x2,x0 *)
(*    1438340: add x5,x2,x0 *)
| 0x15f284 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x12080))
)

(* 0x0015f288: cbz w4,0x0015f294 *)
(*    1438344: cbz w4,0x0015f294 *)
| 0x15f288 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X4)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f294 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f28c: add x1,x5,#0x1 *)
(*    1438348: add x1,x5,#0x1 *)
| 0x15f28c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015f290: strb wzr,[x2, x0, LSL ] *)
(*    1438352: strb wzr,[x2, x0, LSL ] *)
| 0x15f290 => Some (4,
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move (V_TEMP 0x3a400) (Var (V_TEMP 0x300)) $;
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a400)))) LittleE 1)
)

(* 0x0015f294: str x1,[x3] *)
(*    1438356: str x1,[x3] *)
| 0x15f294 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x0015f298: mov x0,x2 *)
(*    1438360: mov x0,x2 *)
| 0x15f298 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f29c: ldp x29,x30,[sp], #0x20 *)
(*    1438364: ldp x29,x30,[sp], #0x20 *)
| 0x15f29c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f2a0: ret *)
(*    1438368: ret *)
| 0x15f2a0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015f2a4: mov x0,x2 *)
(*    1438372: mov x0,x2 *)
| 0x15f2a4 => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015f2a8: ret *)
(*    1438376: ret *)
| 0x15f2a8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strsep_armv8.
Proof. Picinae_typecheck. Qed.
