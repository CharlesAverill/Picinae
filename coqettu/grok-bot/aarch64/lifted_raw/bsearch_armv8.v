(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: bsearch
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition bsearch_armv8 : program := fun _ a => match a with

(* 0x0015d0ec: stp x29,x30,[sp, #-0x50]! *)
(*    1429740: stp x29,x30,[sp, #-0x50]! *)
| 0x15d0ec => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffb0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015d0f0: mov x29,sp *)
(*    1429744: mov x29,sp *)
| 0x15d0f0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015d0f4: stp x19,x20,[sp, #0x10] *)
(*    1429748: stp x19,x20,[sp, #0x10] *)
| 0x15d0f4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015d0f8: mov x19,x2 *)
(*    1429752: mov x19,x2 *)
| 0x15d0f8 => Some (4,
	Move R_X19 (Var R_X2)
)

(* 0x0015d0fc: stp x21,x22,[sp, #0x20] *)
(*    1429756: stp x21,x22,[sp, #0x20] *)
| 0x15d0fc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015d100: mov x22,x1 *)
(*    1429760: mov x22,x1 *)
| 0x15d100 => Some (4,
	Move R_X22 (Var R_X1)
)

(* 0x0015d104: stp x23,x24,[sp, #0x30] *)
(*    1429764: stp x23,x24,[sp, #0x30] *)
| 0x15d104 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X23) $;
	Move (V_TEMP 0x39f80) (Var R_X24) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015d108: mov x24,x0 *)
(*    1429768: mov x24,x0 *)
| 0x15d108 => Some (4,
	Move R_X24 (Var R_X0)
)

(* 0x0015d10c: mov x23,x3 *)
(*    1429772: mov x23,x3 *)
| 0x15d10c => Some (4,
	Move R_X23 (Var R_X3)
)

(* 0x0015d110: str x25,[sp, #0x40] *)
(*    1429776: str x25,[sp, #0x40] *)
| 0x15d110 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X25)) LittleE 8)
)

(* 0x0015d114: mov x25,x4 *)
(*    1429780: mov x25,x4 *)
| 0x15d114 => Some (4,
	Move R_X25 (Var R_X4)
)

(* 0x0015d118: b 0x0015d120 *)
(*    1429784: b 0x0015d120 *)
| 0x15d118 => Some (4,
	Jmp (Word 0x15d120 64)
)

(* 0x0015d11c: mov x19,x20 *)
(*    1429788: mov x19,x20 *)
| 0x15d11c => Some (4,
	Move R_X19 (Var R_X20)
)

(* 0x0015d120: cbz x19,0x0015d150 *)
(*    1429792: cbz x19,0x0015d150 *)
| 0x15d120 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X19) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15d150 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d124: lsr x20,x19,#0x1 *)
(*    1429796: lsr x20,x19,#0x1 *)
| 0x15d124 => Some (4,
	Move R_X20 (BinOp OP_RSHIFT (Var R_X19) (Word 0x1 64))
)

(* 0x0015d128: mov x0,x24 *)
(*    1429800: mov x0,x24 *)
| 0x15d128 => Some (4,
	Move R_X0 (Var R_X24)
)

(* 0x0015d12c: madd x21,x20,x23,x22 *)
(*    1429804: madd x21,x20,x23,x22 *)
| 0x15d12c => Some (4,
	Move (V_TEMP 0x28b00) (BinOp OP_TIMES (Var R_X20) (Var R_X23)) $;
	Move R_X21 (BinOp OP_PLUS (Var R_X22) (Var (V_TEMP 0x28b00)))
)

(* 0x0015d130: mov x1,x21 *)
(*    1429808: mov x1,x21 *)
| 0x15d130 => Some (4,
	Move R_X1 (Var R_X21)
)

(* 0x0015d134: blr x25 *)
(*    1429812: blr x25 *)
| 0x15d134 => Some (4,
	Move R_PC (Var R_X25) $;
	Move R_X30 (BinOp OP_PLUS (Word 0x15d134 64) (Word 0x4 64)) $;
	Jmp (Var R_PC)
)

(* 0x0015d138: tbnz w0,#0x1f,0x0015d11c *)
(*    1429816: tbnz w0,#0x1f,0x0015d11c *)
| 0x15d138 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x15d11c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d13c: cbz w0,0x0015d154 *)
(*    1429820: cbz w0,0x0015d154 *)
| 0x15d13c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15d154 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d140: sub x19,x19,#0x1 *)
(*    1429824: sub x19,x19,#0x1 *)
| 0x15d140 => Some (4,
	Move R_X19 (BinOp OP_MINUS (Var R_X19) (Word 0x1 64))
)

(* 0x0015d144: add x22,x21,x23 *)
(*    1429828: add x22,x21,x23 *)
| 0x15d144 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X23) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) (Var R_X21))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X21) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X21) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X21) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X22 (Var (V_TEMP 0x12080))
)

(* 0x0015d148: sub x19,x19,x20 *)
(*    1429832: sub x19,x19,x20 *)
| 0x15d148 => Some (4,
	Move R_X19 (BinOp OP_MINUS (Var R_X19) (Var R_X20))
)

(* 0x0015d14c: b 0x0015d120 *)
(*    1429836: b 0x0015d120 *)
| 0x15d14c => Some (4,
	Jmp (Word 0x15d120 64)
)

(* 0x0015d150: mov x21,#0x0 *)
(*    1429840: mov x21,#0x0 *)
| 0x15d150 => Some (4,
	Move R_X21 (Word 0x0 64)
)

(* 0x0015d154: ldr x25,[sp, #0x40] *)
(*    1429844: ldr x25,[sp, #0x40] *)
| 0x15d154 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move R_X25 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015d158: mov x0,x21 *)
(*    1429848: mov x0,x21 *)
| 0x15d158 => Some (4,
	Move R_X0 (Var R_X21)
)

(* 0x0015d15c: ldp x19,x20,[sp, #0x10] *)
(*    1429852: ldp x19,x20,[sp, #0x10] *)
| 0x15d15c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015d160: ldp x21,x22,[sp, #0x20] *)
(*    1429856: ldp x21,x22,[sp, #0x20] *)
| 0x15d160 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x0015d164: ldp x23,x24,[sp, #0x30] *)
(*    1429860: ldp x23,x24,[sp, #0x30] *)
| 0x15d164 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X23 (Var (V_TEMP 0x24180)) $;
	Move R_X24 (Var (V_TEMP 0x24300))
)

(* 0x0015d168: ldp x29,x30,[sp], #0x50 *)
(*    1429864: ldp x29,x30,[sp], #0x50 *)
| 0x15d168 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015d16c: ret *)
(*    1429868: ret *)
| 0x15d16c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx bsearch_armv8.
Proof. Picinae_typecheck. Qed.
