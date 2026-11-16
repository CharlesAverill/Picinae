(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strerror_r
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strerror_r_armv8 : program := fun _ a => match a with

(* 0x0015ede8: stp x29,x30,[sp, #-0x30]! *)
(*    1437160: stp x29,x30,[sp, #-0x30]! *)
| 0x15ede8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015edec: mov x29,sp *)
(*    1437164: mov x29,sp *)
| 0x15edec => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015edf0: stp x19,x20,[sp, #0x10] *)
(*    1437168: stp x19,x20,[sp, #0x10] *)
| 0x15edf0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015edf4: mov x19,x1 *)
(*    1437172: mov x19,x1 *)
| 0x15edf4 => Some (4,
	Move R_X19 (Var R_X1)
)

(* 0x0015edf8: str x2,[sp, #0x28] *)
(*    1437176: str x2,[sp, #0x28] *)
| 0x15edf8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x0015edfc: bl 0x00120448 *)
(*    1437180: bl 0x00120448 *)
| 0x15edfc => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15edfc 64) (Word 0x4 64)) $;
	Jmp (Word 0x120448 64)
)

(* 0x0015ee00: mov x20,x0 *)
(*    1437184: mov x20,x0 *)
| 0x15ee00 => Some (4,
	Move R_X20 (Var R_X0)
)

(* 0x0015ee04: bl 0x0015efa8 *)
(*    1437188: bl 0x0015efa8 *)
| 0x15ee04 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ee04 64) (Word 0x4 64)) $;
	Jmp (Word 0x15efa8 64)
)

(* 0x0015ee08: ldr x2,[sp, #0x28] *)
(*    1437192: ldr x2,[sp, #0x28] *)
| 0x15ee08 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ee0c: cmp x0,x2 *)
(*    1437196: cmp x0,x2 *)
| 0x15ee0c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ee10: b.cs 0x0015ee34 *)
(*    1437200: b.cs 0x0015ee34 *)
| 0x15ee10 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x15ee34 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ee14: add x2,x0,#0x1 *)
(*    1437204: add x2,x0,#0x1 *)
| 0x15ee14 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ee18: mov x1,x20 *)
(*    1437208: mov x1,x20 *)
| 0x15ee18 => Some (4,
	Move R_X1 (Var R_X20)
)

(* 0x0015ee1c: mov x0,x19 *)
(*    1437212: mov x0,x19 *)
| 0x15ee1c => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ee20: bl 0x00118270 *)
(*    1437216: bl 0x00118270 *)
| 0x15ee20 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ee20 64) (Word 0x4 64)) $;
	Jmp (Word 0x118270 64)
)

(* 0x0015ee24: mov w0,#0x0 *)
(*    1437220: mov w0,#0x0 *)
| 0x15ee24 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015ee28: ldp x19,x20,[sp, #0x10] *)
(*    1437224: ldp x19,x20,[sp, #0x10] *)
| 0x15ee28 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015ee2c: ldp x29,x30,[sp], #0x30 *)
(*    1437228: ldp x29,x30,[sp], #0x30 *)
| 0x15ee2c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ee30: ret *)
(*    1437232: ret *)
| 0x15ee30 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015ee34: cbnz x2,0x0015ee40 *)
(*    1437236: cbnz x2,0x0015ee40 *)
| 0x15ee34 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15ee40 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ee38: mov w0,#0x22 *)
(*    1437240: mov w0,#0x22 *)
| 0x15ee38 => Some (4,
	Move R_X0 (Word 0x22 64)
)

(* 0x0015ee3c: b 0x0015ee28 *)
(*    1437244: b 0x0015ee28 *)
| 0x15ee3c => Some (4,
	Jmp (Word 0x15ee28 64)
)

(* 0x0015ee40: sub x2,x2,#0x1 *)
(*    1437248: sub x2,x2,#0x1 *)
| 0x15ee40 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015ee44: mov x1,x20 *)
(*    1437252: mov x1,x20 *)
| 0x15ee44 => Some (4,
	Move R_X1 (Var R_X20)
)

(* 0x0015ee48: mov x0,x19 *)
(*    1437256: mov x0,x19 *)
| 0x15ee48 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ee4c: str x2,[sp, #0x28] *)
(*    1437260: str x2,[sp, #0x28] *)
| 0x15ee4c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x0015ee50: bl 0x00118270 *)
(*    1437264: bl 0x00118270 *)
| 0x15ee50 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ee50 64) (Word 0x4 64)) $;
	Jmp (Word 0x118270 64)
)

(* 0x0015ee54: ldr x2,[sp, #0x28] *)
(*    1437268: ldr x2,[sp, #0x28] *)
| 0x15ee54 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ee58: strb wzr,[x19, x2, LSL ] *)
(*    1437272: strb wzr,[x19, x2, LSL ] *)
| 0x15ee58 => Some (4,
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move (V_TEMP 0x3a400) (Var (V_TEMP 0x300)) $;
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a400)))) LittleE 1)
)

(* 0x0015ee5c: b 0x0015ee38 *)
(*    1437276: b 0x0015ee38 *)
| 0x15ee5c => Some (4,
	Jmp (Word 0x15ee38 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx strerror_r_armv8.
Proof. Picinae_typecheck. Qed.
