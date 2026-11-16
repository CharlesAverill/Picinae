(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strlen
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strlen_armv8 : program := fun _ a => match a with

(* 0x0015efa8: mov x1,x0 *)
(*    1437608: mov x1,x0 *)
| 0x15efa8 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x0015efac: b 0x0015efb4 *)
(*    1437612: b 0x0015efb4 *)
| 0x15efac => Some (4,
	Jmp (Word 0x15efb4 64)
)

(* 0x0015efb0: add x1,x1,#0x1 *)
(*    1437616: add x1,x1,#0x1 *)
| 0x15efb0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015efb4: tst x1,#0x7 *)
(*    1437620: tst x1,#0x7 *)
| 0x15efb4 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X1) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015efb8: b.eq 0x0015efc8 *)
(*    1437624: b.eq 0x0015efc8 *)
| 0x15efb8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15efc8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015efbc: ldrb w2,[x1] *)
(*    1437628: ldrb w2,[x1] *)
| 0x15efbc => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015efc0: cbnz w2,0x0015efb0 *)
(*    1437632: cbnz w2,0x0015efb0 *)
| 0x15efc0 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15efb0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015efc4: b 0x0015effc *)
(*    1437636: b 0x0015effc *)
| 0x15efc4 => Some (4,
	Jmp (Word 0x15effc 64)
)

(* 0x0015efc8: orr x4,xzr,#-0x101010101010102 *)
(*    1437640: orr x4,xzr,#-0x101010101010102 *)
| 0x15efc8 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X4 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfefefefefefefefe 64))
)

(* 0x0015efcc: movk x4,#0xfeff *)
(*    1437644: movk x4,#0xfeff *)
| 0x15efcc => Some (4,
	Move R_X4 (BinOp OP_AND (Var R_X4) (Word 0xffffffffffff0000 64)) $;
	Move R_X4 (BinOp OP_OR (Var R_X4) (Word 0xfeff 64))
)

(* 0x0015efd0: b 0x0015efd8 *)
(*    1437648: b 0x0015efd8 *)
| 0x15efd0 => Some (4,
	Jmp (Word 0x15efd8 64)
)

(* 0x0015efd4: add x1,x1,#0x8 *)
(*    1437652: add x1,x1,#0x8 *)
| 0x15efd4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015efd8: ldr x3,[x1] *)
(*    1437656: ldr x3,[x1] *)
| 0x15efd8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015efdc: add x2,x3,x4 *)
(*    1437660: add x2,x3,x4 *)
| 0x15efdc => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X4) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x0015efe0: bic x2,x2,x3 *)
(*    1437664: bic x2,x2,x3 *)
| 0x15efe0 => Some (4,
	Move (V_TEMP 0x15e00) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x15f00) (BinOp OP_XOR (Var R_X3) (Var (V_TEMP 0x15e00))) $;
	Move R_X2 (BinOp OP_AND (Var R_X2) (Var (V_TEMP 0x15f00)))
)

(* 0x0015efe4: tst x2,#-0x7f7f7f7f7f7f7f80 *)
(*    1437668: tst x2,#-0x7f7f7f7f7f7f7f80 *)
| 0x15efe4 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X2) (Word 0x8080808080808080 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015efe8: b.eq 0x0015efd4 *)
(*    1437672: b.eq 0x0015efd4 *)
| 0x15efe8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15efd4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015efec: b 0x0015eff4 *)
(*    1437676: b 0x0015eff4 *)
| 0x15efec => Some (4,
	Jmp (Word 0x15eff4 64)
)

(* 0x0015eff0: add x1,x1,#0x1 *)
(*    1437680: add x1,x1,#0x1 *)
| 0x15eff0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015eff4: ldrb w2,[x1] *)
(*    1437684: ldrb w2,[x1] *)
| 0x15eff4 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015eff8: cbnz w2,0x0015eff0 *)
(*    1437688: cbnz w2,0x0015eff0 *)
| 0x15eff8 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15eff0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015effc: sub x0,x1,x0 *)
(*    1437692: sub x0,x1,x0 *)
| 0x15effc => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x0015f000: ret *)
(*    1437696: ret *)
| 0x15f000 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strlen_armv8.
Proof. Picinae_typecheck. Qed.
