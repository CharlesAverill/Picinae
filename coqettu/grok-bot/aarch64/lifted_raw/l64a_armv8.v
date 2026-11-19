(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: l64a
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition l64a_armv8 : program := fun _ a => match a with

(* 0x0013b14c: adrp x4,0x1c2000 *)
(*    1290572: adrp x4,0x1c2000 *)
| 0x13b14c => Some (4,
	Move R_X4 (Word 0x1c2000 64)
)

(* 0x0013b150: adrp x3,0x19d000 *)
(*    1290576: adrp x3,0x19d000 *)
| 0x13b150 => Some (4,
	Move R_X3 (Word 0x19d000 64)
)

(* 0x0013b154: add x1,x4,#0x348 *)
(*    1290580: add x1,x4,#0x348 *)
| 0x13b154 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x348 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0013b158: add x3,x3,#0xab0 *)
(*    1290584: add x3,x3,#0xab0 *)
| 0x13b158 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0xab0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0013b15c: b 0x0013b170 *)
(*    1290588: b 0x0013b170 *)
| 0x13b15c => Some (4,
	Jmp (Word 0x13b170 64)
)

(* 0x0013b160: and w2,w0,#0x3f *)
(*    1290592: and w2,w0,#0x3f *)
| 0x13b160 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x3f 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0013b164: lsr w0,w0,#0x6 *)
(*    1290596: lsr w0,w0,#0x6 *)
| 0x13b164 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x6 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x0013b168: ldrb w2,[x3, w2, UXTW ] *)
(*    1290600: ldrb w2,[x3, w2, UXTW ] *)
| 0x13b168 => Some (4,
	Move (V_TEMP 0x5580) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x6c00) (Var (V_TEMP 0x5580)) $;
	Move (V_TEMP 0x6c00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6c00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x6c00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0013b16c: strb w2,[x1], #0x1 *)
(*    1290604: strb w2,[x1], #0x1 *)
| 0x13b16c => Some (4,
	Move (V_TEMP 0x3a380) (Extract 31 0 (Var R_X2)) $;
	Move (V_TEMP 0x7000) (Var R_X1) $;
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x1 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a380)))) LittleE 1)
)

(* 0x0013b170: cbnz w0,0x0013b160 *)
(*    1290608: cbnz w0,0x0013b160 *)
| 0x13b170 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x13b160 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013b174: add x0,x4,#0x348 *)
(*    1290612: add x0,x4,#0x348 *)
| 0x13b174 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x348 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0013b178: strb wzr,[x1] *)
(*    1290616: strb wzr,[x1] *)
| 0x13b178 => Some (4,
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move (V_TEMP 0x3a300) (Var (V_TEMP 0x300)) $;
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x0013b17c: ret *)
(*    1290620: ret *)
| 0x13b17c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx l64a_armv8.
Proof. Picinae_typecheck. Qed.
