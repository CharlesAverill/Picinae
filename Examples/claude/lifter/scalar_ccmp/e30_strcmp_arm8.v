(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: strcmp; entry: 0x192f80; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e30_strcmp_arm8 : program := fun _ a => match a with
(* 0x192f80: nop *)
| 0x192f80 => Some (4,
	Nop
)
(* 0x192f84: sub x10,x1,x0 *)
| 0x192f84 => Some (4,
	Move R_X10 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)
(* 0x192f88: orr x8,xzr,#0x101010101010101 *)
| 0x192f88 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move R_X8 (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x101010101010101 64))
)
(* 0x192f8c: and x6,x0,#0x7 *)
| 0x192f8c => Some (4,
	Move R_X6 (BinOp OP_AND (Var R_X0) (Word 0x7 64))
)
(* 0x192f90: tst x10,#0x7 *)
| 0x192f90 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X10) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x192f94: b.ne 0x00193014 *)
| 0x192f94 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x193014 64)) (Nop)
)
(* 0x192f98: cbnz x6,0x00192ff0 *)
| 0x192f98 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_X6) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x192ff0 64)) (Nop)
)
(* 0x192f9c: nop *)
| 0x192f9c => Some (4,
	Nop
)
(* 0x192fa0: ldr x3,[x0, x10, LSL #0x0] *)
| 0x192fa0 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8)
)
(* 0x192fa4: ldr x2,[x0], #0x8 *)
| 0x192fa4 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x192fa8: sub x4,x2,x8 *)
| 0x192fa8 => Some (4,
	Move R_X4 (BinOp OP_MINUS (Var R_X2) (Var R_X8))
)
(* 0x192fac: orr x6,x2,#0x7f7f7f7f7f7f7f7f *)
| 0x192fac => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X2) (Word 0x7f7f7f7f7f7f7f7f 64))
)
(* 0x192fb0: bics x4,x4,x6 *)
| 0x192fb0 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X6) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var R_X4) (Var (V_TEMP 1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 2)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x192fb4: ccmp x2,x3,#0x0,eq *)
| 0x192fb4 => Some (4,
	Move (V_TEMP 0) (Var R_ZR) $;
	Move (V_TEMP 1) (Word 0x0 8) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x8 8))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x4 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x2 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x1 8))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 6))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var R_X3))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var R_X3)))))) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Var R_X2) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x192fb8: b.eq 0x00192fa0 *)
| 0x192fb8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x192fa0 64)) (Nop)
)
(* 0x192fbc: eor x5,x2,x3 *)
| 0x192fbc => Some (4,
	Move R_X5 (BinOp OP_XOR (Var R_X2) (Var R_X3))
)
(* 0x192fc0: orr x6,x5,x4 *)
| 0x192fc0 => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X5) (Var R_X4))
)
(* 0x192fc4: rev x6,x6 *)
| 0x192fc4 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move (V_TEMP 10) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X6 (BinOp OP_OR (Var (V_TEMP 9)) (Var (V_TEMP 10)))
)
(* 0x192fc8: rev x2,x2 *)
| 0x192fc8 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move (V_TEMP 10) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X2 (BinOp OP_OR (Var (V_TEMP 9)) (Var (V_TEMP 10)))
)
(* 0x192fcc: rev x3,x3 *)
| 0x192fcc => Some (4,
	Move (V_TEMP 0) (Var R_X3) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move (V_TEMP 10) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X3 (BinOp OP_OR (Var (V_TEMP 9)) (Var (V_TEMP 10)))
)
(* 0x192fd0: clz x9,x6 *)
| 0x192fd0 => Some (4,
	Move R_X9 (BinOp OP_MINUS (Word 0x40 64) (UnOp OP_BITWIDTH (Var R_X6)))
)
(* 0x192fd4: lsl x2,x2,x9 *)
| 0x192fd4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X2 (BinOp OP_LSHIFT (Var R_X2) (Var (V_TEMP 0)))
)
(* 0x192fd8: lsl x3,x3,x9 *)
| 0x192fd8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X3 (BinOp OP_LSHIFT (Var R_X3) (Var (V_TEMP 0)))
)
(* 0x192fdc: lsr x2,x2,#0x38 *)
| 0x192fdc => Some (4,
	Move R_X2 (BinOp OP_RSHIFT (Var R_X2) (Word 0x38 64))
)
(* 0x192fe0: sub x0,x2,x3, LSR #0x38 *)
| 0x192fe0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Var R_X3) (Cast CAST_UNSIGNED 64 (Word 0x38 32))) $;
	Move R_X0 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0)))
)
(* 0x192fe4: ret *)
| 0x192fe4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x192fe8: nop *)
| 0x192fe8 => Some (4,
	Nop
)
(* 0x192fec: nop *)
| 0x192fec => Some (4,
	Nop
)
(* 0x192ff0: and x0,x0,#-0x8 *)
| 0x192ff0 => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff8 64))
)
(* 0x192ff4: ldr x3,[x0, x10, LSL #0x0] *)
| 0x192ff4 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8)
)
(* 0x192ff8: ldr x2,[x0], #0x8 *)
| 0x192ff8 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x192ffc: neg x9,x1, LSL #0x3 *)
| 0x192ffc => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Var R_X1) (Cast CAST_UNSIGNED 64 (Word 0x3 32))) $;
	Move R_X9 (UnOp OP_NEG (Var (V_TEMP 0)))
)
(* 0x193000: mov x6,#-0x1 *)
| 0x193000 => Some (4,
	Move R_X6 (Word 0xffffffffffffffff 64)
)
(* 0x193004: lsr x6,x6,x9 *)
| 0x193004 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X6 (BinOp OP_RSHIFT (Var R_X6) (Var (V_TEMP 0)))
)
(* 0x193008: orr x2,x2,x6 *)
| 0x193008 => Some (4,
	Move R_X2 (BinOp OP_OR (Var R_X2) (Var R_X6))
)
(* 0x19300c: orr x3,x3,x6 *)
| 0x19300c => Some (4,
	Move R_X3 (BinOp OP_OR (Var R_X3) (Var R_X6))
)
(* 0x193010: b 0x00192fa8 *)
| 0x193010 => Some (4,
	Jmp (Word 0x192fa8 64)
)
(* 0x193014: cbz x6,0x00193034 *)
| 0x193014 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X6) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x193034 64)) (Nop)
)
(* 0x193018: ldrb w2,[x0], #0x1 *)
| 0x193018 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19301c: ldrb w3,[x1], #0x1 *)
| 0x19301c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x193020: cmp w2,#0x0 *)
| 0x193020 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Word 0x0 32))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x0 32)))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x193024: ccmp w2,w3,#0x0,ne *)
| 0x193024 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 8) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x8 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x4 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x2 8))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 6)) (Word 0x1 8))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 1)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 7))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (Extract 31 0 (Var R_X3)))) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_X2))) (Extract 31 31 (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))))))) $;
	Move (V_TEMP 8) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 8)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x193028: b.ne 0x001930ac *)
| 0x193028 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x1930ac 64)) (Nop)
)
(* 0x19302c: tst x0,#0x7 *)
| 0x19302c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X0) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x193030: b.ne 0x00193018 *)
| 0x193030 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x193018 64)) (Nop)
)
(* 0x193034: neg x9,x1, LSL #0x3 *)
| 0x193034 => Some (4,
	Move (V_TEMP 0) (BinOp OP_LSHIFT (Var R_X1) (Cast CAST_UNSIGNED 64 (Word 0x3 32))) $;
	Move R_X9 (UnOp OP_NEG (Var (V_TEMP 0)))
)
(* 0x193038: and x1,x1,#-0x8 *)
| 0x193038 => Some (4,
	Move R_X1 (BinOp OP_AND (Var R_X1) (Word 0xfffffffffffffff8 64))
)
(* 0x19303c: ldr x7,[x1], #0x8 *)
| 0x19303c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move R_X7 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x193040: lsr x6,x8,x9 *)
| 0x193040 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X6 (BinOp OP_RSHIFT (Var R_X8) (Var (V_TEMP 0)))
)
(* 0x193044: orr x7,x7,x6 *)
| 0x193044 => Some (4,
	Move R_X7 (BinOp OP_OR (Var R_X7) (Var R_X6))
)
(* 0x193048: sub x4,x7,x8 *)
| 0x193048 => Some (4,
	Move R_X4 (BinOp OP_MINUS (Var R_X7) (Var R_X8))
)
(* 0x19304c: orr x6,x7,#0x7f7f7f7f7f7f7f7f *)
| 0x19304c => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X7) (Word 0x7f7f7f7f7f7f7f7f 64))
)
(* 0x193050: bics x4,x4,x6 *)
| 0x193050 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X6) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var R_X4) (Var (V_TEMP 1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 2)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x193054: b.ne 0x00193090 *)
| 0x193054 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x193090 64)) (Nop)
)
(* 0x193058: sub x5,x1,x0 *)
| 0x193058 => Some (4,
	Move R_X5 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)
(* 0x19305c: nop *)
| 0x19305c => Some (4,
	Nop
)
(* 0x193060: ldr x7,[x0, x5, LSL #0x0] *)
| 0x193060 => Some (4,
	Move (V_TEMP 0) (Var R_X5) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move R_X7 (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8)
)
(* 0x193064: ldr x3,[x0, x10, LSL #0x0] *)
| 0x193064 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8)
)
(* 0x193068: sub x4,x7,x8 *)
| 0x193068 => Some (4,
	Move R_X4 (BinOp OP_MINUS (Var R_X7) (Var R_X8))
)
(* 0x19306c: orr x6,x7,#0x7f7f7f7f7f7f7f7f *)
| 0x19306c => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X7) (Word 0x7f7f7f7f7f7f7f7f 64))
)
(* 0x193070: ldr x2,[x0], #0x8 *)
| 0x193070 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x193074: bics x4,x4,x6 *)
| 0x193074 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X6) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var R_X4) (Var (V_TEMP 1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 2)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x193078: ccmp x2,x3,#0x0,eq *)
| 0x193078 => Some (4,
	Move (V_TEMP 0) (Var R_ZR) $;
	Move (V_TEMP 1) (Word 0x0 8) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x8 8))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x4 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x2 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x1 8))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 6))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X3) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var R_X3))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var R_X3)))))) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Var R_X2) (Var R_X3)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19307c: b.eq 0x00193060 *)
| 0x19307c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x193060 64)) (Nop)
)
(* 0x193080: lsl x6,x4,x9 *)
| 0x193080 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X6 (BinOp OP_LSHIFT (Var R_X4) (Var (V_TEMP 0)))
)
(* 0x193084: eor x5,x2,x3 *)
| 0x193084 => Some (4,
	Move R_X5 (BinOp OP_XOR (Var R_X2) (Var R_X3))
)
(* 0x193088: orr x6,x5,x6 *)
| 0x193088 => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X5) (Var R_X6))
)
(* 0x19308c: cbnz x6,0x00192fc4 *)
| 0x19308c => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_X6) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x192fc4 64)) (Nop)
)
(* 0x193090: ldr x2,[x0] *)
| 0x193090 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x193094: neg x9,x9 *)
| 0x193094 => Some (4,
	Move R_X9 (UnOp OP_NEG (Var R_X9))
)
(* 0x193098: lsr x3,x7,x9 *)
| 0x193098 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X3 (BinOp OP_RSHIFT (Var R_X7) (Var (V_TEMP 0)))
)
(* 0x19309c: lsr x4,x4,x9 *)
| 0x19309c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X9) (Word 0x3f 64)) $;
	Move R_X4 (BinOp OP_RSHIFT (Var R_X4) (Var (V_TEMP 0)))
)
(* 0x1930a0: eor x5,x2,x3 *)
| 0x1930a0 => Some (4,
	Move R_X5 (BinOp OP_XOR (Var R_X2) (Var R_X3))
)
(* 0x1930a4: orr x6,x5,x4 *)
| 0x1930a4 => Some (4,
	Move R_X6 (BinOp OP_OR (Var R_X5) (Var R_X4))
)
(* 0x1930a8: b 0x00192fc4 *)
| 0x1930a8 => Some (4,
	Jmp (Word 0x192fc4 64)
)
(* 0x1930ac: sub x0,x2,x3 *)
| 0x1930ac => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X2) (Var R_X3))
)
(* 0x1930b0: ret *)
| 0x1930b0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e30_strcmp_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
