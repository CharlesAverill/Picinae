(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: __memmove_generic; entry: 0x19acd0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08___memmove_generic_arm8 : program := fun _ a => match a with
(* 0x19ab40: nop *)
| 0x19ab40 => Some (4,
	Nop
)
(* 0x19ab44: add x4,x1,x2 *)
| 0x19ab44 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 1))
)
(* 0x19ab48: add x5,x0,x2 *)
| 0x19ab48 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 1))
)
(* 0x19ab4c: cmp x2,#0x80 *)
| 0x19ab4c => Some (4,
	Move (V_TEMP 0) (Word 0x80 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ab50: b.hi 0x0019ac40 *)
| 0x19ab50 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ac40 64)) (Nop)
)
(* 0x19ab54: cmp x2,#0x20 *)
| 0x19ab54 => Some (4,
	Move (V_TEMP 0) (Word 0x20 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ab58: b.hi 0x0019abd0 *)
| 0x19ab58 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19abd0 64)) (Nop)
)
(* 0x19ab5c: cmp x2,#0x10 *)
| 0x19ab5c => Some (4,
	Move (V_TEMP 0) (Word 0x10 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ab60: b.cc 0x0019ab78 *)
| 0x19ab60 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19ab78 64)) (Nop)
)
(* 0x19ab64: ldp x6,x7,[x1] *)
| 0x19ab64 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ab68: ldp x12,x13,[x4, #-0x10] *)
| 0x19ab68 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 1)) $;
	Move R_X13 (Var (V_TEMP 3))
)
(* 0x19ab6c: stp x6,x7,[x0] *)
| 0x19ab6c => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ab70: stp x12,x13,[x5, #-0x10] *)
| 0x19ab70 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ab74: ret *)
| 0x19ab74 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19ab78: tbz w2,#0x3,0x0019ab90 *)
| 0x19ab78 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x3 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19ab90 64)) (Nop)
)
(* 0x19ab7c: ldr x6,[x1] *)
| 0x19ab7c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move R_X6 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x19ab80: ldur x7,[x4, #-0x8] *)
| 0x19ab80 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff8 64)) $;
	Move R_X7 (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x19ab84: str x6,[x0] *)
| 0x19ab84 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X6) LittleE 8)
)
(* 0x19ab88: stur x7,[x5, #-0x8] *)
| 0x19ab88 => Some (4,
	Move (V_TEMP 0) (Var R_X7) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x19ab8c: ret *)
| 0x19ab8c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19ab90: tbz w2,#0x2,0x0019aba8 *)
| 0x19ab90 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x2 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19aba8 64)) (Nop)
)
(* 0x19ab94: ldr w6,[x1] *)
| 0x19ab94 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19ab98: ldur w8,[x4, #-0x4] *)
| 0x19ab98 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffc 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 4) $;
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19ab9c: str w6,[x0] *)
| 0x19ab9c => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X6)) LittleE 4)
)
(* 0x19aba0: stur w8,[x5, #-0x4] *)
| 0x19aba0 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X8)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffffc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 4)
)
(* 0x19aba4: ret *)
| 0x19aba4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19aba8: cbz x2,0x0019abc8 *)
| 0x19aba8 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X2) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19abc8 64)) (Nop)
)
(* 0x19abac: lsr x14,x2,#0x1 *)
| 0x19abac => Some (4,
	Move R_X14 (BinOp OP_RSHIFT (Var R_X2) (Word 0x1 64))
)
(* 0x19abb0: ldrb w6,[x1] *)
| 0x19abb0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19abb4: ldurb w10,[x4, #-0x1] *)
| 0x19abb4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffff 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_X10 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)
(* 0x19abb8: ldrb w8,[x1, x14, LSL ] *)
| 0x19abb8 => Some (4,
	Move (V_TEMP 0) (Var R_X14) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x0 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))
)
(* 0x19abbc: strb w6,[x0] *)
| 0x19abbc => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X6)) $;
	Move (V_TEMP 1) (Var R_X0) $;
	Move (V_TEMP 2) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 2)) LittleE 1)
)
(* 0x19abc0: strb w8,[x0, x14, LSL ] *)
| 0x19abc0 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X8)) $;
	Move (V_TEMP 1) (Var R_X14) $;
	Move (V_TEMP 2) (Var (V_TEMP 1)) $;
	Move (V_TEMP 2) (BinOp OP_LSHIFT (Var (V_TEMP 2)) (Word 0x0 64)) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 4)) LittleE 1)
)
(* 0x19abc4: sturb w10,[x5, #-0x1] *)
| 0x19abc4 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X10)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffff 64)) $;
	Move (V_TEMP 2) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 2)) LittleE 1)
)
(* 0x19abc8: ret *)
| 0x19abc8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19abcc: nop *)
| 0x19abcc => Some (4,
	Nop
)
(* 0x19abd0: ldp x6,x7,[x1] *)
| 0x19abd0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19abd4: ldp x8,x9,[x1, #0x10] *)
| 0x19abd4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19abd8: ldp x10,x11,[x4, #-0x20] *)
| 0x19abd8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19abdc: ldp x12,x13,[x4, #-0x10] *)
| 0x19abdc => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 1)) $;
	Move R_X13 (Var (V_TEMP 3))
)
(* 0x19abe0: cmp x2,#0x40 *)
| 0x19abe0 => Some (4,
	Move (V_TEMP 0) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19abe4: b.hi 0x0019ac00 *)
| 0x19abe4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ac00 64)) (Nop)
)
(* 0x19abe8: stp x6,x7,[x0] *)
| 0x19abe8 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19abec: stp x8,x9,[x0, #0x10] *)
| 0x19abec => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19abf0: stp x10,x11,[x5, #-0x20] *)
| 0x19abf0 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19abf4: stp x12,x13,[x5, #-0x10] *)
| 0x19abf4 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19abf8: ret *)
| 0x19abf8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19abfc: nop *)
| 0x19abfc => Some (4,
	Nop
)
(* 0x19ac00: ldp x14,x15,[x1, #0x20] *)
| 0x19ac00 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X14 (Var (V_TEMP 1)) $;
	Move R_X15 (Var (V_TEMP 3))
)
(* 0x19ac04: ldp x16,x17,[x1, #0x30] *)
| 0x19ac04 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X16 (Var (V_TEMP 1)) $;
	Move R_X17 (Var (V_TEMP 3))
)
(* 0x19ac08: cmp x2,#0x60 *)
| 0x19ac08 => Some (4,
	Move (V_TEMP 0) (Word 0x60 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ac0c: b.ls 0x0019ac20 *)
| 0x19ac0c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 0)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ac20 64)) (Nop)
)
(* 0x19ac10: ldp x2,x3,[x4, #-0x40] *)
| 0x19ac10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_X3 (Var (V_TEMP 3))
)
(* 0x19ac14: ldp x1,x4,[x4, #-0x30] *)
| 0x19ac14 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X1 (Var (V_TEMP 1)) $;
	Move R_X4 (Var (V_TEMP 3))
)
(* 0x19ac18: stp x2,x3,[x5, #-0x40] *)
| 0x19ac18 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Var R_X3) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac1c: stp x1,x4,[x5, #-0x30] *)
| 0x19ac1c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X4) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac20: stp x6,x7,[x0] *)
| 0x19ac20 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac24: stp x8,x9,[x0, #0x10] *)
| 0x19ac24 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac28: stp x14,x15,[x0, #0x20] *)
| 0x19ac28 => Some (4,
	Move (V_TEMP 0) (Var R_X14) $;
	Move (V_TEMP 1) (Var R_X15) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac2c: stp x16,x17,[x0, #0x30] *)
| 0x19ac2c => Some (4,
	Move (V_TEMP 0) (Var R_X16) $;
	Move (V_TEMP 1) (Var R_X17) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac30: stp x10,x11,[x5, #-0x20] *)
| 0x19ac30 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac34: stp x12,x13,[x5, #-0x10] *)
| 0x19ac34 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac38: ret *)
| 0x19ac38 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19ac3c: nop *)
| 0x19ac3c => Some (4,
	Nop
)
(* 0x19ac40: ldp x12,x13,[x1] *)
| 0x19ac40 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 1)) $;
	Move R_X13 (Var (V_TEMP 3))
)
(* 0x19ac44: and x14,x0,#0xf *)
| 0x19ac44 => Some (4,
	Move R_X14 (BinOp OP_AND (Var R_X0) (Word 0xf 64))
)
(* 0x19ac48: and x3,x0,#-0x10 *)
| 0x19ac48 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)
(* 0x19ac4c: sub x1,x1,x14 *)
| 0x19ac4c => Some (4,
	Move R_X1 (BinOp OP_MINUS (Var R_X1) (Var R_X14))
)
(* 0x19ac50: add x2,x2,x14 *)
| 0x19ac50 => Some (4,
	Move (V_TEMP 0) (Var R_X14) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1))
)
(* 0x19ac54: ldp x6,x7,[x1, #0x10] *)
| 0x19ac54 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ac58: stp x12,x13,[x0] *)
| 0x19ac58 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac5c: ldp x8,x9,[x1, #0x20] *)
| 0x19ac5c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19ac60: ldp x10,x11,[x1, #0x30] *)
| 0x19ac60 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19ac64: ldp x12,x13,[x1, #0x40]! *)
| 0x19ac64 => Some (4,
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0)) $;
	Move R_X13 (Var (V_TEMP 2))
)
(* 0x19ac68: subs x2,x2,#0x90 *)
| 0x19ac68 => Some (4,
	Move (V_TEMP 0) (Word 0x90 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ac6c: b.ls 0x0019ac98 *)
| 0x19ac6c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 0)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ac98 64)) (Nop)
)
(* 0x19ac70: stp x6,x7,[x3, #0x10] *)
| 0x19ac70 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac74: ldp x6,x7,[x1, #0x10] *)
| 0x19ac74 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ac78: stp x8,x9,[x3, #0x20] *)
| 0x19ac78 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac7c: ldp x8,x9,[x1, #0x20] *)
| 0x19ac7c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19ac80: stp x10,x11,[x3, #0x30] *)
| 0x19ac80 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac84: ldp x10,x11,[x1, #0x30] *)
| 0x19ac84 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19ac88: stp x12,x13,[x3, #0x40]! *)
| 0x19ac88 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X3) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ac8c: ldp x12,x13,[x1, #0x40]! *)
| 0x19ac8c => Some (4,
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0)) $;
	Move R_X13 (Var (V_TEMP 2))
)
(* 0x19ac90: subs x2,x2,#0x40 *)
| 0x19ac90 => Some (4,
	Move (V_TEMP 0) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ac94: b.hi 0x0019ac70 *)
| 0x19ac94 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ac70 64)) (Nop)
)
(* 0x19ac98: ldp x14,x15,[x4, #-0x40] *)
| 0x19ac98 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X14 (Var (V_TEMP 1)) $;
	Move R_X15 (Var (V_TEMP 3))
)
(* 0x19ac9c: stp x6,x7,[x3, #0x10] *)
| 0x19ac9c => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19aca0: ldp x6,x7,[x4, #-0x30] *)
| 0x19aca0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19aca4: stp x8,x9,[x3, #0x20] *)
| 0x19aca4 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19aca8: ldp x8,x9,[x4, #-0x20] *)
| 0x19aca8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19acac: stp x10,x11,[x3, #0x30] *)
| 0x19acac => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acb0: ldp x10,x11,[x4, #-0x10] *)
| 0x19acb0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19acb4: stp x12,x13,[x3, #0x40] *)
| 0x19acb4 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acb8: stp x14,x15,[x5, #-0x40] *)
| 0x19acb8 => Some (4,
	Move (V_TEMP 0) (Var R_X14) $;
	Move (V_TEMP 1) (Var R_X15) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acbc: stp x6,x7,[x5, #-0x30] *)
| 0x19acbc => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acc0: stp x8,x9,[x5, #-0x20] *)
| 0x19acc0 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acc4: stp x10,x11,[x5, #-0x10] *)
| 0x19acc4 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19acc8: ret *)
| 0x19acc8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19acd0: nop *)
| 0x19acd0 => Some (4,
	Nop
)
(* 0x19acd4: add x4,x1,x2 *)
| 0x19acd4 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X1)) (Extract 63 63 (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 1))
)
(* 0x19acd8: add x5,x0,x2 *)
| 0x19acd8 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 1))
)
(* 0x19acdc: cmp x2,#0x80 *)
| 0x19acdc => Some (4,
	Move (V_TEMP 0) (Word 0x80 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ace0: b.hi 0x0019ad10 *)
| 0x19ace0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ad10 64)) (Nop)
)
(* 0x19ace4: cmp x2,#0x20 *)
| 0x19ace4 => Some (4,
	Move (V_TEMP 0) (Word 0x20 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ace8: b.hi 0x0019abd0 *)
| 0x19ace8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19abd0 64)) (Nop)
)
(* 0x19acec: cmp x2,#0x10 *)
| 0x19acec => Some (4,
	Move (V_TEMP 0) (Word 0x10 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19acf0: b.cc 0x0019ab78 *)
| 0x19acf0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19ab78 64)) (Nop)
)
(* 0x19acf4: ldp x6,x7,[x1] *)
| 0x19acf4 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19acf8: ldp x12,x13,[x4, #-0x10] *)
| 0x19acf8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 1)) $;
	Move R_X13 (Var (V_TEMP 3))
)
(* 0x19acfc: stp x6,x7,[x0] *)
| 0x19acfc => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad00: stp x12,x13,[x5, #-0x10] *)
| 0x19ad00 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad04: ret *)
| 0x19ad04 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19ad08: nop *)
| 0x19ad08 => Some (4,
	Nop
)
(* 0x19ad0c: nop *)
| 0x19ad0c => Some (4,
	Nop
)
(* 0x19ad10: sub x14,x0,x1 *)
| 0x19ad10 => Some (4,
	Move R_X14 (BinOp OP_MINUS (Var R_X0) (Var R_X1))
)
(* 0x19ad14: cbz x14,0x0019abc8 *)
| 0x19ad14 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X14) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19abc8 64)) (Nop)
)
(* 0x19ad18: cmp x14,x2 *)
| 0x19ad18 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X14))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X14)) (Extract 63 63 (Var R_X2))) (BinOp OP_XOR (Extract 63 63 (Var R_X14)) (Extract 63 63 (BinOp OP_MINUS (Var R_X14) (Var R_X2)))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Var R_X14) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ad1c: b.cs 0x0019ac40 *)
| 0x19ad1c => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (Jmp (Word 0x19ac40 64)) (Nop)
)
(* 0x19ad20: ldp x12,x13,[x4, #-0x10] *)
| 0x19ad20 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 1)) $;
	Move R_X13 (Var (V_TEMP 3))
)
(* 0x19ad24: and x14,x5,#0xf *)
| 0x19ad24 => Some (4,
	Move R_X14 (BinOp OP_AND (Var R_X5) (Word 0xf 64))
)
(* 0x19ad28: sub x4,x4,x14 *)
| 0x19ad28 => Some (4,
	Move R_X4 (BinOp OP_MINUS (Var R_X4) (Var R_X14))
)
(* 0x19ad2c: sub x2,x2,x14 *)
| 0x19ad2c => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Var R_X14))
)
(* 0x19ad30: ldp x6,x7,[x4, #-0x10] *)
| 0x19ad30 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ad34: stp x12,x13,[x5, #-0x10] *)
| 0x19ad34 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad38: ldp x8,x9,[x4, #-0x20] *)
| 0x19ad38 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19ad3c: ldp x10,x11,[x4, #-0x30] *)
| 0x19ad3c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19ad40: ldp x12,x13,[x4, #-0x40]! *)
| 0x19ad40 => Some (4,
	Move R_X4 (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_X4) LittleE 8) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0)) $;
	Move R_X13 (Var (V_TEMP 2))
)
(* 0x19ad44: sub x5,x5,x14 *)
| 0x19ad44 => Some (4,
	Move R_X5 (BinOp OP_MINUS (Var R_X5) (Var R_X14))
)
(* 0x19ad48: subs x2,x2,#0x80 *)
| 0x19ad48 => Some (4,
	Move (V_TEMP 0) (Word 0x80 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ad4c: b.ls 0x0019ad78 *)
| 0x19ad4c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_CY) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 0)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ad78 64)) (Nop)
)
(* 0x19ad50: stp x6,x7,[x5, #-0x10] *)
| 0x19ad50 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad54: ldp x6,x7,[x4, #-0x10] *)
| 0x19ad54 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ad58: stp x8,x9,[x5, #-0x20] *)
| 0x19ad58 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad5c: ldp x8,x9,[x4, #-0x20] *)
| 0x19ad5c => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19ad60: stp x10,x11,[x5, #-0x30] *)
| 0x19ad60 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad64: ldp x10,x11,[x4, #-0x30] *)
| 0x19ad64 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19ad68: stp x12,x13,[x5, #-0x40]! *)
| 0x19ad68 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move R_X5 (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X5) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad6c: ldp x12,x13,[x4, #-0x40]! *)
| 0x19ad6c => Some (4,
	Move R_X4 (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_X4) LittleE 8) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0)) $;
	Move R_X13 (Var (V_TEMP 2))
)
(* 0x19ad70: subs x2,x2,#0x40 *)
| 0x19ad70 => Some (4,
	Move (V_TEMP 0) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19ad74: b.hi 0x0019ad50 *)
| 0x19ad74 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19ad50 64)) (Nop)
)
(* 0x19ad78: ldp x2,x3,[x1, #0x30] *)
| 0x19ad78 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X2 (Var (V_TEMP 1)) $;
	Move R_X3 (Var (V_TEMP 3))
)
(* 0x19ad7c: stp x6,x7,[x5, #-0x10] *)
| 0x19ad7c => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad80: ldp x6,x7,[x1, #0x20] *)
| 0x19ad80 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 1)) $;
	Move R_X7 (Var (V_TEMP 3))
)
(* 0x19ad84: stp x8,x9,[x5, #-0x20] *)
| 0x19ad84 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad88: ldp x8,x9,[x1, #0x10] *)
| 0x19ad88 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 1)) $;
	Move R_X9 (Var (V_TEMP 3))
)
(* 0x19ad8c: stp x10,x11,[x5, #-0x30] *)
| 0x19ad8c => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad90: ldp x10,x11,[x1] *)
| 0x19ad90 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 1)) $;
	Move R_X11 (Var (V_TEMP 3))
)
(* 0x19ad94: stp x12,x13,[x5, #-0x40] *)
| 0x19ad94 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	Move (V_TEMP 1) (Var R_X13) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad98: stp x2,x3,[x0, #0x30] *)
| 0x19ad98 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move (V_TEMP 1) (Var R_X3) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ad9c: stp x6,x7,[x0, #0x20] *)
| 0x19ad9c => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move (V_TEMP 1) (Var R_X7) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ada0: stp x8,x9,[x0, #0x10] *)
| 0x19ada0 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move (V_TEMP 1) (Var R_X9) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ada4: stp x10,x11,[x0] *)
| 0x19ada4 => Some (4,
	Move (V_TEMP 0) (Var R_X10) $;
	Move (V_TEMP 1) (Var R_X11) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19ada8: ret *)
| 0x19ada8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08___memmove_generic_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
