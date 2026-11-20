(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: __memset_emag; entry: 0x19c300; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e08___memset_emag_arm8 : program := fun _ a => match a with
(* 0x19c300: nop *)
| 0x19c300 => Some (4,
	Nop
)
(* 0x19c304: bfm w1,w1,#0x18,#0x7 *)
| 0x19c304 => Some (4,
	Move (V_TEMP 0) (Word 0xff00 32) $;
	Move (V_TEMP 1) (Word 0xffff 32) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x18 32)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x20 32) (Word 0x18 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 15) (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 15)))
)
(* 0x19c308: bfm w1,w1,#0x10,#0xf *)
| 0x19c308 => Some (4,
	Move (V_TEMP 0) (Word 0xffff0000 32) $;
	Move (V_TEMP 1) (Word 0xffffffff 32) $;
	Move (V_TEMP 2) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x10 32)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 15) (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 15)))
)
(* 0x19c30c: bfm x1,x1,#0x20,#0x1f *)
| 0x19c30c => Some (4,
	Move (V_TEMP 0) (Word 0xffffffff00000000 64) $;
	Move (V_TEMP 1) (Word 0xffffffffffffffff 64) $;
	Move (V_TEMP 2) (Var R_X1) $;
	Move (V_TEMP 3) (Var R_X1) $;
	Move (V_TEMP 4) (UnOp OP_NOT (Var (V_TEMP 0))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 0x20 64)) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Word 0x40 64) (Word 0x20 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 10) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 0))) $;
	Move (V_TEMP 11) (BinOp OP_OR (Var (V_TEMP 5)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (UnOp OP_NOT (Var (V_TEMP 1))) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 12))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 11)) (Var (V_TEMP 1))) $;
	Move R_X1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))
)
(* 0x19c310: add x4,x0,x2 *)
| 0x19c310 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 1))
)
(* 0x19c314: cmp x2,#0x60 *)
| 0x19c314 => Some (4,
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
(* 0x19c318: b.hi 0x0019c3a0 *)
| 0x19c318 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (Jmp (Word 0x19c3a0 64)) (Nop)
)
(* 0x19c31c: cmp x2,#0x10 *)
| 0x19c31c => Some (4,
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
(* 0x19c320: b.cs 0x0019c360 *)
| 0x19c320 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (Jmp (Word 0x19c360 64)) (Nop)
)
(* 0x19c324: tbz w2,#0x3,0x0019c338 *)
| 0x19c324 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x3 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c338 64)) (Nop)
)
(* 0x19c328: str x1,[x0] *)
| 0x19c328 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var R_X1) LittleE 8)
)
(* 0x19c32c: stur x1,[x4, #-0x8] *)
| 0x19c32c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x19c330: ret *)
| 0x19c330 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c334: nop *)
| 0x19c334 => Some (4,
	Nop
)
(* 0x19c338: tbz w2,#0x2,0x0019c348 *)
| 0x19c338 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x2 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c348 64)) (Nop)
)
(* 0x19c33c: str w1,[x0] *)
| 0x19c33c => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Extract 31 0 (Var R_X1)) LittleE 4)
)
(* 0x19c340: stur w1,[x4, #-0x4] *)
| 0x19c340 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 0)) LittleE 4)
)
(* 0x19c344: ret *)
| 0x19c344 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c348: cbz x2,0x0019c358 *)
| 0x19c348 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X2) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19c358 64)) (Nop)
)
(* 0x19c34c: strb w1,[x0] *)
| 0x19c34c => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (Var R_X0) $;
	Move (V_TEMP 2) (Extract 7 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 2)) LittleE 1)
)
(* 0x19c350: tbz w2,#0x1,0x0019c358 *)
| 0x19c350 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c358 64)) (Nop)
)
(* 0x19c354: sturh w1,[x4, #-0x2] *)
| 0x19c354 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffe 64)) $;
	Move (V_TEMP 2) (Extract 15 0 (Var (V_TEMP 0))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 2)) LittleE 2)
)
(* 0x19c358: ret *)
| 0x19c358 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c35c: nop *)
| 0x19c35c => Some (4,
	Nop
)
(* 0x19c360: stp x1,x1,[x0] *)
| 0x19c360 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c364: tbnz w2,#0x6,0x0019c380 *)
| 0x19c364 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x6 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c380 64)) (Nop)
)
(* 0x19c368: stp x1,x1,[x4, #-0x10] *)
| 0x19c368 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c36c: tbz w2,#0x5,0x0019c378 *)
| 0x19c36c => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x5 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c378 64)) (Nop)
)
(* 0x19c370: stp x1,x1,[x0, #0x10] *)
| 0x19c370 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c374: stp x1,x1,[x4, #-0x20] *)
| 0x19c374 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c378: ret *)
| 0x19c378 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c37c: nop *)
| 0x19c37c => Some (4,
	Nop
)
(* 0x19c380: stp x1,x1,[x0, #0x10] *)
| 0x19c380 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c384: stp x1,x1,[x0, #0x20] *)
| 0x19c384 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c388: stp x1,x1,[x0, #0x30] *)
| 0x19c388 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c38c: stp x1,x1,[x4, #-0x20] *)
| 0x19c38c => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c390: stp x1,x1,[x4, #-0x10] *)
| 0x19c390 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c394: ret *)
| 0x19c394 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c398: nop *)
| 0x19c398 => Some (4,
	Nop
)
(* 0x19c39c: nop *)
| 0x19c39c => Some (4,
	Nop
)
(* 0x19c3a0: stp x1,x1,[x0] *)
| 0x19c3a0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3a4: and x3,x0,#-0x10 *)
| 0x19c3a4 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)
(* 0x19c3a8: sub x2,x4,x3 *)
| 0x19c3a8 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X4) (Var R_X3))
)
(* 0x19c3ac: sub x2,x2,#0x51 *)
| 0x19c3ac => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x51 64))
)
(* 0x19c3b0: stp x1,x1,[x3, #0x10] *)
| 0x19c3b0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3b4: stp x1,x1,[x3, #0x20] *)
| 0x19c3b4 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3b8: stp x1,x1,[x3, #0x30] *)
| 0x19c3b8 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3bc: stp x1,x1,[x3, #0x40]! *)
| 0x19c3bc => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X3) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3c0: subs x2,x2,#0x40 *)
| 0x19c3c0 => Some (4,
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
(* 0x19c3c4: b.cs 0x0019c3b0 *)
| 0x19c3c4 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (Jmp (Word 0x19c3b0 64)) (Nop)
)
(* 0x19c3c8: tbz w2,#0x5,0x0019c3d4 *)
| 0x19c3c8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x5 32)) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 3))) (Jmp (Word 0x19c3d4 64)) (Nop)
)
(* 0x19c3cc: stp x1,x1,[x3, #0x10] *)
| 0x19c3cc => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3d0: stp x1,x1,[x3, #0x20] *)
| 0x19c3d0 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3d4: stp x1,x1,[x4, #-0x20] *)
| 0x19c3d4 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3d8: stp x1,x1,[x4, #-0x10] *)
| 0x19c3d8 => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move (V_TEMP 1) (Var R_X1) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 3) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 3)) (Var (V_TEMP 1)) LittleE 8)
)
(* 0x19c3dc: ret *)
| 0x19c3dc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e08___memset_emag_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
