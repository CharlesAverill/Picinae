(* Strict AMD64 copy256 sequential projection, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: glibc-instructions; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
Symbol: pinned_moves; global entry: 0x1c4881; selected: pinned_moves
Profile: copy256 (CET-enabled execution is outside this model).
Scope: isolated-instruction-fixtures; <=256 projection of ZMM0..15 only.
CPU enabled, nonfaulting aligned accesses where required; NT stores sequential only.
Upper>256, faults, ordering/cache/timing and CET-enabled execution excluded.
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e26_pinned_moves_amd64 : program := fun _ a => match a with
(* 0x1c4881: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4881 => Some (3,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x1c4893: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c4893 => Some (3,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x1c4ab8: MOVUPS XMM8,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x1c4ab8 => Some (6,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (Var R_RDX) (Var R_RSI)) (Word 0xffffffffffffffc0 64)) LittleE 16))
)
(* 0x1c4ae3: MOVAPS xmmword ptr [RDI],XMM1 *)
| 0x1c4ae3 => Some (3,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM1)) LittleE 16)
)
(* 0x1c4b07: MOVUPS xmmword ptr [RDX],XMM8 *)
| 0x1c4b07 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDX) (Extract 127 0 (Var R_YMM8)) LittleE 16)
)
(* 0x1c4c6d: MOVNTDQ xmmword ptr [RDI],XMM0 *)
| 0x1c4c6d => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x1c4e00: MOVNTDQ xmmword ptr [RDI + 0x2000],XMM8 *)
| 0x1c4e00 => Some (9,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x2000 64)) (Extract 127 0 (Var R_YMM8)) LittleE 16)
)
(* 0x27acb5: MOVDQU XMM0,xmmword ptr [RSI] *)
| 0x27acb5 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x27ad74: MOVDQA XMM1,xmmword ptr [RSI] *)
| 0x27ad74 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x27ad7c: MOVDQA xmmword ptr [RDI],XMM1 *)
| 0x27ad7c => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM1)) LittleE 16)
)
(* 0x27ad8b: MOVDQU xmmword ptr [R8],XMM0 *)
| 0x27ad8b => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R8) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x27ad98: MOVAPS XMM4,xmmword ptr [RSI] *)
| 0x27ad98 => Some (3,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x27b1fc: MOVDQA XMM6,XMM5 *)
| 0x27b1fc => Some (4,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5)))
)
(* 0x27b2cc: MOVAPS XMM1,XMM5 *)
| 0x27b2cc => Some (3,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (Var R_YMM5)))
)
(* 0x27c58e: MOVDQU xmmword ptr [RDI + -0x48],XMM0 *)
| 0x27c58e => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffb8 64)) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x280463: MOVAPS XMM8,xmmword ptr [RSI + 0x6f] *)
| 0x280463 => Some (5,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RSI) (Word 0x6f 64)) LittleE 16))
)
(* 0x28047b: MOVAPS xmmword ptr [RDI + 0x70],XMM9 *)
| 0x28047b => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x70 64)) (Extract 127 0 (Var R_YMM9)) LittleE 16)
)
(* 0x281cdf: MOVDQU XMM8,xmmword ptr [RSI + -0x80] *)
| 0x281cdf => Some (6,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffff80 64)) LittleE 16))
)
(* 0x281dab: MOVDQA xmmword ptr [RDI + -0x80],XMM8 *)
| 0x281dab => Some (6,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Extract 127 0 (Var R_YMM8)) LittleE 16)
)
(* 0x2a07c1: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x2a07c1 => Some (4,
	Move R_YMM0 (Load (Var V_MEM64) (Var R_RSI) LittleE 32)
)
(* 0x2a07d5: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x2a07d5 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM0) LittleE 32)
)
(* 0x2a07df: VZEROUPPER *)
| 0x2a07df => Some (3,
	Move R_YMM0 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM0))) $;
	Move R_YMM1 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM1))) $;
	Move R_YMM2 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM2))) $;
	Move R_YMM3 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM3))) $;
	Move R_YMM4 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM4))) $;
	Move R_YMM5 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM5))) $;
	Move R_YMM6 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM6))) $;
	Move R_YMM7 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM7))) $;
	Move R_YMM8 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM8))) $;
	Move R_YMM9 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM9))) $;
	Move R_YMM10 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM10))) $;
	Move R_YMM11 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM11))) $;
	Move R_YMM12 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM12))) $;
	Move R_YMM13 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM13))) $;
	Move R_YMM14 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM14))) $;
	Move R_YMM15 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM15)))
)
(* 0x2a08a2: VMOVDQU XMM0,xmmword ptr [RSI] *)
| 0x2a08a2 => Some (4,
	Move R_YMM0 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x2a08ac: VMOVDQU xmmword ptr [RDI],XMM0 *)
| 0x2a08ac => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x2a09c4: VMOVDQU YMM8,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x2a09c4 => Some (6,
	Move R_YMM8 (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (Var R_RDX) (Var R_RSI)) (Word 0xffffffffffffff80 64)) LittleE 32)
)
(* 0x2a09f7: VMOVDQA ymmword ptr [RDI],YMM1 *)
| 0x2a09f7 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM1) LittleE 32)
)
(* 0x2a0a22: VMOVDQU ymmword ptr [RDX],YMM8 *)
| 0x2a0a22 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDX) (Var R_YMM8) LittleE 32)
)
(* 0x2a0ae6: VMOVDQU ymmword ptr [R8],YMM0 *)
| 0x2a0ae6 => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R8) (Var R_YMM0) LittleE 32)
)
(* 0x2a0c44: VMOVNTDQ ymmword ptr [RDI],YMM0 *)
| 0x2a0c44 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM0) LittleE 32)
)
(* 0x2a0e27: VMOVNTDQ ymmword ptr [RDI + 0x2000],YMM8 *)
| 0x2a0e27 => Some (8,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x2000 64)) (Var R_YMM8) LittleE 32)
)
(* 0x2a3e1e: VMOVDQU xmmword ptr [R9 + -0x10],XMM1 *)
| 0x2a3e1e => Some (6,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_R9) (Word 0xfffffffffffffff0 64)) (Extract 127 0 (Var R_YMM1)) LittleE 16)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e26_pinned_moves_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
