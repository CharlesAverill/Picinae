(* Strict AMD64 copy256 sequential projection, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: synthetic; ELF SHA256: 80d54e559d7069c8214eab668066f8ddc850305f96d9598817eb04f46f8db52c
Symbol: zero; global entry: 0x1010e8; selected: legacy, vex128, vex256, zero
Profile: copy256 (CET-enabled execution is outside this model).
Scope: selected-function-extents; <=256 projection of ZMM0..15 only.
CPU enabled, nonfaulting aligned accesses where required; NT stores sequential only.
Upper>256, faults, ordering/cache/timing and CET-enabled execution excluded.
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e26_zero_amd64 : program := fun _ a => match a with
(* 0x101000: MOVDQU XMM0,xmmword ptr [RSI] *)
| 0x101000 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101004: MOVDQU xmmword ptr [RDI],XMM0 *)
| 0x101004 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x101008: MOVDQU XMM1,XMM0 *)
| 0x101008 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (Var R_YMM0)))
)
(* 0x10100c: MOVDQU XMM1,XMM1 *)
| 0x10100c => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (Var R_YMM1)))
)
(* 0x101010: MOVDQA XMM9,xmmword ptr [RSI + RCX*0x2 + -0x10] *)
| 0x101010 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RSI)) (Word 0xfffffffffffffff0 64)) LittleE 16))
)
(* 0x101017: MOVDQA xmmword ptr [RDI + 0x10],XMM9 *)
| 0x101017 => Some (6,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Extract 127 0 (Var R_YMM9)) LittleE 16)
)
(* 0x10101d: MOVDQA XMM8,XMM9 *)
| 0x10101d => Some (5,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9)))
)
(* 0x101022: MOVUPS XMM2,xmmword ptr [RSI] *)
| 0x101022 => Some (3,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101025: MOVUPS xmmword ptr [RDI],XMM2 *)
| 0x101025 => Some (3,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM2)) LittleE 16)
)
(* 0x101028: MOVUPS XMM3,XMM2 *)
| 0x101028 => Some (3,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2)))
)
(* 0x10102b: MOVUPS XMM2,XMM2 *)
| 0x10102b => Some (3,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (Var R_YMM2)))
)
(* 0x10102e: MOVAPS XMM4,xmmword ptr [RSI] *)
| 0x10102e => Some (3,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101031: MOVAPS xmmword ptr [RDI],XMM4 *)
| 0x101031 => Some (3,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM4)) LittleE 16)
)
(* 0x101034: MOVAPS XMM5,XMM4 *)
| 0x101034 => Some (3,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4)))
)
(* 0x101037: MOVAPS XMM4,XMM4 *)
| 0x101037 => Some (3,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (Var R_YMM4)))
)
(* 0x10103a: MOVNTDQ xmmword ptr [RDI],XMM5 *)
| 0x10103a => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM5)) LittleE 16)
)
(* 0x10103e: MOVDQU XMM15,xmmword ptr [0x1000 + RCX*0x4] *)
| 0x10103e => Some (10,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x4 64)) (Word 0x1000 64)) LittleE 16))
)
(* 0x101048: MOVDQU XMM14,xmmword ptr [0x00103000] *)
| 0x101048 => Some (9,
	Move R_YMM14 (Concat (Extract 255 128 (Var R_YMM14)) (Load (Var V_MEM64) (Word 0x103000 64) LittleE 16))
)
(* 0x101051: MOVDQU XMM13,xmmword ptr [R13 + R12*0x8 + -0x1000] *)
| 0x101051 => Some (10,
	Move R_YMM13 (Concat (Extract 255 128 (Var R_YMM13)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_R12) (Word 0x8 64)) (Var R_R13)) (Word 0xfffffffffffff000 64)) LittleE 16))
)
(* 0x10105b: MOVDQU XMM1,XMM0 *)
| 0x10105b => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (Var R_YMM0)))
)
(* 0x10105f: RET *)
| 0x10105f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x101060: VMOVDQU XMM0,xmmword ptr [RSI] *)
| 0x101060 => Some (4,
	Move R_YMM0 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101064: VMOVDQU xmmword ptr [RDI],XMM0 *)
| 0x101064 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM0)) LittleE 16)
)
(* 0x101068: VMOVDQU XMM1,XMM0 *)
| 0x101068 => Some (4,
	Move R_YMM1 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM0)))
)
(* 0x10106c: VMOVDQU XMM1,XMM1 *)
| 0x10106c => Some (4,
	Move R_YMM1 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM1)))
)
(* 0x101070: VMOVDQA XMM9,xmmword ptr [RSI + RCX*0x2 + -0x10] *)
| 0x101070 => Some (6,
	Move R_YMM9 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RSI)) (Word 0xfffffffffffffff0 64)) LittleE 16))
)
(* 0x101076: VMOVDQA xmmword ptr [RDI + 0x10],XMM9 *)
| 0x101076 => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Extract 127 0 (Var R_YMM9)) LittleE 16)
)
(* 0x10107b: VMOVDQA XMM8,XMM9 *)
| 0x10107b => Some (5,
	Move R_YMM8 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM9)))
)
(* 0x101080: VMOVUPS XMM2,xmmword ptr [RSI] *)
| 0x101080 => Some (4,
	Move R_YMM2 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101084: VMOVUPS xmmword ptr [RDI],XMM2 *)
| 0x101084 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM2)) LittleE 16)
)
(* 0x101088: VMOVUPS XMM3,XMM2 *)
| 0x101088 => Some (4,
	Move R_YMM3 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM2)))
)
(* 0x10108c: VMOVAPS XMM4,xmmword ptr [RSI] *)
| 0x10108c => Some (4,
	Move R_YMM4 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101090: VMOVAPS xmmword ptr [RDI],XMM4 *)
| 0x101090 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM4)) LittleE 16)
)
(* 0x101094: VMOVAPS XMM5,XMM4 *)
| 0x101094 => Some (4,
	Move R_YMM5 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM4)))
)
(* 0x101098: VMOVNTDQ xmmword ptr [RDI],XMM5 *)
| 0x101098 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Extract 127 0 (Var R_YMM5)) LittleE 16)
)
(* 0x10109c: VMOVDQU XMM15,xmmword ptr [R13 + R12*0x8 + -0x1000] *)
| 0x10109c => Some (10,
	Move R_YMM15 (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_R12) (Word 0x8 64)) (Var R_R13)) (Word 0xfffffffffffff000 64)) LittleE 16))
)
(* 0x1010a6: VMOVDQU XMM1,XMM0 *)
| 0x1010a6 => Some (4,
	Move R_YMM1 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM0)))
)
(* 0x1010aa: RET *)
| 0x1010aa => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x1010ab: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x1010ab => Some (4,
	Move R_YMM0 (Load (Var V_MEM64) (Var R_RSI) LittleE 32)
)
(* 0x1010af: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x1010af => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM0) LittleE 32)
)
(* 0x1010b3: VMOVDQU YMM1,YMM0 *)
| 0x1010b3 => Some (4,
	Move R_YMM1 (Var R_YMM0)
)
(* 0x1010b7: VMOVDQU YMM1,YMM1 *)
| 0x1010b7 => Some (4,
	Move R_YMM1 (Var R_YMM1)
)
(* 0x1010bb: VMOVDQA YMM9,ymmword ptr [RSI + RCX*0x2 + -0x20] *)
| 0x1010bb => Some (6,
	Move R_YMM9 (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RSI)) (Word 0xffffffffffffffe0 64)) LittleE 32)
)
(* 0x1010c1: VMOVDQA ymmword ptr [RDI + 0x20],YMM9 *)
| 0x1010c1 => Some (5,
	Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) (Var R_YMM9) LittleE 32)
)
(* 0x1010c6: VMOVDQA YMM8,YMM9 *)
| 0x1010c6 => Some (5,
	Move R_YMM8 (Var R_YMM9)
)
(* 0x1010cb: VMOVUPS YMM2,ymmword ptr [RSI] *)
| 0x1010cb => Some (4,
	Move R_YMM2 (Load (Var V_MEM64) (Var R_RSI) LittleE 32)
)
(* 0x1010cf: VMOVUPS ymmword ptr [RDI],YMM2 *)
| 0x1010cf => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM2) LittleE 32)
)
(* 0x1010d3: VMOVUPS YMM3,YMM2 *)
| 0x1010d3 => Some (4,
	Move R_YMM3 (Var R_YMM2)
)
(* 0x1010d7: VMOVAPS YMM4,ymmword ptr [RSI] *)
| 0x1010d7 => Some (4,
	Move R_YMM4 (Load (Var V_MEM64) (Var R_RSI) LittleE 32)
)
(* 0x1010db: VMOVAPS ymmword ptr [RDI],YMM4 *)
| 0x1010db => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM4) LittleE 32)
)
(* 0x1010df: VMOVAPS YMM5,YMM4 *)
| 0x1010df => Some (4,
	Move R_YMM5 (Var R_YMM4)
)
(* 0x1010e3: VMOVNTDQ ymmword ptr [RDI],YMM5 *)
| 0x1010e3 => Some (4,
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var R_YMM5) LittleE 32)
)
(* 0x1010e7: RET *)
| 0x1010e7 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x1010e8: VZEROUPPER *)
| 0x1010e8 => Some (3,
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
(* 0x1010eb: RET *)
| 0x1010eb => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e26_zero_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
