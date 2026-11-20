(* Strict AMD64 shuffle128 sequential projection, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: glibc-instructions; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
Symbol: pinned_shuffles; global entry: 0x27b200; selected: pinned_shuffles
Profile: shuffle128 (CET-enabled execution is outside this model).
Scope: isolated-instruction-fixtures; <=256 projection of ZMM0..15 only.
SSSE3 and OS vector state enabled; nonfaulting full-width accesses, architectural alignment required. New shuffle forms: legacy PALIGNR only; VEX shuffles/PSHUFB/MMX/EVEX rejected.
Upper>256, faults, ordering/cache/timing and CET-enabled execution excluded.
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e34_pinned_shuffles_amd64 : program := fun _ a => match a with
(* 0x27b200: PALIGNR XMM5,XMM4,0x1 *)
| 0x27b200 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x8 256))))
)
(* 0x27b20a: PALIGNR XMM4,XMM3,0x1 *)
| 0x27b20a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x8 256))))
)
(* 0x27b210: PALIGNR XMM3,XMM2,0x1 *)
| 0x27b210 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x8 256))))
)
(* 0x27b21a: PALIGNR XMM2,XMM1,0x1 *)
| 0x27b21a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x8 256))))
)
(* 0x27b2b0: PALIGNR XMM1,XMM2,0x1 *)
| 0x27b2b0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x8 256))))
)
(* 0x27b2b6: PALIGNR XMM2,XMM3,0x1 *)
| 0x27b2b6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x8 256))))
)
(* 0x27b2bc: PALIGNR XMM3,XMM4,0x1 *)
| 0x27b2bc => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x8 256))))
)
(* 0x27b2c2: PALIGNR XMM4,XMM5,0x1 *)
| 0x27b2c2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x8 256))))
)
(* 0x27b350: PALIGNR XMM5,XMM4,0x2 *)
| 0x27b350 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x10 256))))
)
(* 0x27b35a: PALIGNR XMM4,XMM3,0x2 *)
| 0x27b35a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x10 256))))
)
(* 0x27b360: PALIGNR XMM3,XMM2,0x2 *)
| 0x27b360 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x10 256))))
)
(* 0x27b36a: PALIGNR XMM2,XMM1,0x2 *)
| 0x27b36a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x10 256))))
)
(* 0x27b400: PALIGNR XMM1,XMM2,0x2 *)
| 0x27b400 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x10 256))))
)
(* 0x27b406: PALIGNR XMM2,XMM3,0x2 *)
| 0x27b406 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x10 256))))
)
(* 0x27b40c: PALIGNR XMM3,XMM4,0x2 *)
| 0x27b40c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x10 256))))
)
(* 0x27b412: PALIGNR XMM4,XMM5,0x2 *)
| 0x27b412 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x10 256))))
)
(* 0x27b4a0: PALIGNR XMM5,XMM4,0x3 *)
| 0x27b4a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x18 256))))
)
(* 0x27b4aa: PALIGNR XMM4,XMM3,0x3 *)
| 0x27b4aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x18 256))))
)
(* 0x27b4b0: PALIGNR XMM3,XMM2,0x3 *)
| 0x27b4b0 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x18 256))))
)
(* 0x27b4ba: PALIGNR XMM2,XMM1,0x3 *)
| 0x27b4ba => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x18 256))))
)
(* 0x27b550: PALIGNR XMM1,XMM2,0x3 *)
| 0x27b550 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x18 256))))
)
(* 0x27b556: PALIGNR XMM2,XMM3,0x3 *)
| 0x27b556 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x18 256))))
)
(* 0x27b55c: PALIGNR XMM3,XMM4,0x3 *)
| 0x27b55c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x18 256))))
)
(* 0x27b562: PALIGNR XMM4,XMM5,0x3 *)
| 0x27b562 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x18 256))))
)
(* 0x27b5f0: PALIGNR XMM5,XMM4,0x4 *)
| 0x27b5f0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x20 256))))
)
(* 0x27b5fa: PALIGNR XMM4,XMM3,0x4 *)
| 0x27b5fa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x20 256))))
)
(* 0x27b600: PALIGNR XMM3,XMM2,0x4 *)
| 0x27b600 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x20 256))))
)
(* 0x27b60a: PALIGNR XMM2,XMM1,0x4 *)
| 0x27b60a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x20 256))))
)
(* 0x27b6a0: PALIGNR XMM1,XMM2,0x4 *)
| 0x27b6a0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x20 256))))
)
(* 0x27b6a6: PALIGNR XMM2,XMM3,0x4 *)
| 0x27b6a6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x20 256))))
)
(* 0x27b6ac: PALIGNR XMM3,XMM4,0x4 *)
| 0x27b6ac => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x20 256))))
)
(* 0x27b6b2: PALIGNR XMM4,XMM5,0x4 *)
| 0x27b6b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x20 256))))
)
(* 0x27b740: PALIGNR XMM5,XMM4,0x5 *)
| 0x27b740 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x28 256))))
)
(* 0x27b74a: PALIGNR XMM4,XMM3,0x5 *)
| 0x27b74a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x28 256))))
)
(* 0x27b750: PALIGNR XMM3,XMM2,0x5 *)
| 0x27b750 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x28 256))))
)
(* 0x27b75a: PALIGNR XMM2,XMM1,0x5 *)
| 0x27b75a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x28 256))))
)
(* 0x27b7f0: PALIGNR XMM1,XMM2,0x5 *)
| 0x27b7f0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x28 256))))
)
(* 0x27b7f6: PALIGNR XMM2,XMM3,0x5 *)
| 0x27b7f6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x28 256))))
)
(* 0x27b7fc: PALIGNR XMM3,XMM4,0x5 *)
| 0x27b7fc => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x28 256))))
)
(* 0x27b802: PALIGNR XMM4,XMM5,0x5 *)
| 0x27b802 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x28 256))))
)
(* 0x27b890: PALIGNR XMM5,XMM4,0x6 *)
| 0x27b890 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x30 256))))
)
(* 0x27b89a: PALIGNR XMM4,XMM3,0x6 *)
| 0x27b89a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x30 256))))
)
(* 0x27b8a0: PALIGNR XMM3,XMM2,0x6 *)
| 0x27b8a0 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x30 256))))
)
(* 0x27b8aa: PALIGNR XMM2,XMM1,0x6 *)
| 0x27b8aa => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x30 256))))
)
(* 0x27b940: PALIGNR XMM1,XMM2,0x6 *)
| 0x27b940 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x30 256))))
)
(* 0x27b946: PALIGNR XMM2,XMM3,0x6 *)
| 0x27b946 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x30 256))))
)
(* 0x27b94c: PALIGNR XMM3,XMM4,0x6 *)
| 0x27b94c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x30 256))))
)
(* 0x27b952: PALIGNR XMM4,XMM5,0x6 *)
| 0x27b952 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x30 256))))
)
(* 0x27b9e0: PALIGNR XMM5,XMM4,0x7 *)
| 0x27b9e0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x38 256))))
)
(* 0x27b9ea: PALIGNR XMM4,XMM3,0x7 *)
| 0x27b9ea => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x38 256))))
)
(* 0x27b9f0: PALIGNR XMM3,XMM2,0x7 *)
| 0x27b9f0 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x38 256))))
)
(* 0x27b9fa: PALIGNR XMM2,XMM1,0x7 *)
| 0x27b9fa => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x38 256))))
)
(* 0x27ba90: PALIGNR XMM1,XMM2,0x7 *)
| 0x27ba90 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x38 256))))
)
(* 0x27ba96: PALIGNR XMM2,XMM3,0x7 *)
| 0x27ba96 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x38 256))))
)
(* 0x27ba9c: PALIGNR XMM3,XMM4,0x7 *)
| 0x27ba9c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x38 256))))
)
(* 0x27baa2: PALIGNR XMM4,XMM5,0x7 *)
| 0x27baa2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x38 256))))
)
(* 0x27bb2e: PALIGNR XMM5,XMM4,0x8 *)
| 0x27bb2e => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x40 256))))
)
(* 0x27bb38: PALIGNR XMM4,XMM3,0x8 *)
| 0x27bb38 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x40 256))))
)
(* 0x27bb3e: PALIGNR XMM3,XMM2,0x8 *)
| 0x27bb3e => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x40 256))))
)
(* 0x27bb48: PALIGNR XMM2,XMM1,0x8 *)
| 0x27bb48 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x40 256))))
)
(* 0x27bbe0: PALIGNR XMM1,XMM2,0x8 *)
| 0x27bbe0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x40 256))))
)
(* 0x27bbe6: PALIGNR XMM2,XMM3,0x8 *)
| 0x27bbe6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x40 256))))
)
(* 0x27bbec: PALIGNR XMM3,XMM4,0x8 *)
| 0x27bbec => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x40 256))))
)
(* 0x27bbf2: PALIGNR XMM4,XMM5,0x8 *)
| 0x27bbf2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x40 256))))
)
(* 0x27bc80: PALIGNR XMM5,XMM4,0x9 *)
| 0x27bc80 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x48 256))))
)
(* 0x27bc8a: PALIGNR XMM4,XMM3,0x9 *)
| 0x27bc8a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x48 256))))
)
(* 0x27bc90: PALIGNR XMM3,XMM2,0x9 *)
| 0x27bc90 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x48 256))))
)
(* 0x27bc9a: PALIGNR XMM2,XMM1,0x9 *)
| 0x27bc9a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x48 256))))
)
(* 0x27bd30: PALIGNR XMM1,XMM2,0x9 *)
| 0x27bd30 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x48 256))))
)
(* 0x27bd36: PALIGNR XMM2,XMM3,0x9 *)
| 0x27bd36 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x48 256))))
)
(* 0x27bd3c: PALIGNR XMM3,XMM4,0x9 *)
| 0x27bd3c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x48 256))))
)
(* 0x27bd42: PALIGNR XMM4,XMM5,0x9 *)
| 0x27bd42 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x48 256))))
)
(* 0x27bdd0: PALIGNR XMM5,XMM4,0xa *)
| 0x27bdd0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x50 256))))
)
(* 0x27bdda: PALIGNR XMM4,XMM3,0xa *)
| 0x27bdda => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x50 256))))
)
(* 0x27bde0: PALIGNR XMM3,XMM2,0xa *)
| 0x27bde0 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x50 256))))
)
(* 0x27bdea: PALIGNR XMM2,XMM1,0xa *)
| 0x27bdea => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x50 256))))
)
(* 0x27be80: PALIGNR XMM1,XMM2,0xa *)
| 0x27be80 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x50 256))))
)
(* 0x27be86: PALIGNR XMM2,XMM3,0xa *)
| 0x27be86 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x50 256))))
)
(* 0x27be8c: PALIGNR XMM3,XMM4,0xa *)
| 0x27be8c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x50 256))))
)
(* 0x27be92: PALIGNR XMM4,XMM5,0xa *)
| 0x27be92 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x50 256))))
)
(* 0x27bf20: PALIGNR XMM5,XMM4,0xb *)
| 0x27bf20 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x58 256))))
)
(* 0x27bf2a: PALIGNR XMM4,XMM3,0xb *)
| 0x27bf2a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x58 256))))
)
(* 0x27bf30: PALIGNR XMM3,XMM2,0xb *)
| 0x27bf30 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x58 256))))
)
(* 0x27bf3a: PALIGNR XMM2,XMM1,0xb *)
| 0x27bf3a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x58 256))))
)
(* 0x27bfd0: PALIGNR XMM1,XMM2,0xb *)
| 0x27bfd0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x58 256))))
)
(* 0x27bfd6: PALIGNR XMM2,XMM3,0xb *)
| 0x27bfd6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x58 256))))
)
(* 0x27bfdc: PALIGNR XMM3,XMM4,0xb *)
| 0x27bfdc => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x58 256))))
)
(* 0x27bfe2: PALIGNR XMM4,XMM5,0xb *)
| 0x27bfe2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x58 256))))
)
(* 0x27c070: PALIGNR XMM5,XMM4,0xc *)
| 0x27c070 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x60 256))))
)
(* 0x27c07a: PALIGNR XMM4,XMM3,0xc *)
| 0x27c07a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x60 256))))
)
(* 0x27c080: PALIGNR XMM3,XMM2,0xc *)
| 0x27c080 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x60 256))))
)
(* 0x27c08a: PALIGNR XMM2,XMM1,0xc *)
| 0x27c08a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x60 256))))
)
(* 0x27c120: PALIGNR XMM1,XMM2,0xc *)
| 0x27c120 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x60 256))))
)
(* 0x27c126: PALIGNR XMM2,XMM3,0xc *)
| 0x27c126 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x60 256))))
)
(* 0x27c12c: PALIGNR XMM3,XMM4,0xc *)
| 0x27c12c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x60 256))))
)
(* 0x27c132: PALIGNR XMM4,XMM5,0xc *)
| 0x27c132 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x60 256))))
)
(* 0x27c1c0: PALIGNR XMM5,XMM4,0xd *)
| 0x27c1c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x68 256))))
)
(* 0x27c1ca: PALIGNR XMM4,XMM3,0xd *)
| 0x27c1ca => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x68 256))))
)
(* 0x27c1d0: PALIGNR XMM3,XMM2,0xd *)
| 0x27c1d0 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x68 256))))
)
(* 0x27c1da: PALIGNR XMM2,XMM1,0xd *)
| 0x27c1da => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x68 256))))
)
(* 0x27c270: PALIGNR XMM1,XMM2,0xd *)
| 0x27c270 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x68 256))))
)
(* 0x27c276: PALIGNR XMM2,XMM3,0xd *)
| 0x27c276 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x68 256))))
)
(* 0x27c27c: PALIGNR XMM3,XMM4,0xd *)
| 0x27c27c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x68 256))))
)
(* 0x27c282: PALIGNR XMM4,XMM5,0xd *)
| 0x27c282 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x68 256))))
)
(* 0x27c310: PALIGNR XMM5,XMM4,0xe *)
| 0x27c310 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x70 256))))
)
(* 0x27c31a: PALIGNR XMM4,XMM3,0xe *)
| 0x27c31a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x70 256))))
)
(* 0x27c320: PALIGNR XMM3,XMM2,0xe *)
| 0x27c320 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x70 256))))
)
(* 0x27c32a: PALIGNR XMM2,XMM1,0xe *)
| 0x27c32a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x70 256))))
)
(* 0x27c3c0: PALIGNR XMM1,XMM2,0xe *)
| 0x27c3c0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x70 256))))
)
(* 0x27c3c6: PALIGNR XMM2,XMM3,0xe *)
| 0x27c3c6 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x70 256))))
)
(* 0x27c3cc: PALIGNR XMM3,XMM4,0xe *)
| 0x27c3cc => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x70 256))))
)
(* 0x27c3d2: PALIGNR XMM4,XMM5,0xe *)
| 0x27c3d2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x70 256))))
)
(* 0x27c460: PALIGNR XMM5,XMM4,0xf *)
| 0x27c460 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x78 256))))
)
(* 0x27c46a: PALIGNR XMM4,XMM3,0xf *)
| 0x27c46a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x78 256))))
)
(* 0x27c470: PALIGNR XMM3,XMM2,0xf *)
| 0x27c470 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x78 256))))
)
(* 0x27c47a: PALIGNR XMM2,XMM1,0xf *)
| 0x27c47a => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x78 256))))
)
(* 0x27c510: PALIGNR XMM1,XMM2,0xf *)
| 0x27c510 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x78 256))))
)
(* 0x27c516: PALIGNR XMM2,XMM3,0xf *)
| 0x27c516 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x78 256))))
)
(* 0x27c51c: PALIGNR XMM3,XMM4,0xf *)
| 0x27c51c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x78 256))))
)
(* 0x27c522: PALIGNR XMM4,XMM5,0xf *)
| 0x27c522 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x78 256))))
)
(* 0x280474: PALIGNR XMM9,XMM8,0x1 *)
| 0x280474 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x8 256))))
)
(* 0x280480: PALIGNR XMM8,XMM7,0x1 *)
| 0x280480 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x8 256))))
)
(* 0x28048c: PALIGNR XMM7,XMM6,0x1 *)
| 0x28048c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x8 256))))
)
(* 0x280496: PALIGNR XMM6,XMM5,0x1 *)
| 0x280496 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x8 256))))
)
(* 0x2804a0: PALIGNR XMM5,XMM4,0x1 *)
| 0x2804a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x8 256))))
)
(* 0x2804aa: PALIGNR XMM4,XMM3,0x1 *)
| 0x2804aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x8 256))))
)
(* 0x2804b4: PALIGNR XMM3,XMM2,0x1 *)
| 0x2804b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x8 256))))
)
(* 0x2804be: PALIGNR XMM2,XMM1,0x1 *)
| 0x2804be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x8 256))))
)
(* 0x280508: PALIGNR XMM1,XMM2,0x1 *)
| 0x280508 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x8 256))))
)
(* 0x280516: PALIGNR XMM2,XMM3,0x1 *)
| 0x280516 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x8 256))))
)
(* 0x280524: PALIGNR XMM3,XMM4,0x1 *)
| 0x280524 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x8 256))))
)
(* 0x280532: PALIGNR XMM4,XMM5,0x1 *)
| 0x280532 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x8 256))))
)
(* 0x280540: PALIGNR XMM5,XMM6,0x1 *)
| 0x280540 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x8 256))))
)
(* 0x28054e: PALIGNR XMM6,XMM7,0x1 *)
| 0x28054e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x8 256))))
)
(* 0x28055d: PALIGNR XMM7,XMM8,0x1 *)
| 0x28055d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x8 256))))
)
(* 0x280570: PALIGNR XMM8,XMM9,0x1 *)
| 0x280570 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x8 256))))
)
(* 0x2805f4: PALIGNR XMM9,XMM8,0x2 *)
| 0x2805f4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x10 256))))
)
(* 0x280600: PALIGNR XMM8,XMM7,0x2 *)
| 0x280600 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x10 256))))
)
(* 0x28060c: PALIGNR XMM7,XMM6,0x2 *)
| 0x28060c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x10 256))))
)
(* 0x280616: PALIGNR XMM6,XMM5,0x2 *)
| 0x280616 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x10 256))))
)
(* 0x280620: PALIGNR XMM5,XMM4,0x2 *)
| 0x280620 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x10 256))))
)
(* 0x28062a: PALIGNR XMM4,XMM3,0x2 *)
| 0x28062a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x10 256))))
)
(* 0x280634: PALIGNR XMM3,XMM2,0x2 *)
| 0x280634 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x10 256))))
)
(* 0x28063e: PALIGNR XMM2,XMM1,0x2 *)
| 0x28063e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x10 256))))
)
(* 0x280688: PALIGNR XMM1,XMM2,0x2 *)
| 0x280688 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x10 256))))
)
(* 0x280696: PALIGNR XMM2,XMM3,0x2 *)
| 0x280696 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x10 256))))
)
(* 0x2806a4: PALIGNR XMM3,XMM4,0x2 *)
| 0x2806a4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x10 256))))
)
(* 0x2806b2: PALIGNR XMM4,XMM5,0x2 *)
| 0x2806b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x10 256))))
)
(* 0x2806c0: PALIGNR XMM5,XMM6,0x2 *)
| 0x2806c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x10 256))))
)
(* 0x2806ce: PALIGNR XMM6,XMM7,0x2 *)
| 0x2806ce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x10 256))))
)
(* 0x2806dd: PALIGNR XMM7,XMM8,0x2 *)
| 0x2806dd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x10 256))))
)
(* 0x2806f0: PALIGNR XMM8,XMM9,0x2 *)
| 0x2806f0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x10 256))))
)
(* 0x280774: PALIGNR XMM9,XMM8,0x3 *)
| 0x280774 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x18 256))))
)
(* 0x280780: PALIGNR XMM8,XMM7,0x3 *)
| 0x280780 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x18 256))))
)
(* 0x28078c: PALIGNR XMM7,XMM6,0x3 *)
| 0x28078c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x18 256))))
)
(* 0x280796: PALIGNR XMM6,XMM5,0x3 *)
| 0x280796 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x18 256))))
)
(* 0x2807a0: PALIGNR XMM5,XMM4,0x3 *)
| 0x2807a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x18 256))))
)
(* 0x2807aa: PALIGNR XMM4,XMM3,0x3 *)
| 0x2807aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x18 256))))
)
(* 0x2807b4: PALIGNR XMM3,XMM2,0x3 *)
| 0x2807b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x18 256))))
)
(* 0x2807be: PALIGNR XMM2,XMM1,0x3 *)
| 0x2807be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x18 256))))
)
(* 0x280808: PALIGNR XMM1,XMM2,0x3 *)
| 0x280808 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x18 256))))
)
(* 0x280816: PALIGNR XMM2,XMM3,0x3 *)
| 0x280816 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x18 256))))
)
(* 0x280824: PALIGNR XMM3,XMM4,0x3 *)
| 0x280824 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x18 256))))
)
(* 0x280832: PALIGNR XMM4,XMM5,0x3 *)
| 0x280832 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x18 256))))
)
(* 0x280840: PALIGNR XMM5,XMM6,0x3 *)
| 0x280840 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x18 256))))
)
(* 0x28084e: PALIGNR XMM6,XMM7,0x3 *)
| 0x28084e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x18 256))))
)
(* 0x28085d: PALIGNR XMM7,XMM8,0x3 *)
| 0x28085d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x18 256))))
)
(* 0x280870: PALIGNR XMM8,XMM9,0x3 *)
| 0x280870 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x18 256))))
)
(* 0x2808f4: PALIGNR XMM9,XMM8,0x4 *)
| 0x2808f4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x20 256))))
)
(* 0x280900: PALIGNR XMM8,XMM7,0x4 *)
| 0x280900 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x20 256))))
)
(* 0x28090c: PALIGNR XMM7,XMM6,0x4 *)
| 0x28090c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x20 256))))
)
(* 0x280916: PALIGNR XMM6,XMM5,0x4 *)
| 0x280916 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x20 256))))
)
(* 0x280920: PALIGNR XMM5,XMM4,0x4 *)
| 0x280920 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x20 256))))
)
(* 0x28092a: PALIGNR XMM4,XMM3,0x4 *)
| 0x28092a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x20 256))))
)
(* 0x280934: PALIGNR XMM3,XMM2,0x4 *)
| 0x280934 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x20 256))))
)
(* 0x28093e: PALIGNR XMM2,XMM1,0x4 *)
| 0x28093e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x20 256))))
)
(* 0x280988: PALIGNR XMM1,XMM2,0x4 *)
| 0x280988 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x20 256))))
)
(* 0x280996: PALIGNR XMM2,XMM3,0x4 *)
| 0x280996 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x20 256))))
)
(* 0x2809a4: PALIGNR XMM3,XMM4,0x4 *)
| 0x2809a4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x20 256))))
)
(* 0x2809b2: PALIGNR XMM4,XMM5,0x4 *)
| 0x2809b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x20 256))))
)
(* 0x2809c0: PALIGNR XMM5,XMM6,0x4 *)
| 0x2809c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x20 256))))
)
(* 0x2809ce: PALIGNR XMM6,XMM7,0x4 *)
| 0x2809ce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x20 256))))
)
(* 0x2809dd: PALIGNR XMM7,XMM8,0x4 *)
| 0x2809dd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x20 256))))
)
(* 0x2809f0: PALIGNR XMM8,XMM9,0x4 *)
| 0x2809f0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x20 256))))
)
(* 0x280a74: PALIGNR XMM9,XMM8,0x5 *)
| 0x280a74 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x28 256))))
)
(* 0x280a80: PALIGNR XMM8,XMM7,0x5 *)
| 0x280a80 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x28 256))))
)
(* 0x280a8c: PALIGNR XMM7,XMM6,0x5 *)
| 0x280a8c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x28 256))))
)
(* 0x280a96: PALIGNR XMM6,XMM5,0x5 *)
| 0x280a96 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x28 256))))
)
(* 0x280aa0: PALIGNR XMM5,XMM4,0x5 *)
| 0x280aa0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x28 256))))
)
(* 0x280aaa: PALIGNR XMM4,XMM3,0x5 *)
| 0x280aaa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x28 256))))
)
(* 0x280ab4: PALIGNR XMM3,XMM2,0x5 *)
| 0x280ab4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x28 256))))
)
(* 0x280abe: PALIGNR XMM2,XMM1,0x5 *)
| 0x280abe => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x28 256))))
)
(* 0x280b08: PALIGNR XMM1,XMM2,0x5 *)
| 0x280b08 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x28 256))))
)
(* 0x280b16: PALIGNR XMM2,XMM3,0x5 *)
| 0x280b16 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x28 256))))
)
(* 0x280b24: PALIGNR XMM3,XMM4,0x5 *)
| 0x280b24 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x28 256))))
)
(* 0x280b32: PALIGNR XMM4,XMM5,0x5 *)
| 0x280b32 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x28 256))))
)
(* 0x280b40: PALIGNR XMM5,XMM6,0x5 *)
| 0x280b40 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x28 256))))
)
(* 0x280b4e: PALIGNR XMM6,XMM7,0x5 *)
| 0x280b4e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x28 256))))
)
(* 0x280b5d: PALIGNR XMM7,XMM8,0x5 *)
| 0x280b5d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x28 256))))
)
(* 0x280b70: PALIGNR XMM8,XMM9,0x5 *)
| 0x280b70 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x28 256))))
)
(* 0x280bf4: PALIGNR XMM9,XMM8,0x6 *)
| 0x280bf4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x30 256))))
)
(* 0x280c00: PALIGNR XMM8,XMM7,0x6 *)
| 0x280c00 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x30 256))))
)
(* 0x280c0c: PALIGNR XMM7,XMM6,0x6 *)
| 0x280c0c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x30 256))))
)
(* 0x280c16: PALIGNR XMM6,XMM5,0x6 *)
| 0x280c16 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x30 256))))
)
(* 0x280c20: PALIGNR XMM5,XMM4,0x6 *)
| 0x280c20 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x30 256))))
)
(* 0x280c2a: PALIGNR XMM4,XMM3,0x6 *)
| 0x280c2a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x30 256))))
)
(* 0x280c34: PALIGNR XMM3,XMM2,0x6 *)
| 0x280c34 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x30 256))))
)
(* 0x280c3e: PALIGNR XMM2,XMM1,0x6 *)
| 0x280c3e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x30 256))))
)
(* 0x280c88: PALIGNR XMM1,XMM2,0x6 *)
| 0x280c88 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x30 256))))
)
(* 0x280c96: PALIGNR XMM2,XMM3,0x6 *)
| 0x280c96 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x30 256))))
)
(* 0x280ca4: PALIGNR XMM3,XMM4,0x6 *)
| 0x280ca4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x30 256))))
)
(* 0x280cb2: PALIGNR XMM4,XMM5,0x6 *)
| 0x280cb2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x30 256))))
)
(* 0x280cc0: PALIGNR XMM5,XMM6,0x6 *)
| 0x280cc0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x30 256))))
)
(* 0x280cce: PALIGNR XMM6,XMM7,0x6 *)
| 0x280cce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x30 256))))
)
(* 0x280cdd: PALIGNR XMM7,XMM8,0x6 *)
| 0x280cdd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x30 256))))
)
(* 0x280cf0: PALIGNR XMM8,XMM9,0x6 *)
| 0x280cf0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x30 256))))
)
(* 0x280d74: PALIGNR XMM9,XMM8,0x7 *)
| 0x280d74 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x38 256))))
)
(* 0x280d80: PALIGNR XMM8,XMM7,0x7 *)
| 0x280d80 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x38 256))))
)
(* 0x280d8c: PALIGNR XMM7,XMM6,0x7 *)
| 0x280d8c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x38 256))))
)
(* 0x280d96: PALIGNR XMM6,XMM5,0x7 *)
| 0x280d96 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x38 256))))
)
(* 0x280da0: PALIGNR XMM5,XMM4,0x7 *)
| 0x280da0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x38 256))))
)
(* 0x280daa: PALIGNR XMM4,XMM3,0x7 *)
| 0x280daa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x38 256))))
)
(* 0x280db4: PALIGNR XMM3,XMM2,0x7 *)
| 0x280db4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x38 256))))
)
(* 0x280dbe: PALIGNR XMM2,XMM1,0x7 *)
| 0x280dbe => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x38 256))))
)
(* 0x280e08: PALIGNR XMM1,XMM2,0x7 *)
| 0x280e08 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x38 256))))
)
(* 0x280e16: PALIGNR XMM2,XMM3,0x7 *)
| 0x280e16 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x38 256))))
)
(* 0x280e24: PALIGNR XMM3,XMM4,0x7 *)
| 0x280e24 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x38 256))))
)
(* 0x280e32: PALIGNR XMM4,XMM5,0x7 *)
| 0x280e32 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x38 256))))
)
(* 0x280e40: PALIGNR XMM5,XMM6,0x7 *)
| 0x280e40 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x38 256))))
)
(* 0x280e4e: PALIGNR XMM6,XMM7,0x7 *)
| 0x280e4e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x38 256))))
)
(* 0x280e5d: PALIGNR XMM7,XMM8,0x7 *)
| 0x280e5d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x38 256))))
)
(* 0x280e70: PALIGNR XMM8,XMM9,0x7 *)
| 0x280e70 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x38 256))))
)
(* 0x280ef4: PALIGNR XMM9,XMM8,0x8 *)
| 0x280ef4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x40 256))))
)
(* 0x280f00: PALIGNR XMM8,XMM7,0x8 *)
| 0x280f00 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x40 256))))
)
(* 0x280f0c: PALIGNR XMM7,XMM6,0x8 *)
| 0x280f0c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x40 256))))
)
(* 0x280f16: PALIGNR XMM6,XMM5,0x8 *)
| 0x280f16 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x40 256))))
)
(* 0x280f20: PALIGNR XMM5,XMM4,0x8 *)
| 0x280f20 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x40 256))))
)
(* 0x280f2a: PALIGNR XMM4,XMM3,0x8 *)
| 0x280f2a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x40 256))))
)
(* 0x280f34: PALIGNR XMM3,XMM2,0x8 *)
| 0x280f34 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x40 256))))
)
(* 0x280f3e: PALIGNR XMM2,XMM1,0x8 *)
| 0x280f3e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x40 256))))
)
(* 0x280f88: PALIGNR XMM1,XMM2,0x8 *)
| 0x280f88 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x40 256))))
)
(* 0x280f96: PALIGNR XMM2,XMM3,0x8 *)
| 0x280f96 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x40 256))))
)
(* 0x280fa4: PALIGNR XMM3,XMM4,0x8 *)
| 0x280fa4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x40 256))))
)
(* 0x280fb2: PALIGNR XMM4,XMM5,0x8 *)
| 0x280fb2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x40 256))))
)
(* 0x280fc0: PALIGNR XMM5,XMM6,0x8 *)
| 0x280fc0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x40 256))))
)
(* 0x280fce: PALIGNR XMM6,XMM7,0x8 *)
| 0x280fce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x40 256))))
)
(* 0x280fdd: PALIGNR XMM7,XMM8,0x8 *)
| 0x280fdd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x40 256))))
)
(* 0x280ff0: PALIGNR XMM8,XMM9,0x8 *)
| 0x280ff0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x40 256))))
)
(* 0x281074: PALIGNR XMM9,XMM8,0x9 *)
| 0x281074 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x48 256))))
)
(* 0x281080: PALIGNR XMM8,XMM7,0x9 *)
| 0x281080 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x48 256))))
)
(* 0x28108c: PALIGNR XMM7,XMM6,0x9 *)
| 0x28108c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x48 256))))
)
(* 0x281096: PALIGNR XMM6,XMM5,0x9 *)
| 0x281096 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x48 256))))
)
(* 0x2810a0: PALIGNR XMM5,XMM4,0x9 *)
| 0x2810a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x48 256))))
)
(* 0x2810aa: PALIGNR XMM4,XMM3,0x9 *)
| 0x2810aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x48 256))))
)
(* 0x2810b4: PALIGNR XMM3,XMM2,0x9 *)
| 0x2810b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x48 256))))
)
(* 0x2810be: PALIGNR XMM2,XMM1,0x9 *)
| 0x2810be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x48 256))))
)
(* 0x281108: PALIGNR XMM1,XMM2,0x9 *)
| 0x281108 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x48 256))))
)
(* 0x281116: PALIGNR XMM2,XMM3,0x9 *)
| 0x281116 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x48 256))))
)
(* 0x281124: PALIGNR XMM3,XMM4,0x9 *)
| 0x281124 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x48 256))))
)
(* 0x281132: PALIGNR XMM4,XMM5,0x9 *)
| 0x281132 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x48 256))))
)
(* 0x281140: PALIGNR XMM5,XMM6,0x9 *)
| 0x281140 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x48 256))))
)
(* 0x28114e: PALIGNR XMM6,XMM7,0x9 *)
| 0x28114e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x48 256))))
)
(* 0x28115d: PALIGNR XMM7,XMM8,0x9 *)
| 0x28115d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x48 256))))
)
(* 0x281170: PALIGNR XMM8,XMM9,0x9 *)
| 0x281170 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x48 256))))
)
(* 0x2811f4: PALIGNR XMM9,XMM8,0xa *)
| 0x2811f4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x50 256))))
)
(* 0x281200: PALIGNR XMM8,XMM7,0xa *)
| 0x281200 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x50 256))))
)
(* 0x28120c: PALIGNR XMM7,XMM6,0xa *)
| 0x28120c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x50 256))))
)
(* 0x281216: PALIGNR XMM6,XMM5,0xa *)
| 0x281216 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x50 256))))
)
(* 0x281220: PALIGNR XMM5,XMM4,0xa *)
| 0x281220 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x50 256))))
)
(* 0x28122a: PALIGNR XMM4,XMM3,0xa *)
| 0x28122a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x50 256))))
)
(* 0x281234: PALIGNR XMM3,XMM2,0xa *)
| 0x281234 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x50 256))))
)
(* 0x28123e: PALIGNR XMM2,XMM1,0xa *)
| 0x28123e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x50 256))))
)
(* 0x281288: PALIGNR XMM1,XMM2,0xa *)
| 0x281288 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x50 256))))
)
(* 0x281296: PALIGNR XMM2,XMM3,0xa *)
| 0x281296 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x50 256))))
)
(* 0x2812a4: PALIGNR XMM3,XMM4,0xa *)
| 0x2812a4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x50 256))))
)
(* 0x2812b2: PALIGNR XMM4,XMM5,0xa *)
| 0x2812b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x50 256))))
)
(* 0x2812c0: PALIGNR XMM5,XMM6,0xa *)
| 0x2812c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x50 256))))
)
(* 0x2812ce: PALIGNR XMM6,XMM7,0xa *)
| 0x2812ce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x50 256))))
)
(* 0x2812dd: PALIGNR XMM7,XMM8,0xa *)
| 0x2812dd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x50 256))))
)
(* 0x2812f0: PALIGNR XMM8,XMM9,0xa *)
| 0x2812f0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x50 256))))
)
(* 0x281374: PALIGNR XMM9,XMM8,0xb *)
| 0x281374 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x58 256))))
)
(* 0x281380: PALIGNR XMM8,XMM7,0xb *)
| 0x281380 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x58 256))))
)
(* 0x28138c: PALIGNR XMM7,XMM6,0xb *)
| 0x28138c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x58 256))))
)
(* 0x281396: PALIGNR XMM6,XMM5,0xb *)
| 0x281396 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x58 256))))
)
(* 0x2813a0: PALIGNR XMM5,XMM4,0xb *)
| 0x2813a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x58 256))))
)
(* 0x2813aa: PALIGNR XMM4,XMM3,0xb *)
| 0x2813aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x58 256))))
)
(* 0x2813b4: PALIGNR XMM3,XMM2,0xb *)
| 0x2813b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x58 256))))
)
(* 0x2813be: PALIGNR XMM2,XMM1,0xb *)
| 0x2813be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x58 256))))
)
(* 0x281408: PALIGNR XMM1,XMM2,0xb *)
| 0x281408 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x58 256))))
)
(* 0x281416: PALIGNR XMM2,XMM3,0xb *)
| 0x281416 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x58 256))))
)
(* 0x281424: PALIGNR XMM3,XMM4,0xb *)
| 0x281424 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x58 256))))
)
(* 0x281432: PALIGNR XMM4,XMM5,0xb *)
| 0x281432 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x58 256))))
)
(* 0x281440: PALIGNR XMM5,XMM6,0xb *)
| 0x281440 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x58 256))))
)
(* 0x28144e: PALIGNR XMM6,XMM7,0xb *)
| 0x28144e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x58 256))))
)
(* 0x28145d: PALIGNR XMM7,XMM8,0xb *)
| 0x28145d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x58 256))))
)
(* 0x281470: PALIGNR XMM8,XMM9,0xb *)
| 0x281470 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x58 256))))
)
(* 0x2814f5: PALIGNR XMM9,XMM8,0xc *)
| 0x2814f5 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x60 256))))
)
(* 0x281501: PALIGNR XMM8,XMM7,0xc *)
| 0x281501 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x60 256))))
)
(* 0x28150d: PALIGNR XMM7,XMM6,0xc *)
| 0x28150d => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x60 256))))
)
(* 0x281517: PALIGNR XMM6,XMM5,0xc *)
| 0x281517 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x60 256))))
)
(* 0x281521: PALIGNR XMM5,XMM4,0xc *)
| 0x281521 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x60 256))))
)
(* 0x28152b: PALIGNR XMM4,XMM3,0xc *)
| 0x28152b => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x60 256))))
)
(* 0x281535: PALIGNR XMM3,XMM2,0xc *)
| 0x281535 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x60 256))))
)
(* 0x28153f: PALIGNR XMM2,XMM1,0xc *)
| 0x28153f => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x60 256))))
)
(* 0x281588: PALIGNR XMM1,XMM2,0xc *)
| 0x281588 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x60 256))))
)
(* 0x281596: PALIGNR XMM2,XMM3,0xc *)
| 0x281596 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x60 256))))
)
(* 0x2815a4: PALIGNR XMM3,XMM4,0xc *)
| 0x2815a4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x60 256))))
)
(* 0x2815b2: PALIGNR XMM4,XMM5,0xc *)
| 0x2815b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x60 256))))
)
(* 0x2815c0: PALIGNR XMM5,XMM6,0xc *)
| 0x2815c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x60 256))))
)
(* 0x2815ce: PALIGNR XMM6,XMM7,0xc *)
| 0x2815ce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x60 256))))
)
(* 0x2815dd: PALIGNR XMM7,XMM8,0xc *)
| 0x2815dd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x60 256))))
)
(* 0x2815f0: PALIGNR XMM8,XMM9,0xc *)
| 0x2815f0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x60 256))))
)
(* 0x281674: PALIGNR XMM9,XMM8,0xd *)
| 0x281674 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x68 256))))
)
(* 0x281680: PALIGNR XMM8,XMM7,0xd *)
| 0x281680 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x68 256))))
)
(* 0x28168c: PALIGNR XMM7,XMM6,0xd *)
| 0x28168c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x68 256))))
)
(* 0x281696: PALIGNR XMM6,XMM5,0xd *)
| 0x281696 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x68 256))))
)
(* 0x2816a0: PALIGNR XMM5,XMM4,0xd *)
| 0x2816a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x68 256))))
)
(* 0x2816aa: PALIGNR XMM4,XMM3,0xd *)
| 0x2816aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x68 256))))
)
(* 0x2816b4: PALIGNR XMM3,XMM2,0xd *)
| 0x2816b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x68 256))))
)
(* 0x2816be: PALIGNR XMM2,XMM1,0xd *)
| 0x2816be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x68 256))))
)
(* 0x281708: PALIGNR XMM1,XMM2,0xd *)
| 0x281708 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x68 256))))
)
(* 0x281716: PALIGNR XMM2,XMM3,0xd *)
| 0x281716 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x68 256))))
)
(* 0x281724: PALIGNR XMM3,XMM4,0xd *)
| 0x281724 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x68 256))))
)
(* 0x281732: PALIGNR XMM4,XMM5,0xd *)
| 0x281732 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x68 256))))
)
(* 0x281740: PALIGNR XMM5,XMM6,0xd *)
| 0x281740 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x68 256))))
)
(* 0x28174e: PALIGNR XMM6,XMM7,0xd *)
| 0x28174e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x68 256))))
)
(* 0x28175d: PALIGNR XMM7,XMM8,0xd *)
| 0x28175d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x68 256))))
)
(* 0x281770: PALIGNR XMM8,XMM9,0xd *)
| 0x281770 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x68 256))))
)
(* 0x2817f4: PALIGNR XMM9,XMM8,0xe *)
| 0x2817f4 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x70 256))))
)
(* 0x281800: PALIGNR XMM8,XMM7,0xe *)
| 0x281800 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x70 256))))
)
(* 0x28180c: PALIGNR XMM7,XMM6,0xe *)
| 0x28180c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x70 256))))
)
(* 0x281816: PALIGNR XMM6,XMM5,0xe *)
| 0x281816 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x70 256))))
)
(* 0x281820: PALIGNR XMM5,XMM4,0xe *)
| 0x281820 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x70 256))))
)
(* 0x28182a: PALIGNR XMM4,XMM3,0xe *)
| 0x28182a => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x70 256))))
)
(* 0x281834: PALIGNR XMM3,XMM2,0xe *)
| 0x281834 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x70 256))))
)
(* 0x28183e: PALIGNR XMM2,XMM1,0xe *)
| 0x28183e => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x70 256))))
)
(* 0x281888: PALIGNR XMM1,XMM2,0xe *)
| 0x281888 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x70 256))))
)
(* 0x281896: PALIGNR XMM2,XMM3,0xe *)
| 0x281896 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x70 256))))
)
(* 0x2818a4: PALIGNR XMM3,XMM4,0xe *)
| 0x2818a4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x70 256))))
)
(* 0x2818b2: PALIGNR XMM4,XMM5,0xe *)
| 0x2818b2 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x70 256))))
)
(* 0x2818c0: PALIGNR XMM5,XMM6,0xe *)
| 0x2818c0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x70 256))))
)
(* 0x2818ce: PALIGNR XMM6,XMM7,0xe *)
| 0x2818ce => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x70 256))))
)
(* 0x2818dd: PALIGNR XMM7,XMM8,0xe *)
| 0x2818dd => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x70 256))))
)
(* 0x2818f0: PALIGNR XMM8,XMM9,0xe *)
| 0x2818f0 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x70 256))))
)
(* 0x281974: PALIGNR XMM9,XMM8,0xf *)
| 0x281974 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x78 256))))
)
(* 0x281980: PALIGNR XMM8,XMM7,0xf *)
| 0x281980 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM7))) (Word 0x78 256))))
)
(* 0x28198c: PALIGNR XMM7,XMM6,0xf *)
| 0x28198c => Some (6,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM6))) (Word 0x78 256))))
)
(* 0x281996: PALIGNR XMM6,XMM5,0xf *)
| 0x281996 => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM5))) (Word 0x78 256))))
)
(* 0x2819a0: PALIGNR XMM5,XMM4,0xf *)
| 0x2819a0 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM4))) (Word 0x78 256))))
)
(* 0x2819aa: PALIGNR XMM4,XMM3,0xf *)
| 0x2819aa => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM3))) (Word 0x78 256))))
)
(* 0x2819b4: PALIGNR XMM3,XMM2,0xf *)
| 0x2819b4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM2))) (Word 0x78 256))))
)
(* 0x2819be: PALIGNR XMM2,XMM1,0xf *)
| 0x2819be => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM1))) (Word 0x78 256))))
)
(* 0x281a08: PALIGNR XMM1,XMM2,0xf *)
| 0x281a08 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x78 256))))
)
(* 0x281a16: PALIGNR XMM2,XMM3,0xf *)
| 0x281a16 => Some (6,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM3))) (Word 0x78 256))))
)
(* 0x281a24: PALIGNR XMM3,XMM4,0xf *)
| 0x281a24 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM4))) (Word 0x78 256))))
)
(* 0x281a32: PALIGNR XMM4,XMM5,0xf *)
| 0x281a32 => Some (6,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Extract 127 0 (Var R_YMM5))) (Word 0x78 256))))
)
(* 0x281a40: PALIGNR XMM5,XMM6,0xf *)
| 0x281a40 => Some (6,
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM5)) (Extract 127 0 (Var R_YMM6))) (Word 0x78 256))))
)
(* 0x281a4e: PALIGNR XMM6,XMM7,0xf *)
| 0x281a4e => Some (6,
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM6)) (Extract 127 0 (Var R_YMM7))) (Word 0x78 256))))
)
(* 0x281a5d: PALIGNR XMM7,XMM8,0xf *)
| 0x281a5d => Some (7,
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM8))) (Word 0x78 256))))
)
(* 0x281a70: PALIGNR XMM8,XMM9,0xf *)
| 0x281a70 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x78 256))))
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e34_pinned_shuffles_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
