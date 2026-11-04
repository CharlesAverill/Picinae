(* Strict AMD64 shuffle128 sequential projection, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: synthetic; ELF SHA256: dd3fd060a11db86ddf7bbdf0c530413299bdd6fbf45c2d48bb3932324d4f616a
Symbol: align; global entry: 0x101000; selected: align
Profile: shuffle128 (CET-enabled execution is outside this model).
Scope: selected-function-extents; <=256 projection of ZMM0..15 only.
SSSE3 and OS vector state enabled; nonfaulting full-width accesses, architectural alignment required. New shuffle forms: legacy PALIGNR only; VEX shuffles/PSHUFB/MMX/EVEX rejected.
Upper>256, faults, ordering/cache/timing and CET-enabled execution excluded.
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e34_align_amd64 : program := fun _ a => match a with
(* 0x101000: PALIGNR XMM1,XMM2,0x0 *)
| 0x101000 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x0 256))))
)
(* 0x101006: PALIGNR XMM1,XMM2,0x1 *)
| 0x101006 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x8 256))))
)
(* 0x10100c: PALIGNR XMM1,XMM2,0x2 *)
| 0x10100c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x10 256))))
)
(* 0x101012: PALIGNR XMM1,XMM2,0x3 *)
| 0x101012 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x18 256))))
)
(* 0x101018: PALIGNR XMM1,XMM2,0x4 *)
| 0x101018 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x20 256))))
)
(* 0x10101e: PALIGNR XMM1,XMM2,0x5 *)
| 0x10101e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x28 256))))
)
(* 0x101024: PALIGNR XMM1,XMM2,0x6 *)
| 0x101024 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x30 256))))
)
(* 0x10102a: PALIGNR XMM1,XMM2,0x7 *)
| 0x10102a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x38 256))))
)
(* 0x101030: PALIGNR XMM1,XMM2,0x8 *)
| 0x101030 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x40 256))))
)
(* 0x101036: PALIGNR XMM1,XMM2,0x9 *)
| 0x101036 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x48 256))))
)
(* 0x10103c: PALIGNR XMM1,XMM2,0xa *)
| 0x10103c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x50 256))))
)
(* 0x101042: PALIGNR XMM1,XMM2,0xb *)
| 0x101042 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x58 256))))
)
(* 0x101048: PALIGNR XMM1,XMM2,0xc *)
| 0x101048 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x60 256))))
)
(* 0x10104e: PALIGNR XMM1,XMM2,0xd *)
| 0x10104e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x68 256))))
)
(* 0x101054: PALIGNR XMM1,XMM2,0xe *)
| 0x101054 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x70 256))))
)
(* 0x10105a: PALIGNR XMM1,XMM2,0xf *)
| 0x10105a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x78 256))))
)
(* 0x101060: PALIGNR XMM1,XMM2,0x10 *)
| 0x101060 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x80 256))))
)
(* 0x101066: PALIGNR XMM1,XMM2,0x11 *)
| 0x101066 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x88 256))))
)
(* 0x10106c: PALIGNR XMM1,XMM2,0x12 *)
| 0x10106c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x90 256))))
)
(* 0x101072: PALIGNR XMM1,XMM2,0x13 *)
| 0x101072 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x98 256))))
)
(* 0x101078: PALIGNR XMM1,XMM2,0x14 *)
| 0x101078 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xa0 256))))
)
(* 0x10107e: PALIGNR XMM1,XMM2,0x15 *)
| 0x10107e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xa8 256))))
)
(* 0x101084: PALIGNR XMM1,XMM2,0x16 *)
| 0x101084 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xb0 256))))
)
(* 0x10108a: PALIGNR XMM1,XMM2,0x17 *)
| 0x10108a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xb8 256))))
)
(* 0x101090: PALIGNR XMM1,XMM2,0x18 *)
| 0x101090 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xc0 256))))
)
(* 0x101096: PALIGNR XMM1,XMM2,0x19 *)
| 0x101096 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xc8 256))))
)
(* 0x10109c: PALIGNR XMM1,XMM2,0x1a *)
| 0x10109c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xd0 256))))
)
(* 0x1010a2: PALIGNR XMM1,XMM2,0x1b *)
| 0x1010a2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xd8 256))))
)
(* 0x1010a8: PALIGNR XMM1,XMM2,0x1c *)
| 0x1010a8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xe0 256))))
)
(* 0x1010ae: PALIGNR XMM1,XMM2,0x1d *)
| 0x1010ae => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xe8 256))))
)
(* 0x1010b4: PALIGNR XMM1,XMM2,0x1e *)
| 0x1010b4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xf0 256))))
)
(* 0x1010ba: PALIGNR XMM1,XMM2,0x1f *)
| 0x1010ba => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0xf8 256))))
)
(* 0x1010c0: PALIGNR XMM1,XMM2,0x20 *)
| 0x1010c0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x100 256))))
)
(* 0x1010c6: PALIGNR XMM1,XMM2,0x21 *)
| 0x1010c6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x108 256))))
)
(* 0x1010cc: PALIGNR XMM1,XMM2,0x22 *)
| 0x1010cc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x110 256))))
)
(* 0x1010d2: PALIGNR XMM1,XMM2,0x23 *)
| 0x1010d2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x118 256))))
)
(* 0x1010d8: PALIGNR XMM1,XMM2,0x24 *)
| 0x1010d8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x120 256))))
)
(* 0x1010de: PALIGNR XMM1,XMM2,0x25 *)
| 0x1010de => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x128 256))))
)
(* 0x1010e4: PALIGNR XMM1,XMM2,0x26 *)
| 0x1010e4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x130 256))))
)
(* 0x1010ea: PALIGNR XMM1,XMM2,0x27 *)
| 0x1010ea => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x138 256))))
)
(* 0x1010f0: PALIGNR XMM1,XMM2,0x28 *)
| 0x1010f0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x140 256))))
)
(* 0x1010f6: PALIGNR XMM1,XMM2,0x29 *)
| 0x1010f6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x148 256))))
)
(* 0x1010fc: PALIGNR XMM1,XMM2,0x2a *)
| 0x1010fc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x150 256))))
)
(* 0x101102: PALIGNR XMM1,XMM2,0x2b *)
| 0x101102 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x158 256))))
)
(* 0x101108: PALIGNR XMM1,XMM2,0x2c *)
| 0x101108 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x160 256))))
)
(* 0x10110e: PALIGNR XMM1,XMM2,0x2d *)
| 0x10110e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x168 256))))
)
(* 0x101114: PALIGNR XMM1,XMM2,0x2e *)
| 0x101114 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x170 256))))
)
(* 0x10111a: PALIGNR XMM1,XMM2,0x2f *)
| 0x10111a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x178 256))))
)
(* 0x101120: PALIGNR XMM1,XMM2,0x30 *)
| 0x101120 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x180 256))))
)
(* 0x101126: PALIGNR XMM1,XMM2,0x31 *)
| 0x101126 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x188 256))))
)
(* 0x10112c: PALIGNR XMM1,XMM2,0x32 *)
| 0x10112c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x190 256))))
)
(* 0x101132: PALIGNR XMM1,XMM2,0x33 *)
| 0x101132 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x198 256))))
)
(* 0x101138: PALIGNR XMM1,XMM2,0x34 *)
| 0x101138 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1a0 256))))
)
(* 0x10113e: PALIGNR XMM1,XMM2,0x35 *)
| 0x10113e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1a8 256))))
)
(* 0x101144: PALIGNR XMM1,XMM2,0x36 *)
| 0x101144 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1b0 256))))
)
(* 0x10114a: PALIGNR XMM1,XMM2,0x37 *)
| 0x10114a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1b8 256))))
)
(* 0x101150: PALIGNR XMM1,XMM2,0x38 *)
| 0x101150 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1c0 256))))
)
(* 0x101156: PALIGNR XMM1,XMM2,0x39 *)
| 0x101156 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1c8 256))))
)
(* 0x10115c: PALIGNR XMM1,XMM2,0x3a *)
| 0x10115c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1d0 256))))
)
(* 0x101162: PALIGNR XMM1,XMM2,0x3b *)
| 0x101162 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1d8 256))))
)
(* 0x101168: PALIGNR XMM1,XMM2,0x3c *)
| 0x101168 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1e0 256))))
)
(* 0x10116e: PALIGNR XMM1,XMM2,0x3d *)
| 0x10116e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1e8 256))))
)
(* 0x101174: PALIGNR XMM1,XMM2,0x3e *)
| 0x101174 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1f0 256))))
)
(* 0x10117a: PALIGNR XMM1,XMM2,0x3f *)
| 0x10117a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x1f8 256))))
)
(* 0x101180: PALIGNR XMM1,XMM2,0x40 *)
| 0x101180 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x200 256))))
)
(* 0x101186: PALIGNR XMM1,XMM2,0x41 *)
| 0x101186 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x208 256))))
)
(* 0x10118c: PALIGNR XMM1,XMM2,0x42 *)
| 0x10118c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x210 256))))
)
(* 0x101192: PALIGNR XMM1,XMM2,0x43 *)
| 0x101192 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x218 256))))
)
(* 0x101198: PALIGNR XMM1,XMM2,0x44 *)
| 0x101198 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x220 256))))
)
(* 0x10119e: PALIGNR XMM1,XMM2,0x45 *)
| 0x10119e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x228 256))))
)
(* 0x1011a4: PALIGNR XMM1,XMM2,0x46 *)
| 0x1011a4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x230 256))))
)
(* 0x1011aa: PALIGNR XMM1,XMM2,0x47 *)
| 0x1011aa => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x238 256))))
)
(* 0x1011b0: PALIGNR XMM1,XMM2,0x48 *)
| 0x1011b0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x240 256))))
)
(* 0x1011b6: PALIGNR XMM1,XMM2,0x49 *)
| 0x1011b6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x248 256))))
)
(* 0x1011bc: PALIGNR XMM1,XMM2,0x4a *)
| 0x1011bc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x250 256))))
)
(* 0x1011c2: PALIGNR XMM1,XMM2,0x4b *)
| 0x1011c2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x258 256))))
)
(* 0x1011c8: PALIGNR XMM1,XMM2,0x4c *)
| 0x1011c8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x260 256))))
)
(* 0x1011ce: PALIGNR XMM1,XMM2,0x4d *)
| 0x1011ce => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x268 256))))
)
(* 0x1011d4: PALIGNR XMM1,XMM2,0x4e *)
| 0x1011d4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x270 256))))
)
(* 0x1011da: PALIGNR XMM1,XMM2,0x4f *)
| 0x1011da => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x278 256))))
)
(* 0x1011e0: PALIGNR XMM1,XMM2,0x50 *)
| 0x1011e0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x280 256))))
)
(* 0x1011e6: PALIGNR XMM1,XMM2,0x51 *)
| 0x1011e6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x288 256))))
)
(* 0x1011ec: PALIGNR XMM1,XMM2,0x52 *)
| 0x1011ec => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x290 256))))
)
(* 0x1011f2: PALIGNR XMM1,XMM2,0x53 *)
| 0x1011f2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x298 256))))
)
(* 0x1011f8: PALIGNR XMM1,XMM2,0x54 *)
| 0x1011f8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2a0 256))))
)
(* 0x1011fe: PALIGNR XMM1,XMM2,0x55 *)
| 0x1011fe => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2a8 256))))
)
(* 0x101204: PALIGNR XMM1,XMM2,0x56 *)
| 0x101204 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2b0 256))))
)
(* 0x10120a: PALIGNR XMM1,XMM2,0x57 *)
| 0x10120a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2b8 256))))
)
(* 0x101210: PALIGNR XMM1,XMM2,0x58 *)
| 0x101210 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2c0 256))))
)
(* 0x101216: PALIGNR XMM1,XMM2,0x59 *)
| 0x101216 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2c8 256))))
)
(* 0x10121c: PALIGNR XMM1,XMM2,0x5a *)
| 0x10121c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2d0 256))))
)
(* 0x101222: PALIGNR XMM1,XMM2,0x5b *)
| 0x101222 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2d8 256))))
)
(* 0x101228: PALIGNR XMM1,XMM2,0x5c *)
| 0x101228 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2e0 256))))
)
(* 0x10122e: PALIGNR XMM1,XMM2,0x5d *)
| 0x10122e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2e8 256))))
)
(* 0x101234: PALIGNR XMM1,XMM2,0x5e *)
| 0x101234 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2f0 256))))
)
(* 0x10123a: PALIGNR XMM1,XMM2,0x5f *)
| 0x10123a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x2f8 256))))
)
(* 0x101240: PALIGNR XMM1,XMM2,0x60 *)
| 0x101240 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x300 256))))
)
(* 0x101246: PALIGNR XMM1,XMM2,0x61 *)
| 0x101246 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x308 256))))
)
(* 0x10124c: PALIGNR XMM1,XMM2,0x62 *)
| 0x10124c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x310 256))))
)
(* 0x101252: PALIGNR XMM1,XMM2,0x63 *)
| 0x101252 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x318 256))))
)
(* 0x101258: PALIGNR XMM1,XMM2,0x64 *)
| 0x101258 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x320 256))))
)
(* 0x10125e: PALIGNR XMM1,XMM2,0x65 *)
| 0x10125e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x328 256))))
)
(* 0x101264: PALIGNR XMM1,XMM2,0x66 *)
| 0x101264 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x330 256))))
)
(* 0x10126a: PALIGNR XMM1,XMM2,0x67 *)
| 0x10126a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x338 256))))
)
(* 0x101270: PALIGNR XMM1,XMM2,0x68 *)
| 0x101270 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x340 256))))
)
(* 0x101276: PALIGNR XMM1,XMM2,0x69 *)
| 0x101276 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x348 256))))
)
(* 0x10127c: PALIGNR XMM1,XMM2,0x6a *)
| 0x10127c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x350 256))))
)
(* 0x101282: PALIGNR XMM1,XMM2,0x6b *)
| 0x101282 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x358 256))))
)
(* 0x101288: PALIGNR XMM1,XMM2,0x6c *)
| 0x101288 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x360 256))))
)
(* 0x10128e: PALIGNR XMM1,XMM2,0x6d *)
| 0x10128e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x368 256))))
)
(* 0x101294: PALIGNR XMM1,XMM2,0x6e *)
| 0x101294 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x370 256))))
)
(* 0x10129a: PALIGNR XMM1,XMM2,0x6f *)
| 0x10129a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x378 256))))
)
(* 0x1012a0: PALIGNR XMM1,XMM2,0x70 *)
| 0x1012a0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x380 256))))
)
(* 0x1012a6: PALIGNR XMM1,XMM2,0x71 *)
| 0x1012a6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x388 256))))
)
(* 0x1012ac: PALIGNR XMM1,XMM2,0x72 *)
| 0x1012ac => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x390 256))))
)
(* 0x1012b2: PALIGNR XMM1,XMM2,0x73 *)
| 0x1012b2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x398 256))))
)
(* 0x1012b8: PALIGNR XMM1,XMM2,0x74 *)
| 0x1012b8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3a0 256))))
)
(* 0x1012be: PALIGNR XMM1,XMM2,0x75 *)
| 0x1012be => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3a8 256))))
)
(* 0x1012c4: PALIGNR XMM1,XMM2,0x76 *)
| 0x1012c4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3b0 256))))
)
(* 0x1012ca: PALIGNR XMM1,XMM2,0x77 *)
| 0x1012ca => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3b8 256))))
)
(* 0x1012d0: PALIGNR XMM1,XMM2,0x78 *)
| 0x1012d0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3c0 256))))
)
(* 0x1012d6: PALIGNR XMM1,XMM2,0x79 *)
| 0x1012d6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3c8 256))))
)
(* 0x1012dc: PALIGNR XMM1,XMM2,0x7a *)
| 0x1012dc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3d0 256))))
)
(* 0x1012e2: PALIGNR XMM1,XMM2,0x7b *)
| 0x1012e2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3d8 256))))
)
(* 0x1012e8: PALIGNR XMM1,XMM2,0x7c *)
| 0x1012e8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3e0 256))))
)
(* 0x1012ee: PALIGNR XMM1,XMM2,0x7d *)
| 0x1012ee => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3e8 256))))
)
(* 0x1012f4: PALIGNR XMM1,XMM2,0x7e *)
| 0x1012f4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3f0 256))))
)
(* 0x1012fa: PALIGNR XMM1,XMM2,0x7f *)
| 0x1012fa => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x3f8 256))))
)
(* 0x101300: PALIGNR XMM1,XMM2,0x80 *)
| 0x101300 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x400 256))))
)
(* 0x101306: PALIGNR XMM1,XMM2,0x81 *)
| 0x101306 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x408 256))))
)
(* 0x10130c: PALIGNR XMM1,XMM2,0x82 *)
| 0x10130c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x410 256))))
)
(* 0x101312: PALIGNR XMM1,XMM2,0x83 *)
| 0x101312 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x418 256))))
)
(* 0x101318: PALIGNR XMM1,XMM2,0x84 *)
| 0x101318 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x420 256))))
)
(* 0x10131e: PALIGNR XMM1,XMM2,0x85 *)
| 0x10131e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x428 256))))
)
(* 0x101324: PALIGNR XMM1,XMM2,0x86 *)
| 0x101324 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x430 256))))
)
(* 0x10132a: PALIGNR XMM1,XMM2,0x87 *)
| 0x10132a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x438 256))))
)
(* 0x101330: PALIGNR XMM1,XMM2,0x88 *)
| 0x101330 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x440 256))))
)
(* 0x101336: PALIGNR XMM1,XMM2,0x89 *)
| 0x101336 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x448 256))))
)
(* 0x10133c: PALIGNR XMM1,XMM2,0x8a *)
| 0x10133c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x450 256))))
)
(* 0x101342: PALIGNR XMM1,XMM2,0x8b *)
| 0x101342 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x458 256))))
)
(* 0x101348: PALIGNR XMM1,XMM2,0x8c *)
| 0x101348 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x460 256))))
)
(* 0x10134e: PALIGNR XMM1,XMM2,0x8d *)
| 0x10134e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x468 256))))
)
(* 0x101354: PALIGNR XMM1,XMM2,0x8e *)
| 0x101354 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x470 256))))
)
(* 0x10135a: PALIGNR XMM1,XMM2,0x8f *)
| 0x10135a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x478 256))))
)
(* 0x101360: PALIGNR XMM1,XMM2,0x90 *)
| 0x101360 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x480 256))))
)
(* 0x101366: PALIGNR XMM1,XMM2,0x91 *)
| 0x101366 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x488 256))))
)
(* 0x10136c: PALIGNR XMM1,XMM2,0x92 *)
| 0x10136c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x490 256))))
)
(* 0x101372: PALIGNR XMM1,XMM2,0x93 *)
| 0x101372 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x498 256))))
)
(* 0x101378: PALIGNR XMM1,XMM2,0x94 *)
| 0x101378 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4a0 256))))
)
(* 0x10137e: PALIGNR XMM1,XMM2,0x95 *)
| 0x10137e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4a8 256))))
)
(* 0x101384: PALIGNR XMM1,XMM2,0x96 *)
| 0x101384 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4b0 256))))
)
(* 0x10138a: PALIGNR XMM1,XMM2,0x97 *)
| 0x10138a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4b8 256))))
)
(* 0x101390: PALIGNR XMM1,XMM2,0x98 *)
| 0x101390 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4c0 256))))
)
(* 0x101396: PALIGNR XMM1,XMM2,0x99 *)
| 0x101396 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4c8 256))))
)
(* 0x10139c: PALIGNR XMM1,XMM2,0x9a *)
| 0x10139c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4d0 256))))
)
(* 0x1013a2: PALIGNR XMM1,XMM2,0x9b *)
| 0x1013a2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4d8 256))))
)
(* 0x1013a8: PALIGNR XMM1,XMM2,0x9c *)
| 0x1013a8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4e0 256))))
)
(* 0x1013ae: PALIGNR XMM1,XMM2,0x9d *)
| 0x1013ae => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4e8 256))))
)
(* 0x1013b4: PALIGNR XMM1,XMM2,0x9e *)
| 0x1013b4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4f0 256))))
)
(* 0x1013ba: PALIGNR XMM1,XMM2,0x9f *)
| 0x1013ba => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x4f8 256))))
)
(* 0x1013c0: PALIGNR XMM1,XMM2,0xa0 *)
| 0x1013c0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x500 256))))
)
(* 0x1013c6: PALIGNR XMM1,XMM2,0xa1 *)
| 0x1013c6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x508 256))))
)
(* 0x1013cc: PALIGNR XMM1,XMM2,0xa2 *)
| 0x1013cc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x510 256))))
)
(* 0x1013d2: PALIGNR XMM1,XMM2,0xa3 *)
| 0x1013d2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x518 256))))
)
(* 0x1013d8: PALIGNR XMM1,XMM2,0xa4 *)
| 0x1013d8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x520 256))))
)
(* 0x1013de: PALIGNR XMM1,XMM2,0xa5 *)
| 0x1013de => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x528 256))))
)
(* 0x1013e4: PALIGNR XMM1,XMM2,0xa6 *)
| 0x1013e4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x530 256))))
)
(* 0x1013ea: PALIGNR XMM1,XMM2,0xa7 *)
| 0x1013ea => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x538 256))))
)
(* 0x1013f0: PALIGNR XMM1,XMM2,0xa8 *)
| 0x1013f0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x540 256))))
)
(* 0x1013f6: PALIGNR XMM1,XMM2,0xa9 *)
| 0x1013f6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x548 256))))
)
(* 0x1013fc: PALIGNR XMM1,XMM2,0xaa *)
| 0x1013fc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x550 256))))
)
(* 0x101402: PALIGNR XMM1,XMM2,0xab *)
| 0x101402 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x558 256))))
)
(* 0x101408: PALIGNR XMM1,XMM2,0xac *)
| 0x101408 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x560 256))))
)
(* 0x10140e: PALIGNR XMM1,XMM2,0xad *)
| 0x10140e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x568 256))))
)
(* 0x101414: PALIGNR XMM1,XMM2,0xae *)
| 0x101414 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x570 256))))
)
(* 0x10141a: PALIGNR XMM1,XMM2,0xaf *)
| 0x10141a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x578 256))))
)
(* 0x101420: PALIGNR XMM1,XMM2,0xb0 *)
| 0x101420 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x580 256))))
)
(* 0x101426: PALIGNR XMM1,XMM2,0xb1 *)
| 0x101426 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x588 256))))
)
(* 0x10142c: PALIGNR XMM1,XMM2,0xb2 *)
| 0x10142c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x590 256))))
)
(* 0x101432: PALIGNR XMM1,XMM2,0xb3 *)
| 0x101432 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x598 256))))
)
(* 0x101438: PALIGNR XMM1,XMM2,0xb4 *)
| 0x101438 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5a0 256))))
)
(* 0x10143e: PALIGNR XMM1,XMM2,0xb5 *)
| 0x10143e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5a8 256))))
)
(* 0x101444: PALIGNR XMM1,XMM2,0xb6 *)
| 0x101444 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5b0 256))))
)
(* 0x10144a: PALIGNR XMM1,XMM2,0xb7 *)
| 0x10144a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5b8 256))))
)
(* 0x101450: PALIGNR XMM1,XMM2,0xb8 *)
| 0x101450 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5c0 256))))
)
(* 0x101456: PALIGNR XMM1,XMM2,0xb9 *)
| 0x101456 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5c8 256))))
)
(* 0x10145c: PALIGNR XMM1,XMM2,0xba *)
| 0x10145c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5d0 256))))
)
(* 0x101462: PALIGNR XMM1,XMM2,0xbb *)
| 0x101462 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5d8 256))))
)
(* 0x101468: PALIGNR XMM1,XMM2,0xbc *)
| 0x101468 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5e0 256))))
)
(* 0x10146e: PALIGNR XMM1,XMM2,0xbd *)
| 0x10146e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5e8 256))))
)
(* 0x101474: PALIGNR XMM1,XMM2,0xbe *)
| 0x101474 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5f0 256))))
)
(* 0x10147a: PALIGNR XMM1,XMM2,0xbf *)
| 0x10147a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x5f8 256))))
)
(* 0x101480: PALIGNR XMM1,XMM2,0xc0 *)
| 0x101480 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x600 256))))
)
(* 0x101486: PALIGNR XMM1,XMM2,0xc1 *)
| 0x101486 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x608 256))))
)
(* 0x10148c: PALIGNR XMM1,XMM2,0xc2 *)
| 0x10148c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x610 256))))
)
(* 0x101492: PALIGNR XMM1,XMM2,0xc3 *)
| 0x101492 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x618 256))))
)
(* 0x101498: PALIGNR XMM1,XMM2,0xc4 *)
| 0x101498 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x620 256))))
)
(* 0x10149e: PALIGNR XMM1,XMM2,0xc5 *)
| 0x10149e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x628 256))))
)
(* 0x1014a4: PALIGNR XMM1,XMM2,0xc6 *)
| 0x1014a4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x630 256))))
)
(* 0x1014aa: PALIGNR XMM1,XMM2,0xc7 *)
| 0x1014aa => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x638 256))))
)
(* 0x1014b0: PALIGNR XMM1,XMM2,0xc8 *)
| 0x1014b0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x640 256))))
)
(* 0x1014b6: PALIGNR XMM1,XMM2,0xc9 *)
| 0x1014b6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x648 256))))
)
(* 0x1014bc: PALIGNR XMM1,XMM2,0xca *)
| 0x1014bc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x650 256))))
)
(* 0x1014c2: PALIGNR XMM1,XMM2,0xcb *)
| 0x1014c2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x658 256))))
)
(* 0x1014c8: PALIGNR XMM1,XMM2,0xcc *)
| 0x1014c8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x660 256))))
)
(* 0x1014ce: PALIGNR XMM1,XMM2,0xcd *)
| 0x1014ce => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x668 256))))
)
(* 0x1014d4: PALIGNR XMM1,XMM2,0xce *)
| 0x1014d4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x670 256))))
)
(* 0x1014da: PALIGNR XMM1,XMM2,0xcf *)
| 0x1014da => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x678 256))))
)
(* 0x1014e0: PALIGNR XMM1,XMM2,0xd0 *)
| 0x1014e0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x680 256))))
)
(* 0x1014e6: PALIGNR XMM1,XMM2,0xd1 *)
| 0x1014e6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x688 256))))
)
(* 0x1014ec: PALIGNR XMM1,XMM2,0xd2 *)
| 0x1014ec => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x690 256))))
)
(* 0x1014f2: PALIGNR XMM1,XMM2,0xd3 *)
| 0x1014f2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x698 256))))
)
(* 0x1014f8: PALIGNR XMM1,XMM2,0xd4 *)
| 0x1014f8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6a0 256))))
)
(* 0x1014fe: PALIGNR XMM1,XMM2,0xd5 *)
| 0x1014fe => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6a8 256))))
)
(* 0x101504: PALIGNR XMM1,XMM2,0xd6 *)
| 0x101504 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6b0 256))))
)
(* 0x10150a: PALIGNR XMM1,XMM2,0xd7 *)
| 0x10150a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6b8 256))))
)
(* 0x101510: PALIGNR XMM1,XMM2,0xd8 *)
| 0x101510 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6c0 256))))
)
(* 0x101516: PALIGNR XMM1,XMM2,0xd9 *)
| 0x101516 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6c8 256))))
)
(* 0x10151c: PALIGNR XMM1,XMM2,0xda *)
| 0x10151c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6d0 256))))
)
(* 0x101522: PALIGNR XMM1,XMM2,0xdb *)
| 0x101522 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6d8 256))))
)
(* 0x101528: PALIGNR XMM1,XMM2,0xdc *)
| 0x101528 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6e0 256))))
)
(* 0x10152e: PALIGNR XMM1,XMM2,0xdd *)
| 0x10152e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6e8 256))))
)
(* 0x101534: PALIGNR XMM1,XMM2,0xde *)
| 0x101534 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6f0 256))))
)
(* 0x10153a: PALIGNR XMM1,XMM2,0xdf *)
| 0x10153a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x6f8 256))))
)
(* 0x101540: PALIGNR XMM1,XMM2,0xe0 *)
| 0x101540 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x700 256))))
)
(* 0x101546: PALIGNR XMM1,XMM2,0xe1 *)
| 0x101546 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x708 256))))
)
(* 0x10154c: PALIGNR XMM1,XMM2,0xe2 *)
| 0x10154c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x710 256))))
)
(* 0x101552: PALIGNR XMM1,XMM2,0xe3 *)
| 0x101552 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x718 256))))
)
(* 0x101558: PALIGNR XMM1,XMM2,0xe4 *)
| 0x101558 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x720 256))))
)
(* 0x10155e: PALIGNR XMM1,XMM2,0xe5 *)
| 0x10155e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x728 256))))
)
(* 0x101564: PALIGNR XMM1,XMM2,0xe6 *)
| 0x101564 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x730 256))))
)
(* 0x10156a: PALIGNR XMM1,XMM2,0xe7 *)
| 0x10156a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x738 256))))
)
(* 0x101570: PALIGNR XMM1,XMM2,0xe8 *)
| 0x101570 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x740 256))))
)
(* 0x101576: PALIGNR XMM1,XMM2,0xe9 *)
| 0x101576 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x748 256))))
)
(* 0x10157c: PALIGNR XMM1,XMM2,0xea *)
| 0x10157c => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x750 256))))
)
(* 0x101582: PALIGNR XMM1,XMM2,0xeb *)
| 0x101582 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x758 256))))
)
(* 0x101588: PALIGNR XMM1,XMM2,0xec *)
| 0x101588 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x760 256))))
)
(* 0x10158e: PALIGNR XMM1,XMM2,0xed *)
| 0x10158e => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x768 256))))
)
(* 0x101594: PALIGNR XMM1,XMM2,0xee *)
| 0x101594 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x770 256))))
)
(* 0x10159a: PALIGNR XMM1,XMM2,0xef *)
| 0x10159a => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x778 256))))
)
(* 0x1015a0: PALIGNR XMM1,XMM2,0xf0 *)
| 0x1015a0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x780 256))))
)
(* 0x1015a6: PALIGNR XMM1,XMM2,0xf1 *)
| 0x1015a6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x788 256))))
)
(* 0x1015ac: PALIGNR XMM1,XMM2,0xf2 *)
| 0x1015ac => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x790 256))))
)
(* 0x1015b2: PALIGNR XMM1,XMM2,0xf3 *)
| 0x1015b2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x798 256))))
)
(* 0x1015b8: PALIGNR XMM1,XMM2,0xf4 *)
| 0x1015b8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7a0 256))))
)
(* 0x1015be: PALIGNR XMM1,XMM2,0xf5 *)
| 0x1015be => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7a8 256))))
)
(* 0x1015c4: PALIGNR XMM1,XMM2,0xf6 *)
| 0x1015c4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7b0 256))))
)
(* 0x1015ca: PALIGNR XMM1,XMM2,0xf7 *)
| 0x1015ca => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7b8 256))))
)
(* 0x1015d0: PALIGNR XMM1,XMM2,0xf8 *)
| 0x1015d0 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7c0 256))))
)
(* 0x1015d6: PALIGNR XMM1,XMM2,0xf9 *)
| 0x1015d6 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7c8 256))))
)
(* 0x1015dc: PALIGNR XMM1,XMM2,0xfa *)
| 0x1015dc => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7d0 256))))
)
(* 0x1015e2: PALIGNR XMM1,XMM2,0xfb *)
| 0x1015e2 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7d8 256))))
)
(* 0x1015e8: PALIGNR XMM1,XMM2,0xfc *)
| 0x1015e8 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7e0 256))))
)
(* 0x1015ee: PALIGNR XMM1,XMM2,0xfd *)
| 0x1015ee => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7e8 256))))
)
(* 0x1015f4: PALIGNR XMM1,XMM2,0xfe *)
| 0x1015f4 => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7f0 256))))
)
(* 0x1015fa: PALIGNR XMM1,XMM2,0xff *)
| 0x1015fa => Some (6,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM2))) (Word 0x7f8 256))))
)
(* 0x101600: PALIGNR XMM3,XMM3,0x0 *)
| 0x101600 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x0 256))))
)
(* 0x101606: PALIGNR XMM8,XMM9,0x0 *)
| 0x101606 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x0 256))))
)
(* 0x10160d: PALIGNR XMM9,XMM8,0x0 *)
| 0x10160d => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x0 256))))
)
(* 0x101614: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x0 *)
| 0x101614 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x0 256))))
)
(* 0x10161d: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x0 *)
| 0x10161d => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x0 256))))
)
(* 0x101628: PALIGNR XMM4,xmmword ptr [0x00102000],0x0 *)
| 0x101628 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x0 256))))
)
(* 0x101632: PALIGNR XMM3,XMM3,0x1 *)
| 0x101632 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x8 256))))
)
(* 0x101638: PALIGNR XMM8,XMM9,0x1 *)
| 0x101638 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x8 256))))
)
(* 0x10163f: PALIGNR XMM9,XMM8,0x1 *)
| 0x10163f => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x8 256))))
)
(* 0x101646: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x1 *)
| 0x101646 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x8 256))))
)
(* 0x10164f: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x1 *)
| 0x10164f => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x8 256))))
)
(* 0x10165a: PALIGNR XMM4,xmmword ptr [0x00102000],0x1 *)
| 0x10165a => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x8 256))))
)
(* 0x101664: PALIGNR XMM3,XMM3,0xf *)
| 0x101664 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x78 256))))
)
(* 0x10166a: PALIGNR XMM8,XMM9,0xf *)
| 0x10166a => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x78 256))))
)
(* 0x101671: PALIGNR XMM9,XMM8,0xf *)
| 0x101671 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x78 256))))
)
(* 0x101678: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0xf *)
| 0x101678 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x78 256))))
)
(* 0x101681: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0xf *)
| 0x101681 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x78 256))))
)
(* 0x10168c: PALIGNR XMM4,xmmword ptr [0x00102000],0xf *)
| 0x10168c => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x78 256))))
)
(* 0x101696: PALIGNR XMM3,XMM3,0x10 *)
| 0x101696 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x80 256))))
)
(* 0x10169c: PALIGNR XMM8,XMM9,0x10 *)
| 0x10169c => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x80 256))))
)
(* 0x1016a3: PALIGNR XMM9,XMM8,0x10 *)
| 0x1016a3 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x80 256))))
)
(* 0x1016aa: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x10 *)
| 0x1016aa => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x80 256))))
)
(* 0x1016b3: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x10 *)
| 0x1016b3 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x80 256))))
)
(* 0x1016be: PALIGNR XMM4,xmmword ptr [0x00102000],0x10 *)
| 0x1016be => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x80 256))))
)
(* 0x1016c8: PALIGNR XMM3,XMM3,0x11 *)
| 0x1016c8 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x88 256))))
)
(* 0x1016ce: PALIGNR XMM8,XMM9,0x11 *)
| 0x1016ce => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x88 256))))
)
(* 0x1016d5: PALIGNR XMM9,XMM8,0x11 *)
| 0x1016d5 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x88 256))))
)
(* 0x1016dc: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x11 *)
| 0x1016dc => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x88 256))))
)
(* 0x1016e5: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x11 *)
| 0x1016e5 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x88 256))))
)
(* 0x1016f0: PALIGNR XMM4,xmmword ptr [0x00102000],0x11 *)
| 0x1016f0 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x88 256))))
)
(* 0x1016fa: PALIGNR XMM3,XMM3,0x1f *)
| 0x1016fa => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0xf8 256))))
)
(* 0x101700: PALIGNR XMM8,XMM9,0x1f *)
| 0x101700 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0xf8 256))))
)
(* 0x101707: PALIGNR XMM9,XMM8,0x1f *)
| 0x101707 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0xf8 256))))
)
(* 0x10170e: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x1f *)
| 0x10170e => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0xf8 256))))
)
(* 0x101717: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x1f *)
| 0x101717 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0xf8 256))))
)
(* 0x101722: PALIGNR XMM4,xmmword ptr [0x00102000],0x1f *)
| 0x101722 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0xf8 256))))
)
(* 0x10172c: PALIGNR XMM3,XMM3,0x20 *)
| 0x10172c => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x100 256))))
)
(* 0x101732: PALIGNR XMM8,XMM9,0x20 *)
| 0x101732 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x100 256))))
)
(* 0x101739: PALIGNR XMM9,XMM8,0x20 *)
| 0x101739 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x100 256))))
)
(* 0x101740: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x20 *)
| 0x101740 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x100 256))))
)
(* 0x101749: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x20 *)
| 0x101749 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x100 256))))
)
(* 0x101754: PALIGNR XMM4,xmmword ptr [0x00102000],0x20 *)
| 0x101754 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x100 256))))
)
(* 0x10175e: PALIGNR XMM3,XMM3,0x21 *)
| 0x10175e => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x108 256))))
)
(* 0x101764: PALIGNR XMM8,XMM9,0x21 *)
| 0x101764 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x108 256))))
)
(* 0x10176b: PALIGNR XMM9,XMM8,0x21 *)
| 0x10176b => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x108 256))))
)
(* 0x101772: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x21 *)
| 0x101772 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x108 256))))
)
(* 0x10177b: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x21 *)
| 0x10177b => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x108 256))))
)
(* 0x101786: PALIGNR XMM4,xmmword ptr [0x00102000],0x21 *)
| 0x101786 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x108 256))))
)
(* 0x101790: PALIGNR XMM3,XMM3,0x7f *)
| 0x101790 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x3f8 256))))
)
(* 0x101796: PALIGNR XMM8,XMM9,0x7f *)
| 0x101796 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x3f8 256))))
)
(* 0x10179d: PALIGNR XMM9,XMM8,0x7f *)
| 0x10179d => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x3f8 256))))
)
(* 0x1017a4: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x7f *)
| 0x1017a4 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x3f8 256))))
)
(* 0x1017ad: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x7f *)
| 0x1017ad => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x3f8 256))))
)
(* 0x1017b8: PALIGNR XMM4,xmmword ptr [0x00102000],0x7f *)
| 0x1017b8 => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x3f8 256))))
)
(* 0x1017c2: PALIGNR XMM3,XMM3,0x80 *)
| 0x1017c2 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x400 256))))
)
(* 0x1017c8: PALIGNR XMM8,XMM9,0x80 *)
| 0x1017c8 => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x400 256))))
)
(* 0x1017cf: PALIGNR XMM9,XMM8,0x80 *)
| 0x1017cf => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x400 256))))
)
(* 0x1017d6: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x80 *)
| 0x1017d6 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x400 256))))
)
(* 0x1017df: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0x80 *)
| 0x1017df => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x400 256))))
)
(* 0x1017ea: PALIGNR XMM4,xmmword ptr [0x00102000],0x80 *)
| 0x1017ea => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x400 256))))
)
(* 0x1017f4: PALIGNR XMM3,XMM3,0xff *)
| 0x1017f4 => Some (6,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))) (Word 0x7f8 256))))
)
(* 0x1017fa: PALIGNR XMM8,XMM9,0xff *)
| 0x1017fa => Some (7,
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM8)) (Extract 127 0 (Var R_YMM9))) (Word 0x7f8 256))))
)
(* 0x101801: PALIGNR XMM9,XMM8,0xff *)
| 0x101801 => Some (7,
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM8))) (Word 0x7f8 256))))
)
(* 0x101808: PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0xff *)
| 0x101808 => Some (9,
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM15)) (Load (Var V_MEM64) (BinOp OP_PLUS (BinOp OP_PLUS (BinOp OP_TIMES (Var R_RCX) (Word 0x2 64)) (Var R_RDI)) (Word 0xffffffffffffffef 64)) LittleE 16)) (Word 0x7f8 256))))
)
(* 0x101811: PALIGNR XMM10,xmmword ptr [R8 + 0x1234],0xff *)
| 0x101811 => Some (11,
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM10)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R8) (Word 0x1234 64)) LittleE 16)) (Word 0x7f8 256))))
)
(* 0x10181c: PALIGNR XMM4,xmmword ptr [0x00102000],0xff *)
| 0x10181c => Some (10,
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Extract 127 0 (BinOp OP_RSHIFT (Concat (Extract 127 0 (Var R_YMM4)) (Load (Var V_MEM64) (Word 0x102000 64) LittleE 16)) (Word 0x7f8 256))))
)
(* 0x101826: RET *)
| 0x101826 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e34_align_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
