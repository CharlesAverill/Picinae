(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_002989c0
entry: 0x2989c0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition strcmp_avx2_amd64 : program := fun _ a => match a with

(* 0x002989c0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x002989c4: MOV EAX,EDI *)
(*          4: MOV EAX,EDI *)
| 0x4 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x002989c6: XOR EDX,EDX *)
(*          6: XOR EDX,EDX *)
| 0x6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_XOR (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002989c8: VPXOR XMM7,XMM7,XMM7 *)
(*          8: VPXOR XMM7,XMM7,XMM7 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 127 0 (Var R_YMM7)) (Extract 127 0 (Var R_YMM7))) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002989cc: OR EAX,ESI *)
(*         12: OR EAX,ESI *)
| 0xc => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RSI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002989ce: AND EAX,0xfff *)
(*         14: AND EAX,0xfff *)
| 0xe => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xfff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002989d3: CMP EAX,0xf80 *)
(*         19: CMP EAX,0xf80 *)
| 0x13 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xf80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xf80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xf80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xf80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xf80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002989d8: JG 0x00298d30 *)
(*         24: JG 0x00298d30 *)
| 0x18 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x370 64)
	) (* else *) (
		Nop
	)
)

(* 0x002989de: VMOVDQU YMM1,ymmword ptr [RDI] *)
(*         30: VMOVDQU YMM1,ymmword ptr [RDI] *)
| 0x1e => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002989e2: VPCMPEQB YMM0,YMM1,ymmword ptr [RSI] *)
(*         34: VPCMPEQB YMM0,YMM1,ymmword ptr [RSI] *)
| 0x22 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002989e6: VPMINUB YMM0,YMM0,YMM1 *)
(*         38: VPMINUB YMM0,YMM0,YMM1 *)
| 0x26 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM1))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM1))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM1))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM1))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM1))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM1))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM1))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM1))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM1))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM1))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM1))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM1))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM1))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM1))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM1))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM1))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002989ea: VPCMPEQB YMM0,YMM0,YMM7 *)
(*         42: VPCMPEQB YMM0,YMM0,YMM7 *)
| 0x2a => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002989ee: VPMOVMSKB ECX,YMM0 *)
(*         46: VPMOVMSKB ECX,YMM0 *)
| 0x2e => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x002989f2: TEST ECX,ECX *)
(*         50: TEST ECX,ECX *)
| 0x32 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002989f4: JZ 0x00298a70 *)
(*         52: JZ 0x00298a70 *)
| 0x34 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0xb0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002989f6: TZCNT EDX,ECX *)
(*         54: TZCNT EDX,ECX *)
| 0x36 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x002989fa: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
(*         58: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
| 0x3a => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x002989fe: MOVZX EDX,byte ptr [RSI + RDX*0x1] *)
(*         62: MOVZX EDX,byte ptr [RSI + RDX*0x1] *)
| 0x3e => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a02: SUB EAX,EDX *)
(*         66: SUB EAX,EDX *)
| 0x42 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298a04: VZEROUPPER *)
(*         68: VZEROUPPER *)
| 0x44 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298a07: RET *)
(*         71: RET *)
| 0x47 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298a10: TZCNT EDX,ECX *)
(*         80: TZCNT EDX,ECX *)
| 0x50 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a14: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x20] *)
(*         84: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x20] *)
| 0x54 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298a19: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x20] *)
(*         89: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x20] *)
| 0x59 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a1e: SUB EAX,EDX *)
(*         94: SUB EAX,EDX *)
| 0x5e => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298a20: VZEROUPPER *)
(*         96: VZEROUPPER *)
| 0x60 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298a23: RET *)
(*         99: RET *)
| 0x63 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298a30: TZCNT EDX,ECX *)
(*        112: TZCNT EDX,ECX *)
| 0x70 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a34: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x40] *)
(*        116: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x40] *)
| 0x74 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298a39: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x40] *)
(*        121: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x40] *)
| 0x79 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a3e: SUB EAX,EDX *)
(*        126: SUB EAX,EDX *)
| 0x7e => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298a40: VZEROUPPER *)
(*        128: VZEROUPPER *)
| 0x80 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298a43: RET *)
(*        131: RET *)
| 0x83 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298a50: TZCNT EDX,ECX *)
(*        144: TZCNT EDX,ECX *)
| 0x90 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a54: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x60] *)
(*        148: MOVZX EAX,byte ptr [RDI + RDX*0x1 + 0x60] *)
| 0x94 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298a59: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x60] *)
(*        153: MOVZX EDX,byte ptr [RSI + RDX*0x1 + 0x60] *)
| 0x99 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298a5e: SUB EAX,EDX *)
(*        158: SUB EAX,EDX *)
| 0x9e => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298a60: VZEROUPPER *)
(*        160: VZEROUPPER *)
| 0xa0 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298a63: RET *)
(*        163: RET *)
| 0xa3 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298a70: VMOVDQU YMM6,ymmword ptr [RDI + 0x20] *)
(*        176: VMOVDQU YMM6,ymmword ptr [RDI + 0x20] *)
| 0xb0 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00298a75: VPCMPEQB YMM3,YMM6,ymmword ptr [RSI + 0x20] *)
(*        181: VPCMPEQB YMM3,YMM6,ymmword ptr [RSI + 0x20] *)
| 0xb5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298a7a: VPMINUB YMM3,YMM3,YMM6 *)
(*        186: VPMINUB YMM3,YMM3,YMM6 *)
| 0xba => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var R_YMM6))) (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var R_YMM6))) (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var R_YMM6))) (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var R_YMM6))) (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var R_YMM6))) (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var R_YMM6))) (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var R_YMM6))) (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var R_YMM6))) (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var R_YMM6))) (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var R_YMM6))) (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var R_YMM6))) (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var R_YMM6))) (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var R_YMM6))) (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var R_YMM6))) (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var R_YMM6))) (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var R_YMM6))) (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM6))) (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM6))) (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM6))) (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM6))) (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM6))) (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM6))) (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM6))) (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM6))) (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM6))) (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM6))) (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM6))) (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM6))) (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM6))) (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM6))) (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM6))) (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM6))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM6))) (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM6)))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298a7e: VPCMPEQB YMM3,YMM3,YMM7 *)
(*        190: VPCMPEQB YMM3,YMM3,YMM7 *)
| 0xbe => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298a82: VPMOVMSKB ECX,YMM3 *)
(*        194: VPMOVMSKB ECX,YMM3 *)
| 0xc2 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM3) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM3) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM3) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM3) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM3) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM3) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM3) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM3) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM3) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM3) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM3) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM3) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM3) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM3) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM3) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM3) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM3) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM3) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM3) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM3) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM3) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM3) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM3) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM3) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM3) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM3) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM3) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM3) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM3) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM3) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM3) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM3) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298a86: TEST ECX,ECX *)
(*        198: TEST ECX,ECX *)
| 0xc6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298a88: JNZ 0x00298a10 *)
(*        200: JNZ 0x00298a10 *)
| 0xc8 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x50 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298a8a: VMOVDQU YMM5,ymmword ptr [RDI + 0x40] *)
(*        202: VMOVDQU YMM5,ymmword ptr [RDI + 0x40] *)
| 0xca => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00298a8f: VMOVDQU YMM4,ymmword ptr [RDI + 0x60] *)
(*        207: VMOVDQU YMM4,ymmword ptr [RDI + 0x60] *)
| 0xcf => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00298a94: VMOVDQU YMM0,ymmword ptr [RSI + 0x60] *)
(*        212: VMOVDQU YMM0,ymmword ptr [RSI + 0x60] *)
| 0xd4 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00298a99: VPCMPEQB YMM2,YMM5,ymmword ptr [RSI + 0x40] *)
(*        217: VPCMPEQB YMM2,YMM5,ymmword ptr [RSI + 0x40] *)
| 0xd9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298a9e: VPMINUB YMM2,YMM2,YMM5 *)
(*        222: VPMINUB YMM2,YMM2,YMM5 *)
| 0xde => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var R_YMM5))) (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var R_YMM5))) (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var R_YMM5))) (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var R_YMM5))) (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var R_YMM5))) (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var R_YMM5))) (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var R_YMM5))) (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var R_YMM5))) (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var R_YMM5))) (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var R_YMM5))) (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var R_YMM5))) (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var R_YMM5))) (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var R_YMM5))) (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var R_YMM5))) (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var R_YMM5))) (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var R_YMM5))) (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM5))) (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM5))) (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM5))) (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM5))) (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM5))) (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM5))) (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM5))) (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM5))) (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM5))) (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM5))) (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM5))) (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM5))) (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM5))) (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM5))) (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM5))) (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM5))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM5))) (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM5)))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298aa2: VPCMPEQB YMM0,YMM0,YMM4 *)
(*        226: VPCMPEQB YMM0,YMM0,YMM4 *)
| 0xe2 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM4)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM4)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM4)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298aa6: VPCMPEQB YMM2,YMM2,YMM7 *)
(*        230: VPCMPEQB YMM2,YMM2,YMM7 *)
| 0xe6 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298aaa: VPMOVMSKB ECX,YMM2 *)
(*        234: VPMOVMSKB ECX,YMM2 *)
| 0xea => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM2) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM2) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM2) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM2) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM2) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM2) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM2) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM2) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM2) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM2) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM2) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM2) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM2) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM2) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM2) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM2) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM2) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM2) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM2) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM2) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM2) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM2) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM2) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM2) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM2) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM2) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM2) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM2) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM2) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM2) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM2) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM2) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298aae: TEST ECX,ECX *)
(*        238: TEST ECX,ECX *)
| 0xee => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298ab0: JNZ 0x00298a30 *)
(*        240: JNZ 0x00298a30 *)
| 0xf0 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x70 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298ab6: VPMINUB YMM0,YMM0,YMM4 *)
(*        246: VPMINUB YMM0,YMM0,YMM4 *)
| 0xf6 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM4))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM4))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM4))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM4))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM4))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM4))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM4))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM4))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM4))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM4))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM4))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM4))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM4))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM4))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM4))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM4))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM4))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM4))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM4))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM4))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM4))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM4))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM4))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM4))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM4))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM4))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM4))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM4))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM4))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM4))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM4))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM4))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM4))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM4)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298aba: VPCMPEQB YMM0,YMM0,YMM7 *)
(*        250: VPCMPEQB YMM0,YMM0,YMM7 *)
| 0xfa => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298abe: VPMOVMSKB ECX,YMM0 *)
(*        254: VPMOVMSKB ECX,YMM0 *)
| 0xfe => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298ac2: TEST ECX,ECX *)
(*        258: TEST ECX,ECX *)
| 0x102 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298ac4: JNZ 0x00298a50 *)
(*        260: JNZ 0x00298a50 *)
| 0x104 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x90 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298ac6: LEA RDX,[RDI + 0x80] *)
(*        262: LEA RDX,[RDI + 0x80] *)
| 0x106 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x80 64)) $;
	Move R_RDX (Var (V_TEMP 0))
)

(* 0x00298acd: MOV ECX,0x1000 *)
(*        269: MOV ECX,0x1000 *)
| 0x10d => Some (5,
	Move R_RCX (Word 0x1000 64)
)

(* 0x00298ad2: AND RDX,-0x80 *)
(*        274: AND RDX,-0x80 *)
| 0x112 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_AND (Var R_RDX) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ad6: SUB RDX,RDI *)
(*        278: SUB RDX,RDI *)
| 0x116 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ad9: LEA RAX,[RDI + RDX*0x1] *)
(*        281: LEA RAX,[RDI + RDX*0x1] *)
| 0x119 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move R_RAX (Var (V_TEMP 1))
)

(* 0x00298add: ADD RDX,RSI *)
(*        285: ADD RDX,RSI *)
| 0x11d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Var R_RSI)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ae0: MOV RSI,RDX *)
(*        288: MOV RSI,RDX *)
| 0x120 => Some (3,
	Move R_RSI (Var R_RDX)
)

(* 0x00298ae3: AND ESI,0xfff *)
(*        291: AND ESI,0xfff *)
| 0x123 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xfff 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ae9: SUB RCX,RSI *)
(*        297: SUB RCX,RSI *)
| 0x129 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298aec: SHR RCX,0x7 *)
(*        300: SHR RCX,0x7 *)
| 0x12c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x7 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_RCX) $;
	Move R_RCX (BinOp OP_RSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00298af0: MOV ESI,ECX *)
(*        304: MOV ESI,ECX *)
| 0x130 => Some (2,
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Extract 31 0 (Var R_RCX))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00298af2: JMP 0x00298b0d *)
(*        306: JMP 0x00298b0d *)
| 0x132 => Some (2,
	Jmp (Word 0x14d 64)
)

(* 0x00298b00: ADD RAX,0x80 *)
(*        320: ADD RAX,0x80 *)
| 0x140 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x80 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298b06: ADD RDX,0x80 *)
(*        326: ADD RDX,0x80 *)
| 0x146 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Word 0x80 64)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Word 0x80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Word 0x80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298b0d: TEST ESI,ESI *)
(*        333: TEST ESI,ESI *)
| 0x14d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298b0f: LEA ESI,[ESI + -0x1] *)
(*        335: LEA ESI,[ESI + -0x1] *)
| 0x14f => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Extract 31 0 (Var R_RSI)) (Word 0xffffffff 32)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00298b13: JZ 0x00298bf0 *)
(*        339: JZ 0x00298bf0 *)
| 0x153 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x230 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298b19: VMOVDQA YMM0,ymmword ptr [RAX] *)
(*        345: VMOVDQA YMM0,ymmword ptr [RAX] *)
| 0x159 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RAX) LittleE 32) $;
	Move R_YMM0 (Var (V_TEMP 0)) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM0)))
)

(* 0x00298b1d: VMOVDQA YMM3,ymmword ptr [RAX + 0x20] *)
(*        349: VMOVDQA YMM3,ymmword ptr [RAX + 0x20] *)
| 0x15d => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Var (V_TEMP 1)) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM3)))
)

(* 0x00298b22: VPCMPEQB YMM4,YMM0,ymmword ptr [RDX] *)
(*        354: VPCMPEQB YMM4,YMM0,ymmword ptr [RDX] *)
| 0x162 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDX) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00298b26: VPCMPEQB YMM1,YMM3,ymmword ptr [RDX + 0x20] *)
(*        358: VPCMPEQB YMM1,YMM3,ymmword ptr [RDX + 0x20] *)
| 0x166 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298b2b: VPMINUB YMM4,YMM4,YMM0 *)
(*        363: VPMINUB YMM4,YMM4,YMM0 *)
| 0x16b => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM0))) (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM0))) (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM0))) (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM0))) (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM0))) (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM0))) (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM0))) (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM0))) (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM0))) (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM0))) (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM0))) (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM0))) (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM0))) (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM0))) (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM0))) (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM0))) (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM0))) (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM0))) (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM0))) (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM0))) (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM0))) (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM0))) (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM0))) (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM0))) (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM0))) (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM0))) (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM0))) (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM0))) (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM0))) (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM0))) (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM0))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM0))) (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM0))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM0))) (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM0)))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b2f: VPMINUB YMM1,YMM1,YMM3 *)
(*        367: VPMINUB YMM1,YMM1,YMM3 *)
| 0x16f => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b33: VMOVDQA YMM2,ymmword ptr [RAX + 0x40] *)
(*        371: VMOVDQA YMM2,ymmword ptr [RAX + 0x40] *)
| 0x173 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Var (V_TEMP 1)) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM2)))
)

(* 0x00298b38: VPMINUB YMM0,YMM4,YMM1 *)
(*        376: VPMINUB YMM0,YMM4,YMM1 *)
| 0x178 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM1))) (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM1))) (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM1))) (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM1))) (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM1))) (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM1))) (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM1))) (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM1))) (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM1))) (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM1))) (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM1))) (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM1))) (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM1))) (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM1))) (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM1))) (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM1))) (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM1))) (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM1))) (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM1))) (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM1))) (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM1))) (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM1))) (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM1))) (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM1))) (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM1))) (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM1))) (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM1))) (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM1))) (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM1))) (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM1))) (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM1))) (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM1))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM1))) (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM1)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b3c: VMOVDQA YMM3,ymmword ptr [RAX + 0x60] *)
(*        380: VMOVDQA YMM3,ymmword ptr [RAX + 0x60] *)
| 0x17c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RAX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Var (V_TEMP 1)) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM3)))
)

(* 0x00298b41: VPCMPEQB YMM5,YMM2,ymmword ptr [RDX + 0x40] *)
(*        385: VPCMPEQB YMM5,YMM2,ymmword ptr [RDX + 0x40] *)
| 0x181 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298b46: VPCMPEQB YMM6,YMM3,ymmword ptr [RDX + 0x60] *)
(*        390: VPCMPEQB YMM6,YMM3,ymmword ptr [RDX + 0x60] *)
| 0x186 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298b4b: VPMINUB YMM5,YMM5,YMM2 *)
(*        395: VPMINUB YMM5,YMM5,YMM2 *)
| 0x18b => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM2))) (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM2))) (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM2))) (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM2))) (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM2))) (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM2))) (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM2))) (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM2))) (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM2))) (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM2))) (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM2))) (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM2))) (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM2))) (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM2))) (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM2))) (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM2))) (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM2))) (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM2))) (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM2))) (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM2))) (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM2))) (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM2))) (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM2))) (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM2))) (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM2))) (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM2))) (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM2))) (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM2))) (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM2))) (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM2))) (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM2))) (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM2))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM2))) (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM2)))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b4f: VPMINUB YMM6,YMM6,YMM3 *)
(*        399: VPMINUB YMM6,YMM6,YMM3 *)
| 0x18f => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b53: VPMINUB YMM0,YMM0,YMM5 *)
(*        403: VPMINUB YMM0,YMM0,YMM5 *)
| 0x193 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM5))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM5))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM5))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM5))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM5))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM5))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM5))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM5))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM5))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM5))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM5))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM5))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM5))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM5))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM5))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM5))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM5))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM5))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM5))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM5))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM5))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM5))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM5))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM5))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM5))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM5))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM5))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM5))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM5))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM5))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM5))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM5))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM5))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM5)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b57: VPMINUB YMM0,YMM0,YMM6 *)
(*        407: VPMINUB YMM0,YMM0,YMM6 *)
| 0x197 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM6))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM6))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM6))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM6))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM6))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM6))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM6))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM6))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM6))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM6))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM6))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM6))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM6))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM6))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM6))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM6))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM6))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM6))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM6))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM6))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM6))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM6))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM6))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM6))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM6))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM6))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM6))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM6))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM6))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM6))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM6))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM6))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM6))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM6))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM6)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b5b: VPCMPEQB YMM0,YMM0,YMM7 *)
(*        411: VPCMPEQB YMM0,YMM0,YMM7 *)
| 0x19b => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b5f: VPMOVMSKB ECX,YMM0 *)
(*        415: VPMOVMSKB ECX,YMM0 *)
| 0x19f => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298b63: TEST ECX,ECX *)
(*        419: TEST ECX,ECX *)
| 0x1a3 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298b65: JZ 0x00298b00 *)
(*        421: JZ 0x00298b00 *)
| 0x1a5 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x140 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298b67: VPCMPEQB YMM0,YMM4,YMM7 *)
(*        423: VPCMPEQB YMM0,YMM4,YMM7 *)
| 0x1a7 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b6b: VPMOVMSKB EDI,YMM0 *)
(*        427: VPMOVMSKB EDI,YMM0 *)
| 0x1ab => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Var (V_TEMP 0))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00298b6f: TEST EDI,EDI *)
(*        431: TEST EDI,EDI *)
| 0x1af => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298b71: JZ 0x00298b90 *)
(*        433: JZ 0x00298b90 *)
| 0x1b1 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1d0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298b73: TZCNT ECX,EDI *)
(*        435: TZCNT ECX,EDI *)
| 0x1b3 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RDI)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298b77: MOVZX EAX,byte ptr [RAX + RCX*0x1] *)
(*        439: MOVZX EAX,byte ptr [RAX + RCX*0x1] *)
| 0x1b7 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298b7b: MOVZX EDX,byte ptr [RDX + RCX*0x1] *)
(*        443: MOVZX EDX,byte ptr [RDX + RCX*0x1] *)
| 0x1bb => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298b7f: SUB EAX,EDX *)
(*        447: SUB EAX,EDX *)
| 0x1bf => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298b81: VZEROUPPER *)
(*        449: VZEROUPPER *)
| 0x1c1 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298b84: RET *)
(*        452: RET *)
| 0x1c4 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298b90: VPCMPEQB YMM1,YMM1,YMM7 *)
(*        464: VPCMPEQB YMM1,YMM1,YMM7 *)
| 0x1d0 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298b94: VPMOVMSKB ECX,YMM1 *)
(*        468: VPMOVMSKB ECX,YMM1 *)
| 0x1d4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM1) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM1) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM1) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM1) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM1) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM1) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM1) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM1) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM1) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM1) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM1) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM1) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM1) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM1) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM1) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM1) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM1) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM1) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM1) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM1) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM1) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM1) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM1) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM1) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM1) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM1) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM1) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM1) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM1) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM1) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM1) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM1) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298b98: TEST ECX,ECX *)
(*        472: TEST ECX,ECX *)
| 0x1d8 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298b9a: JZ 0x00298bb0 *)
(*        474: JZ 0x00298bb0 *)
| 0x1da => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298b9c: TZCNT EDI,ECX *)
(*        476: TZCNT EDI,ECX *)
| 0x1dc => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Var (V_TEMP 0))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00298ba0: MOVZX EAX,byte ptr [RAX + RDI*0x1 + 0x20] *)
(*        480: MOVZX EAX,byte ptr [RAX + RDI*0x1 + 0x20] *)
| 0x1e0 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298ba5: MOVZX EDX,byte ptr [RDX + RDI*0x1 + 0x20] *)
(*        485: MOVZX EDX,byte ptr [RDX + RDI*0x1 + 0x20] *)
| 0x1e5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298baa: SUB EAX,EDX *)
(*        490: SUB EAX,EDX *)
| 0x1ea => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298bac: VZEROUPPER *)
(*        492: VZEROUPPER *)
| 0x1ec => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298baf: RET *)
(*        495: RET *)
| 0x1ef => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298bb0: VPCMPEQB YMM5,YMM5,YMM7 *)
(*        496: VPCMPEQB YMM5,YMM5,YMM7 *)
| 0x1f0 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298bb4: VPMOVMSKB ECX,YMM5 *)
(*        500: VPMOVMSKB ECX,YMM5 *)
| 0x1f4 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM5) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM5) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM5) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM5) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM5) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM5) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM5) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM5) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM5) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM5) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM5) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM5) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM5) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM5) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM5) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM5) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM5) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM5) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM5) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM5) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM5) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM5) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM5) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM5) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM5) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM5) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM5) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM5) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM5) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM5) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM5) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM5) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298bb8: TEST ECX,ECX *)
(*        504: TEST ECX,ECX *)
| 0x1f8 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298bba: JZ 0x00298bd0 *)
(*        506: JZ 0x00298bd0 *)
| 0x1fa => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x210 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298bbc: TZCNT EDI,ECX *)
(*        508: TZCNT EDI,ECX *)
| 0x1fc => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Var (V_TEMP 0))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00298bc0: MOVZX EAX,byte ptr [RAX + RDI*0x1 + 0x40] *)
(*        512: MOVZX EAX,byte ptr [RAX + RDI*0x1 + 0x40] *)
| 0x200 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298bc5: MOVZX EDX,byte ptr [RDX + RDI*0x1 + 0x40] *)
(*        517: MOVZX EDX,byte ptr [RDX + RDI*0x1 + 0x40] *)
| 0x205 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298bca: SUB EAX,EDX *)
(*        522: SUB EAX,EDX *)
| 0x20a => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298bcc: VZEROUPPER *)
(*        524: VZEROUPPER *)
| 0x20c => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298bcf: RET *)
(*        527: RET *)
| 0x20f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298bd0: VPCMPEQB YMM6,YMM6,YMM7 *)
(*        528: VPCMPEQB YMM6,YMM6,YMM7 *)
| 0x210 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298bd4: VPMOVMSKB ESI,YMM6 *)
(*        532: VPMOVMSKB ESI,YMM6 *)
| 0x214 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM6) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM6) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM6) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM6) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM6) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM6) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM6) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM6) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM6) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM6) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM6) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM6) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM6) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM6) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM6) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM6) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM6) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM6) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM6) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM6) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM6) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM6) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM6) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM6) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM6) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM6) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM6) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM6) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM6) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM6) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM6) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM6) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00298bd8: TZCNT ECX,ESI *)
(*        536: TZCNT ECX,ESI *)
| 0x218 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RSI)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298bdc: MOVZX EAX,byte ptr [RAX + RCX*0x1 + 0x60] *)
(*        540: MOVZX EAX,byte ptr [RAX + RCX*0x1 + 0x60] *)
| 0x21c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298be1: MOVZX EDX,byte ptr [RDX + RCX*0x1 + 0x60] *)
(*        545: MOVZX EDX,byte ptr [RDX + RCX*0x1 + 0x60] *)
| 0x221 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298be6: SUB EAX,EDX *)
(*        550: SUB EAX,EDX *)
| 0x226 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298be8: VZEROUPPER *)
(*        552: VZEROUPPER *)
| 0x228 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298beb: RET *)
(*        555: RET *)
| 0x22b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298bf0: XOR R10D,R10D *)
(*        560: XOR R10D,R10D *)
| 0x230 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R10 (Concat (Extract 63 32 (Var R_R10)) (BinOp OP_XOR (Extract 31 0 (Var R_R10)) (Extract 31 0 (Var R_R10)))) $;
	Move R_R10 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R10))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_R10)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_R10)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_R10)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298bf3: MOV RCX,RDX *)
(*        563: MOV RCX,RDX *)
| 0x233 => Some (3,
	Move R_RCX (Var R_RDX)
)

(* 0x00298bf6: AND ECX,0x7f *)
(*        566: AND ECX,0x7f *)
| 0x236 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7f 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298bf9: SUB R10,RCX *)
(*        569: SUB R10,RCX *)
| 0x239 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_R10) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R10 (BinOp OP_MINUS (Var R_R10) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298bfc: CMP ECX,0x40 *)
(*        572: CMP ECX,0x40 *)
| 0x23c => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00298bff: JGE 0x00298c60 *)
(*        575: JGE 0x00298c60 *)
| 0x23f => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x2a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298c01: VMOVDQU YMM2,ymmword ptr [RAX + R10*0x1] *)
(*        577: VMOVDQU YMM2,ymmword ptr [RAX + R10*0x1] *)
| 0x241 => Some (6,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298c07: VMOVDQU YMM3,ymmword ptr [RAX + R10*0x1 + 0x20] *)
(*        583: VMOVDQU YMM3,ymmword ptr [RAX + R10*0x1 + 0x20] *)
| 0x247 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298c0e: VPCMPEQB YMM0,YMM2,ymmword ptr [RDX + R10*0x1] *)
(*        590: VPCMPEQB YMM0,YMM2,ymmword ptr [RDX + R10*0x1] *)
| 0x24e => Some (6,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move (V_TEMP 3) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 2))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 2))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298c14: VPCMPEQB YMM1,YMM3,ymmword ptr [RDX + R10*0x1 + 0x20] *)
(*        596: VPCMPEQB YMM1,YMM3,ymmword ptr [RDX + R10*0x1 + 0x20] *)
| 0x254 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move (V_TEMP 4) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 3))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 3))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 4))))
)

(* 0x00298c1b: VPMINUB YMM0,YMM0,YMM2 *)
(*        603: VPMINUB YMM0,YMM0,YMM2 *)
| 0x25b => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM2))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM2))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM2))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM2))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM2))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM2))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM2))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM2))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM2))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM2))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM2))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM2))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM2))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM2))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM2))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM2))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM2))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM2))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM2))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM2))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM2))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM2))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM2))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM2))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM2))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM2))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM2))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM2))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM2))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM2))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM2))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM2))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM2))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM2)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c1f: VPMINUB YMM1,YMM1,YMM3 *)
(*        607: VPMINUB YMM1,YMM1,YMM3 *)
| 0x25f => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c23: VPCMPEQB YMM0,YMM0,YMM7 *)
(*        611: VPCMPEQB YMM0,YMM0,YMM7 *)
| 0x263 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c27: VPCMPEQB YMM1,YMM1,YMM7 *)
(*        615: VPCMPEQB YMM1,YMM1,YMM7 *)
| 0x267 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c2b: VPMOVMSKB EDI,YMM0 *)
(*        619: VPMOVMSKB EDI,YMM0 *)
| 0x26b => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Var (V_TEMP 0))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00298c2f: VPMOVMSKB ESI,YMM1 *)
(*        623: VPMOVMSKB ESI,YMM1 *)
| 0x26f => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM1) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM1) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM1) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM1) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM1) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM1) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM1) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM1) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM1) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM1) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM1) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM1) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM1) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM1) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM1) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM1) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM1) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM1) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM1) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM1) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM1) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM1) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM1) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM1) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM1) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM1) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM1) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM1) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM1) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM1) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM1) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM1) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00298c33: SHL RSI,0x20 *)
(*        627: SHL RSI,0x20 *)
| 0x273 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_RSI) $;
	Move R_RSI (BinOp OP_LSHIFT (Var R_RSI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 64))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00298c37: XOR RDI,RSI *)
(*        631: XOR RDI,RSI *)
| 0x277 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_XOR (Var R_RDI) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298c3a: SHR RDI,CL *)
(*        634: SHR RDI,CL *)
| 0x27a => Some (3,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Move R_RDI (BinOp OP_RSHIFT (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 8))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 8)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 8))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 8))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00298c3d: TEST RDI,RDI *)
(*        637: TEST RDI,RDI *)
| 0x27d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 64)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298c40: JZ 0x00298c60 *)
(*        640: JZ 0x00298c60 *)
| 0x280 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x2a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298c42: TZCNT RCX,RDI *)
(*        642: TZCNT RCX,RDI *)
| 0x282 => Some (5,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Rep (Word 65 64) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 64))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 64))) (Word 0x8000000000000000 64)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move R_RCX (Var (V_TEMP 0))
)

(* 0x00298c47: MOVZX EAX,byte ptr [RAX + RCX*0x1] *)
(*        647: MOVZX EAX,byte ptr [RAX + RCX*0x1] *)
| 0x287 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298c4b: MOVZX EDX,byte ptr [RDX + RCX*0x1] *)
(*        651: MOVZX EDX,byte ptr [RDX + RCX*0x1] *)
| 0x28b => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298c4f: SUB EAX,EDX *)
(*        655: SUB EAX,EDX *)
| 0x28f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298c51: VZEROUPPER *)
(*        657: VZEROUPPER *)
| 0x291 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298c54: RET *)
(*        660: RET *)
| 0x294 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298c60: VMOVDQU YMM2,ymmword ptr [RAX + R10*0x1 + 0x40] *)
(*        672: VMOVDQU YMM2,ymmword ptr [RAX + R10*0x1 + 0x40] *)
| 0x2a0 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298c67: VMOVDQU YMM3,ymmword ptr [RAX + R10*0x1 + 0x60] *)
(*        679: VMOVDQU YMM3,ymmword ptr [RAX + R10*0x1 + 0x60] *)
| 0x2a7 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298c6e: VPCMPEQB YMM5,YMM2,ymmword ptr [RDX + R10*0x1 + 0x40] *)
(*        686: VPCMPEQB YMM5,YMM2,ymmword ptr [RDX + R10*0x1 + 0x40] *)
| 0x2ae => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move (V_TEMP 4) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 3))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 3))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 4))))
)

(* 0x00298c75: VPMINUB YMM5,YMM5,YMM2 *)
(*        693: VPMINUB YMM5,YMM5,YMM2 *)
| 0x2b5 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM2))) (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM2))) (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM2))) (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM2))) (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM2))) (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM2))) (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM2))) (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM2))) (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM2))) (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM2))) (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM2))) (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM2))) (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM2))) (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM2))) (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM2))) (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM2))) (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM2))) (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM2))) (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM2))) (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM2))) (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM2))) (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM2))) (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM2))) (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM2))) (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM2))) (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM2))) (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM2))) (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM2))) (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM2))) (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM2))) (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM2))) (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM2))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM2))) (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM2)))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c79: VPCMPEQB YMM6,YMM3,ymmword ptr [RDX + R10*0x1 + 0x60] *)
(*        697: VPCMPEQB YMM6,YMM3,ymmword ptr [RDX + R10*0x1 + 0x60] *)
| 0x2b9 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R10) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move (V_TEMP 4) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 3))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 3))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 4))))
)

(* 0x00298c80: VPCMPEQB YMM5,YMM5,YMM7 *)
(*        704: VPCMPEQB YMM5,YMM5,YMM7 *)
| 0x2c0 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c84: VPMINUB YMM6,YMM6,YMM3 *)
(*        708: VPMINUB YMM6,YMM6,YMM3 *)
| 0x2c4 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c88: VPCMPEQB YMM6,YMM6,YMM7 *)
(*        712: VPCMPEQB YMM6,YMM6,YMM7 *)
| 0x2c8 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298c8c: VPMOVMSKB EDI,YMM5 *)
(*        716: VPMOVMSKB EDI,YMM5 *)
| 0x2cc => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM5) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM5) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM5) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM5) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM5) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM5) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM5) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM5) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM5) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM5) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM5) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM5) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM5) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM5) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM5) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM5) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM5) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM5) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM5) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM5) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM5) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM5) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM5) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM5) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM5) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM5) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM5) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM5) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM5) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM5) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM5) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM5) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Var (V_TEMP 0))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00298c90: VPMOVMSKB ESI,YMM6 *)
(*        720: VPMOVMSKB ESI,YMM6 *)
| 0x2d0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM6) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM6) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM6) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM6) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM6) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM6) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM6) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM6) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM6) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM6) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM6) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM6) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM6) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM6) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM6) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM6) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM6) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM6) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM6) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM6) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM6) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM6) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM6) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM6) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM6) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM6) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM6) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM6) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM6) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM6) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM6) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM6) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00298c94: SHL RSI,0x20 *)
(*        724: SHL RSI,0x20 *)
| 0x2d4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_RSI) $;
	Move R_RSI (BinOp OP_LSHIFT (Var R_RSI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 64))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00298c98: XOR RDI,RSI *)
(*        728: XOR RDI,RSI *)
| 0x2d8 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_XOR (Var R_RDI) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298c9b: XOR R8D,R8D *)
(*        731: XOR R8D,R8D *)
| 0x2db => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (BinOp OP_XOR (Extract 31 0 (Var R_R8)) (Extract 31 0 (Var R_R8)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_R8)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_R8)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_R8)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298c9e: SUB ECX,0x40 *)
(*        734: SUB ECX,0x40 *)
| 0x2de => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RCX)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x40 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ca1: JLE 0x00298ca9 *)
(*        737: JLE 0x00298ca9 *)
| 0x2e1 => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 1) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x2e9 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298ca3: SHR RDI,CL *)
(*        739: SHR RDI,CL *)
| 0x2e3 => Some (3,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Move R_RDI (BinOp OP_RSHIFT (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 8))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 8)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 8))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 8))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00298ca6: MOV R8D,ECX *)
(*        742: MOV R8D,ECX *)
| 0x2e6 => Some (3,
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Extract 31 0 (Var R_RCX))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x00298ca9: MOV ESI,0x1f *)
(*        745: MOV ESI,0x1f *)
| 0x2e9 => Some (5,
	Move R_RSI (Word 0x1f 64)
)

(* 0x00298cae: TEST RDI,RDI *)
(*        750: TEST RDI,RDI *)
| 0x2ee => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 64)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298cb1: JZ 0x00298b19 *)
(*        753: JZ 0x00298b19 *)
| 0x2f1 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x159 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298cb7: TZCNT RCX,RDI *)
(*        759: TZCNT RCX,RDI *)
| 0x2f7 => Some (5,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Rep (Word 65 64) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 64))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 64))) (Word 0x8000000000000000 64)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move R_RCX (Var (V_TEMP 0))
)

(* 0x00298cbc: ADD RCX,R10 *)
(*        764: ADD RCX,R10 *)
| 0x2fc => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Var R_R10)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Var R_R10)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Var R_R10)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298cbf: ADD RCX,R8 *)
(*        767: ADD RCX,R8 *)
| 0x2ff => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Var R_R8)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298cc2: MOVZX EAX,byte ptr [RAX + RCX*0x1 + 0x40] *)
(*        770: MOVZX EAX,byte ptr [RAX + RCX*0x1 + 0x40] *)
| 0x302 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RAX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298cc7: MOVZX EDX,byte ptr [RDX + RCX*0x1 + 0x40] *)
(*        775: MOVZX EDX,byte ptr [RDX + RCX*0x1 + 0x40] *)
| 0x307 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298ccc: SUB EAX,EDX *)
(*        780: SUB EAX,EDX *)
| 0x30c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298cce: VZEROUPPER *)
(*        782: VZEROUPPER *)
| 0x30e => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298cd1: RET *)
(*        785: RET *)
| 0x311 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298ce0: SUB EAX,ECX *)
(*        800: SUB EAX,ECX *)
| 0x320 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ce2: JNZ 0x00298d01 *)
(*        802: JNZ 0x00298d01 *)
| 0x322 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x341 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298ce4: ADD EDX,0x1 *)
(*        804: ADD EDX,0x1 *)
| 0x324 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x1 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x1 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298ce7: CMP EDX,0x80 *)
(*        807: CMP EDX,0x80 *)
| 0x327 => Some (6,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00298ced: JZ 0x00298ac6 *)
(*        813: JZ 0x00298ac6 *)
| 0x32d => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x106 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298cf3: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
(*        819: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
| 0x333 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298cf7: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
(*        823: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
| 0x337 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298cfb: TEST EAX,EAX *)
(*        827: TEST EAX,EAX *)
| 0x33b => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298cfd: JNZ 0x00298ce0 *)
(*        829: JNZ 0x00298ce0 *)
| 0x33d => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x320 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298cff: SUB EAX,ECX *)
(*        831: SUB EAX,ECX *)
| 0x33f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d01: VZEROUPPER *)
(*        833: VZEROUPPER *)
| 0x341 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298d04: RET *)
(*        836: RET *)
| 0x344 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298d10: ADD RDI,RDX *)
(*        848: ADD RDI,RDX *)
| 0x350 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d13: ADD RSI,RDX *)
(*        851: ADD RSI,RDX *)
| 0x353 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RDX)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d16: TZCNT EDX,ECX *)
(*        854: TZCNT EDX,ECX *)
| 0x356 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298d1a: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
(*        858: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
| 0x35a => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298d1e: MOVZX EDX,byte ptr [RSI + RDX*0x1] *)
(*        862: MOVZX EDX,byte ptr [RSI + RDX*0x1] *)
| 0x35e => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00298d22: SUB EAX,EDX *)
(*        866: SUB EAX,EDX *)
| 0x362 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d24: VZEROUPPER *)
(*        868: VZEROUPPER *)
| 0x364 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298d27: RET *)
(*        871: RET *)
| 0x367 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00298d30: CMP EAX,0xfe0 *)
(*        880: CMP EAX,0xfe0 *)
| 0x370 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfe0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d35: JG 0x00298d5e *)
(*        885: JG 0x00298d5e *)
| 0x375 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x39e 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d37: VMOVDQU YMM1,ymmword ptr [RDI + RDX*0x1] *)
(*        887: VMOVDQU YMM1,ymmword ptr [RDI + RDX*0x1] *)
| 0x377 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298d3c: VPCMPEQB YMM0,YMM1,ymmword ptr [RSI + RDX*0x1] *)
(*        892: VPCMPEQB YMM0,YMM1,ymmword ptr [RSI + RDX*0x1] *)
| 0x37c => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move (V_TEMP 3) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 2))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 2))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298d41: VPMINUB YMM0,YMM0,YMM1 *)
(*        897: VPMINUB YMM0,YMM0,YMM1 *)
| 0x381 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM1))) (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM1))) (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM1))) (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM1))) (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM1))) (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM1))) (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM1))) (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM1))) (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM1))) (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM1))) (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM1))) (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM1))) (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM1))) (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM1))) (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM1))) (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM1))) (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1))) (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1))) (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1))) (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1))) (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1))) (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1))) (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1))) (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1))) (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1))) (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1))) (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1))) (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1))) (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1))) (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1))) (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1))) (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1))) (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d45: VPCMPEQB YMM0,YMM0,YMM7 *)
(*        901: VPCMPEQB YMM0,YMM0,YMM7 *)
| 0x385 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM7)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM7)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM7)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d49: VPMOVMSKB ECX,YMM0 *)
(*        905: VPMOVMSKB ECX,YMM0 *)
| 0x389 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM0) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM0) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM0) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM0) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM0) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM0) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM0) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM0) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM0) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM0) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM0) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM0) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM0) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM0) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM0) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM0) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM0) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM0) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM0) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM0) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM0) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM0) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM0) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM0) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM0) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM0) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM0) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM0) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM0) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM0) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM0) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM0) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298d4d: TEST ECX,ECX *)
(*        909: TEST ECX,ECX *)
| 0x38d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d4f: JNZ 0x00298d10 *)
(*        911: JNZ 0x00298d10 *)
| 0x38f => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x350 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d51: ADD EDX,0x20 *)
(*        913: ADD EDX,0x20 *)
| 0x391 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d54: ADD EAX,0x20 *)
(*        916: ADD EAX,0x20 *)
| 0x394 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x20 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x20 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d57: CMP EAX,0xfe0 *)
(*        919: CMP EAX,0xfe0 *)
| 0x397 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfe0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xfe0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d5c: JLE 0x00298d37 *)
(*        924: JLE 0x00298d37 *)
| 0x39c => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 1) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Var (V_TEMP 0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x377 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d5e: CMP EAX,0xff0 *)
(*        926: CMP EAX,0xff0 *)
| 0x39e => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xff0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d63: JG 0x00298d85 *)
(*        931: JG 0x00298d85 *)
| 0x3a3 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x3c5 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d65: VMOVDQU XMM1,xmmword ptr [RDI + RDX*0x1] *)
(*        933: VMOVDQU XMM1,xmmword ptr [RDI + RDX*0x1] *)
| 0x3a5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 16) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298d6a: VPCMPEQB XMM0,XMM1,xmmword ptr [RSI + RDX*0x1] *)
(*        938: VPCMPEQB XMM0,XMM1,xmmword ptr [RSI + RDX*0x1] *)
| 0x3aa => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 16) $;
	Move (V_TEMP 3) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM1))) (Extract 127 120 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM1))) (Extract 119 112 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM1))) (Extract 111 104 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM1))) (Extract 103 96 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM1))) (Extract 95 88 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM1))) (Extract 87 80 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM1))) (Extract 79 72 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM1))) (Extract 71 64 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM1))) (Extract 63 56 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM1))) (Extract 55 48 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM1))) (Extract 47 40 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM1))) (Extract 39 32 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM1))) (Extract 31 24 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM1))) (Extract 23 16 (Var (V_TEMP 2))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM1))) (Extract 15 8 (Var (V_TEMP 2))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM1))) (Extract 7 0 (Var (V_TEMP 2))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298d6f: VPMINUB XMM0,XMM0,XMM1 *)
(*        943: VPMINUB XMM0,XMM0,XMM1 *)
| 0x3af => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Ite (BinOp OP_LT (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1)))) (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d73: VPCMPEQB XMM0,XMM0,XMM7 *)
(*        947: VPCMPEQB XMM0,XMM0,XMM7 *)
| 0x3b3 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d77: VPMOVMSKB ECX,XMM0 *)
(*        951: VPMOVMSKB ECX,XMM0 *)
| 0x3b7 => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298d7b: TEST ECX,ECX *)
(*        955: TEST ECX,ECX *)
| 0x3bb => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d7d: JNZ 0x00298d10 *)
(*        957: JNZ 0x00298d10 *)
| 0x3bd => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x350 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d7f: ADD EDX,0x10 *)
(*        959: ADD EDX,0x10 *)
| 0x3bf => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d82: ADD EAX,0x10 *)
(*        962: ADD EAX,0x10 *)
| 0x3c2 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x10 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x10 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298d85: CMP EAX,0xff8 *)
(*        965: CMP EAX,0xff8 *)
| 0x3c5 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xff8 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff8 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xff8 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298d8a: JG 0x00298dba *)
(*        970: JG 0x00298dba *)
| 0x3ca => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x3fa 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298d8c: VMOVQ XMM1,qword ptr [RDI + RDX*0x1] *)
(*        972: VMOVQ XMM1,qword ptr [RDI + RDX*0x1] *)
| 0x3cc => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 2))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298d91: VMOVQ XMM0,qword ptr [RSI + RDX*0x1] *)
(*        977: VMOVQ XMM0,qword ptr [RSI + RDX*0x1] *)
| 0x3d1 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 8) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 2))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00298d96: VPCMPEQB XMM0,XMM1,XMM0 *)
(*        982: VPCMPEQB XMM0,XMM1,XMM0 *)
| 0x3d6 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM1))) (Extract 127 120 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM1))) (Extract 119 112 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM1))) (Extract 111 104 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM1))) (Extract 103 96 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM1))) (Extract 95 88 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM1))) (Extract 87 80 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM1))) (Extract 79 72 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM1))) (Extract 71 64 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM1))) (Extract 63 56 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM1))) (Extract 55 48 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM1))) (Extract 47 40 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM1))) (Extract 39 32 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM1))) (Extract 31 24 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM1))) (Extract 23 16 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM1))) (Extract 15 8 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM1))) (Extract 7 0 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d9a: VPMINUB XMM0,XMM0,XMM1 *)
(*        986: VPMINUB XMM0,XMM0,XMM1 *)
| 0x3da => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Ite (BinOp OP_LT (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1)))) (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298d9e: VPCMPEQB XMM0,XMM0,XMM7 *)
(*        990: VPCMPEQB XMM0,XMM0,XMM7 *)
| 0x3de => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298da2: VPMOVMSKB ECX,XMM0 *)
(*        994: VPMOVMSKB ECX,XMM0 *)
| 0x3e2 => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298da6: AND ECX,0xff *)
(*        998: AND ECX,0xff *)
| 0x3e6 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298dac: TEST ECX,ECX *)
(*       1004: TEST ECX,ECX *)
| 0x3ec => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298dae: JNZ 0x00298d10 *)
(*       1006: JNZ 0x00298d10 *)
| 0x3ee => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x350 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298db4: ADD EDX,0x8 *)
(*       1012: ADD EDX,0x8 *)
| 0x3f4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x8 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x8 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298db7: ADD EAX,0x8 *)
(*       1015: ADD EAX,0x8 *)
| 0x3f7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x8 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x8 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298dba: CMP EAX,0xffc *)
(*       1018: CMP EAX,0xffc *)
| 0x3fa => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xffc 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffc 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffc 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffc 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffc 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298dbf: JG 0x00298de9 *)
(*       1023: JG 0x00298de9 *)
| 0x3ff => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x429 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298dc1: VMOVD XMM1,dword ptr [RDI + RDX*0x1] *)
(*       1025: VMOVD XMM1,dword ptr [RDI + RDX*0x1] *)
| 0x401 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 4) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298dc6: VMOVD XMM0,dword ptr [RSI + RDX*0x1] *)
(*       1030: VMOVD XMM0,dword ptr [RSI + RDX*0x1] *)
| 0x406 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 4) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00298dcb: VPCMPEQB XMM0,XMM1,XMM0 *)
(*       1035: VPCMPEQB XMM0,XMM1,XMM0 *)
| 0x40b => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM1))) (Extract 127 120 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM1))) (Extract 119 112 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM1))) (Extract 111 104 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM1))) (Extract 103 96 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM1))) (Extract 95 88 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM1))) (Extract 87 80 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM1))) (Extract 79 72 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM1))) (Extract 71 64 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM1))) (Extract 63 56 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM1))) (Extract 55 48 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM1))) (Extract 47 40 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM1))) (Extract 39 32 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM1))) (Extract 31 24 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM1))) (Extract 23 16 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM1))) (Extract 15 8 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM1))) (Extract 7 0 (Extract 127 0 (Var R_YMM0))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298dcf: VPMINUB XMM0,XMM0,XMM1 *)
(*       1039: VPMINUB XMM0,XMM0,XMM1 *)
| 0x40f => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM1)))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM1)))) (Ite (BinOp OP_LT (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1)))) (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM1))))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298dd3: VPCMPEQB XMM0,XMM0,XMM7 *)
(*       1043: VPCMPEQB XMM0,XMM0,XMM7 *)
| 0x413 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM0))) (Extract 127 120 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM0))) (Extract 119 112 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM0))) (Extract 111 104 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM0))) (Extract 103 96 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM0))) (Extract 95 88 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM0))) (Extract 87 80 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM0))) (Extract 79 72 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM0))) (Extract 71 64 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM0))) (Extract 63 56 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM0))) (Extract 55 48 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM0))) (Extract 47 40 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM0))) (Extract 39 32 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM0))) (Extract 31 24 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM0))) (Extract 23 16 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM0))) (Extract 15 8 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM0))) (Extract 7 0 (Extract 127 0 (Var R_YMM7))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00298dd7: VPMOVMSKB ECX,XMM0 *)
(*       1047: VPMOVMSKB ECX,XMM0 *)
| 0x417 => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298ddb: AND ECX,0xf *)
(*       1051: AND ECX,0xf *)
| 0x41b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298dde: TEST ECX,ECX *)
(*       1054: TEST ECX,ECX *)
| 0x41e => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298de0: JNZ 0x00298d10 *)
(*       1056: JNZ 0x00298d10 *)
| 0x420 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x350 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298de6: ADD EDX,0x4 *)
(*       1062: ADD EDX,0x4 *)
| 0x426 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x4 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x4 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298de9: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
(*       1065: MOVZX EAX,byte ptr [RDI + RDX*0x1] *)
| 0x429 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00298ded: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
(*       1069: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
| 0x42d => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00298df1: TEST EAX,EAX *)
(*       1073: TEST EAX,EAX *)
| 0x431 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x00298df3: JNZ 0x00298ce0 *)
(*       1075: JNZ 0x00298ce0 *)
| 0x433 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x320 64)
	) (* else *) (
		Nop
	)
)

(* 0x00298df9: SUB EAX,ECX *)
(*       1081: SUB EAX,ECX *)
| 0x439 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RCX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00298dfb: VZEROUPPER *)
(*       1083: VZEROUPPER *)
| 0x43b => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x00298dfe: RET *)
(*       1086: RET *)
| 0x43e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx strcmp_avx2_amd64.
Proof. Picinae_typecheck. Qed.

