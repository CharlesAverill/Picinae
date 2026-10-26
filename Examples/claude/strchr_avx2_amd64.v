(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_0029d200
entry: 0x29d200 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition strchr_avx2_amd64 : program := fun _ a => match a with

(* 0x0029d200: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x0029d204: VMOVD XMM0,ESI *)
(*          4: VMOVD XMM0,ESI *)
| 0x4 => Some (4,
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Extract 31 0 (Var R_RSI))))
)

(* 0x0029d208: MOV EAX,EDI *)
(*          8: MOV EAX,EDI *)
| 0x8 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d20a: AND EAX,0xfff *)
(*         10: AND EAX,0xfff *)
| 0xa => Some (5,
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

(* 0x0029d20f: VPBROADCASTB YMM0,XMM0 *)
(*         15: VPBROADCASTB YMM0,XMM0 *)
| 0xf => Some (5,
	Move (V_TEMP 0) (Extract 7 0 (Var R_YMM0)) $;
	Move R_YMM0 (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Var (V_TEMP 0)) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) (Var (V_TEMP 0))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM0)))
)

(* 0x0029d214: VPXOR XMM9,XMM9,XMM9 *)
(*         20: VPXOR XMM9,XMM9,XMM9 *)
| 0x14 => Some (5,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 127 0 (Var R_YMM9)) (Extract 127 0 (Var R_YMM9))) $;
	Move R_YMM9 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d219: CMP EAX,0xfe0 *)
(*         25: CMP EAX,0xfe0 *)
| 0x19 => Some (5,
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

(* 0x0029d21e: JA 0x0029d430 *)
(*         30: JA 0x0029d430 *)
| 0x1e => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x230 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d224: VMOVDQU YMM8,ymmword ptr [RDI] *)
(*         36: VMOVDQU YMM8,ymmword ptr [RDI] *)
| 0x24 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d228: VPCMPEQB YMM1,YMM0,YMM8 *)
(*         40: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0x28 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d22d: VPCMPEQB YMM2,YMM9,YMM8 *)
(*         45: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0x2d => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d232: VPOR YMM1,YMM2,YMM1 *)
(*         50: VPOR YMM1,YMM2,YMM1 *)
| 0x32 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d236: VPMOVMSKB EAX,YMM1 *)
(*         54: VPMOVMSKB EAX,YMM1 *)
| 0x36 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d23a: TEST EAX,EAX *)
(*         58: TEST EAX,EAX *)
| 0x3a => Some (2,
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

(* 0x0029d23c: JZ 0x0029d2e0 *)
(*         60: JZ 0x0029d2e0 *)
| 0x3c => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d242: TZCNT EAX,EAX *)
(*         66: TZCNT EAX,EAX *)
| 0x42 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d246: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*         70: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x46 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d24a: JNZ 0x0029d275 *)
(*         74: JNZ 0x0029d275 *)
| 0x4a => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x75 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d24c: ADD RAX,RDI *)
(*         76: ADD RAX,RDI *)
| 0x4c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d24f: VZEROUPPER *)
(*         79: VZEROUPPER *)
| 0x4f => Some (3,
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

(* 0x0029d252: RET *)
(*         82: RET *)
| 0x52 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d260: TZCNT EAX,EAX *)
(*         96: TZCNT EAX,EAX *)
| 0x60 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d264: ADD RDI,0x61 *)
(*        100: ADD RDI,0x61 *)
| 0x64 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x61 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d268: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        104: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x68 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d26c: JNZ 0x0029d275 *)
(*        108: JNZ 0x0029d275 *)
| 0x6c => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x75 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d26e: ADD RAX,RDI *)
(*        110: ADD RAX,RDI *)
| 0x6e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d271: VZEROUPPER *)
(*        113: VZEROUPPER *)
| 0x71 => Some (3,
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

(* 0x0029d274: RET *)
(*        116: RET *)
| 0x74 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d275: XOR EAX,EAX *)
(*        117: XOR EAX,EAX *)
| 0x75 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d277: VZEROUPPER *)
(*        119: VZEROUPPER *)
| 0x77 => Some (3,
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

(* 0x0029d27a: RET *)
(*        122: RET *)
| 0x7a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d280: TZCNT EAX,EAX *)
(*        128: TZCNT EAX,EAX *)
| 0x80 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d284: INC RDI *)
(*        132: INC RDI *)
| 0x84 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d287: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        135: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x87 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d28b: JNZ 0x0029d275 *)
(*        139: JNZ 0x0029d275 *)
| 0x8b => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x75 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d28d: ADD RAX,RDI *)
(*        141: ADD RAX,RDI *)
| 0x8d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d290: VZEROUPPER *)
(*        144: VZEROUPPER *)
| 0x90 => Some (3,
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

(* 0x0029d293: RET *)
(*        147: RET *)
| 0x93 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d2a0: TZCNT EAX,EAX *)
(*        160: TZCNT EAX,EAX *)
| 0xa0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d2a4: ADD RDI,0x21 *)
(*        164: ADD RDI,0x21 *)
| 0xa4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x21 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d2a8: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        168: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0xa8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d2ac: JNZ 0x0029d275 *)
(*        172: JNZ 0x0029d275 *)
| 0xac => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x75 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d2ae: ADD RAX,RDI *)
(*        174: ADD RAX,RDI *)
| 0xae => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d2b1: VZEROUPPER *)
(*        177: VZEROUPPER *)
| 0xb1 => Some (3,
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

(* 0x0029d2b4: RET *)
(*        180: RET *)
| 0xb4 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d2c0: TZCNT EAX,EAX *)
(*        192: TZCNT EAX,EAX *)
| 0xc0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d2c4: ADD RDI,0x41 *)
(*        196: ADD RDI,0x41 *)
| 0xc4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x41 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d2c8: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        200: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0xc8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d2cc: JNZ 0x0029d275 *)
(*        204: JNZ 0x0029d275 *)
| 0xcc => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x75 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d2ce: ADD RAX,RDI *)
(*        206: ADD RAX,RDI *)
| 0xce => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d2d1: VZEROUPPER *)
(*        209: VZEROUPPER *)
| 0xd1 => Some (3,
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

(* 0x0029d2d4: RET *)
(*        212: RET *)
| 0xd4 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d2e0: OR RDI,0x1f *)
(*        224: OR RDI,0x1f *)
| 0xe0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_OR (Var R_RDI) (Word 0x1f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d2e4: VMOVDQA YMM8,ymmword ptr [RDI + 0x1] *)
(*        228: VMOVDQA YMM8,ymmword ptr [RDI + 0x1] *)
| 0xe4 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d2e9: VPCMPEQB YMM1,YMM0,YMM8 *)
(*        233: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0xe9 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d2ee: VPCMPEQB YMM2,YMM9,YMM8 *)
(*        238: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0xee => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d2f3: VPOR YMM1,YMM2,YMM1 *)
(*        243: VPOR YMM1,YMM2,YMM1 *)
| 0xf3 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d2f7: VPMOVMSKB EAX,YMM1 *)
(*        247: VPMOVMSKB EAX,YMM1 *)
| 0xf7 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d2fb: TEST EAX,EAX *)
(*        251: TEST EAX,EAX *)
| 0xfb => Some (2,
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

(* 0x0029d2fd: JNZ 0x0029d280 *)
(*        253: JNZ 0x0029d280 *)
| 0xfd => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x80 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d2ff: VMOVDQA YMM8,ymmword ptr [RDI + 0x21] *)
(*        255: VMOVDQA YMM8,ymmword ptr [RDI + 0x21] *)
| 0xff => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d304: VPCMPEQB YMM1,YMM0,YMM8 *)
(*        260: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0x104 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d309: VPCMPEQB YMM2,YMM9,YMM8 *)
(*        265: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0x109 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d30e: VPOR YMM1,YMM2,YMM1 *)
(*        270: VPOR YMM1,YMM2,YMM1 *)
| 0x10e => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d312: VPMOVMSKB EAX,YMM1 *)
(*        274: VPMOVMSKB EAX,YMM1 *)
| 0x112 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d316: TEST EAX,EAX *)
(*        278: TEST EAX,EAX *)
| 0x116 => Some (2,
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

(* 0x0029d318: JNZ 0x0029d2a0 *)
(*        280: JNZ 0x0029d2a0 *)
| 0x118 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xa0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d31a: VMOVDQA YMM8,ymmword ptr [RDI + 0x41] *)
(*        282: VMOVDQA YMM8,ymmword ptr [RDI + 0x41] *)
| 0x11a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d31f: VPCMPEQB YMM1,YMM0,YMM8 *)
(*        287: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0x11f => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d324: VPCMPEQB YMM2,YMM9,YMM8 *)
(*        292: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0x124 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d329: VPOR YMM1,YMM2,YMM1 *)
(*        297: VPOR YMM1,YMM2,YMM1 *)
| 0x129 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d32d: VPMOVMSKB EAX,YMM1 *)
(*        301: VPMOVMSKB EAX,YMM1 *)
| 0x12d => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d331: TEST EAX,EAX *)
(*        305: TEST EAX,EAX *)
| 0x131 => Some (2,
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

(* 0x0029d333: JNZ 0x0029d2c0 *)
(*        307: JNZ 0x0029d2c0 *)
| 0x133 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xc0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d335: VMOVDQA YMM8,ymmword ptr [RDI + 0x61] *)
(*        309: VMOVDQA YMM8,ymmword ptr [RDI + 0x61] *)
| 0x135 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d33a: VPCMPEQB YMM1,YMM0,YMM8 *)
(*        314: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0x13a => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d33f: VPCMPEQB YMM2,YMM9,YMM8 *)
(*        319: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0x13f => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d344: VPOR YMM1,YMM2,YMM1 *)
(*        324: VPOR YMM1,YMM2,YMM1 *)
| 0x144 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d348: VPMOVMSKB EAX,YMM1 *)
(*        328: VPMOVMSKB EAX,YMM1 *)
| 0x148 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d34c: TEST EAX,EAX *)
(*        332: TEST EAX,EAX *)
| 0x14c => Some (2,
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

(* 0x0029d34e: JNZ 0x0029d260 *)
(*        334: JNZ 0x0029d260 *)
| 0x14e => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x60 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d354: ADD RDI,0x81 *)
(*        340: ADD RDI,0x81 *)
| 0x154 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x81 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x81 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x81 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x81 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d35b: AND RDI,-0x80 *)
(*        347: AND RDI,-0x80 *)
| 0x15b => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d35f: NOP *)
(*        351: NOP *)
| 0x15f => Some (1,
	Nop
)

(* 0x0029d360: VMOVDQA YMM5,ymmword ptr [RDI] *)
(*        352: VMOVDQA YMM5,ymmword ptr [RDI] *)
| 0x160 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move R_YMM5 (Var (V_TEMP 0)) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM5)))
)

(* 0x0029d364: VMOVDQA YMM6,ymmword ptr [RDI + 0x20] *)
(*        356: VMOVDQA YMM6,ymmword ptr [RDI + 0x20] *)
| 0x164 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM6 (Var (V_TEMP 1)) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM6)))
)

(* 0x0029d369: VMOVDQA YMM7,ymmword ptr [RDI + 0x40] *)
(*        361: VMOVDQA YMM7,ymmword ptr [RDI + 0x40] *)
| 0x169 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM7 (Var (V_TEMP 1)) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM7)))
)

(* 0x0029d36e: VMOVDQA YMM8,ymmword ptr [RDI + 0x60] *)
(*        366: VMOVDQA YMM8,ymmword ptr [RDI + 0x60] *)
| 0x16e => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d373: VPXOR YMM1,YMM0,YMM5 *)
(*        371: VPXOR YMM1,YMM0,YMM5 *)
| 0x173 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_YMM0) (Var R_YMM5)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d377: VPXOR YMM2,YMM0,YMM6 *)
(*        375: VPXOR YMM2,YMM0,YMM6 *)
| 0x177 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_YMM0) (Var R_YMM6)) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d37b: VPXOR YMM3,YMM0,YMM7 *)
(*        379: VPXOR YMM3,YMM0,YMM7 *)
| 0x17b => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_YMM0) (Var R_YMM7)) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d37f: VPXOR YMM4,YMM0,YMM8 *)
(*        383: VPXOR YMM4,YMM0,YMM8 *)
| 0x17f => Some (5,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_YMM0) (Var R_YMM8)) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d384: VPMINUB YMM1,YMM5,YMM1 *)
(*        388: VPMINUB YMM1,YMM5,YMM1 *)
| 0x184 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM1))) (Extract 255 248 (Var R_YMM5)) (Extract 255 248 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM1))) (Extract 247 240 (Var R_YMM5)) (Extract 247 240 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM1))) (Extract 239 232 (Var R_YMM5)) (Extract 239 232 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM1))) (Extract 231 224 (Var R_YMM5)) (Extract 231 224 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM1))) (Extract 223 216 (Var R_YMM5)) (Extract 223 216 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM1))) (Extract 215 208 (Var R_YMM5)) (Extract 215 208 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM1))) (Extract 207 200 (Var R_YMM5)) (Extract 207 200 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM1))) (Extract 199 192 (Var R_YMM5)) (Extract 199 192 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM1))) (Extract 191 184 (Var R_YMM5)) (Extract 191 184 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM1))) (Extract 183 176 (Var R_YMM5)) (Extract 183 176 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM1))) (Extract 175 168 (Var R_YMM5)) (Extract 175 168 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM1))) (Extract 167 160 (Var R_YMM5)) (Extract 167 160 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM1))) (Extract 159 152 (Var R_YMM5)) (Extract 159 152 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM1))) (Extract 151 144 (Var R_YMM5)) (Extract 151 144 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM1))) (Extract 143 136 (Var R_YMM5)) (Extract 143 136 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM1))) (Extract 135 128 (Var R_YMM5)) (Extract 135 128 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM1))) (Extract 127 120 (Var R_YMM5)) (Extract 127 120 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM1))) (Extract 119 112 (Var R_YMM5)) (Extract 119 112 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM1))) (Extract 111 104 (Var R_YMM5)) (Extract 111 104 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM1))) (Extract 103 96 (Var R_YMM5)) (Extract 103 96 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM1))) (Extract 95 88 (Var R_YMM5)) (Extract 95 88 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM1))) (Extract 87 80 (Var R_YMM5)) (Extract 87 80 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM1))) (Extract 79 72 (Var R_YMM5)) (Extract 79 72 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM1))) (Extract 71 64 (Var R_YMM5)) (Extract 71 64 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM1))) (Extract 63 56 (Var R_YMM5)) (Extract 63 56 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM1))) (Extract 55 48 (Var R_YMM5)) (Extract 55 48 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM1))) (Extract 47 40 (Var R_YMM5)) (Extract 47 40 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM1))) (Extract 39 32 (Var R_YMM5)) (Extract 39 32 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM1))) (Extract 31 24 (Var R_YMM5)) (Extract 31 24 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM1))) (Extract 23 16 (Var R_YMM5)) (Extract 23 16 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM1))) (Extract 15 8 (Var R_YMM5)) (Extract 15 8 (Var R_YMM1))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM1))) (Extract 7 0 (Var R_YMM5)) (Extract 7 0 (Var R_YMM1)))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d388: VPMINUB YMM2,YMM6,YMM2 *)
(*        392: VPMINUB YMM2,YMM6,YMM2 *)
| 0x188 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM2))) (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM2))) (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM2))) (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM2))) (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM2))) (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM2))) (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM2))) (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM2))) (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM2))) (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM2))) (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM2))) (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM2))) (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM2))) (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM2))) (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM2))) (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM2))) (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM2))) (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM2))) (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM2))) (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM2))) (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM2))) (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM2))) (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM2))) (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM2))) (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM2))) (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM2))) (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM2))) (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM2))) (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM2))) (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM2))) (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM2))) (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM2))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM2))) (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM2)))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d38c: VPMINUB YMM3,YMM7,YMM3 *)
(*        396: VPMINUB YMM3,YMM7,YMM3 *)
| 0x18c => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM7)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM7)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM7)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM7)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM7)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM7)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM7)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM7)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM7)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM7)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM7)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM7)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM7)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM7)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM7)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM7)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM7)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM7)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM7)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM7)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM7)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM7)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM7)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM7)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM7)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM7)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM7)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM7)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM7)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM7)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM7)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM7)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM7)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM7)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM7)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM7)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM7)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM7)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM7)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM7)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM7)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM7)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM7)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM7)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM7)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM7)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM7)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM7)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM7)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM7)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM7)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM7)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM7)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM7)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM7)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM7)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM7)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM7)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM7)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM7)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM7)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM7)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM7)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM7)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d390: VPMINUB YMM4,YMM8,YMM4 *)
(*        400: VPMINUB YMM4,YMM8,YMM4 *)
| 0x190 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM8)) (Extract 255 248 (Var R_YMM4))) (Extract 255 248 (Var R_YMM8)) (Extract 255 248 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM8)) (Extract 247 240 (Var R_YMM4))) (Extract 247 240 (Var R_YMM8)) (Extract 247 240 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM8)) (Extract 239 232 (Var R_YMM4))) (Extract 239 232 (Var R_YMM8)) (Extract 239 232 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM8)) (Extract 231 224 (Var R_YMM4))) (Extract 231 224 (Var R_YMM8)) (Extract 231 224 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM8)) (Extract 223 216 (Var R_YMM4))) (Extract 223 216 (Var R_YMM8)) (Extract 223 216 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM8)) (Extract 215 208 (Var R_YMM4))) (Extract 215 208 (Var R_YMM8)) (Extract 215 208 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM8)) (Extract 207 200 (Var R_YMM4))) (Extract 207 200 (Var R_YMM8)) (Extract 207 200 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM8)) (Extract 199 192 (Var R_YMM4))) (Extract 199 192 (Var R_YMM8)) (Extract 199 192 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM8)) (Extract 191 184 (Var R_YMM4))) (Extract 191 184 (Var R_YMM8)) (Extract 191 184 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM8)) (Extract 183 176 (Var R_YMM4))) (Extract 183 176 (Var R_YMM8)) (Extract 183 176 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM8)) (Extract 175 168 (Var R_YMM4))) (Extract 175 168 (Var R_YMM8)) (Extract 175 168 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM8)) (Extract 167 160 (Var R_YMM4))) (Extract 167 160 (Var R_YMM8)) (Extract 167 160 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM8)) (Extract 159 152 (Var R_YMM4))) (Extract 159 152 (Var R_YMM8)) (Extract 159 152 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM8)) (Extract 151 144 (Var R_YMM4))) (Extract 151 144 (Var R_YMM8)) (Extract 151 144 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM8)) (Extract 143 136 (Var R_YMM4))) (Extract 143 136 (Var R_YMM8)) (Extract 143 136 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM8)) (Extract 135 128 (Var R_YMM4))) (Extract 135 128 (Var R_YMM8)) (Extract 135 128 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM8)) (Extract 127 120 (Var R_YMM4))) (Extract 127 120 (Var R_YMM8)) (Extract 127 120 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM8)) (Extract 119 112 (Var R_YMM4))) (Extract 119 112 (Var R_YMM8)) (Extract 119 112 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM8)) (Extract 111 104 (Var R_YMM4))) (Extract 111 104 (Var R_YMM8)) (Extract 111 104 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM8)) (Extract 103 96 (Var R_YMM4))) (Extract 103 96 (Var R_YMM8)) (Extract 103 96 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM8)) (Extract 95 88 (Var R_YMM4))) (Extract 95 88 (Var R_YMM8)) (Extract 95 88 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM8)) (Extract 87 80 (Var R_YMM4))) (Extract 87 80 (Var R_YMM8)) (Extract 87 80 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM8)) (Extract 79 72 (Var R_YMM4))) (Extract 79 72 (Var R_YMM8)) (Extract 79 72 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM8)) (Extract 71 64 (Var R_YMM4))) (Extract 71 64 (Var R_YMM8)) (Extract 71 64 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM8)) (Extract 63 56 (Var R_YMM4))) (Extract 63 56 (Var R_YMM8)) (Extract 63 56 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM8)) (Extract 55 48 (Var R_YMM4))) (Extract 55 48 (Var R_YMM8)) (Extract 55 48 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM8)) (Extract 47 40 (Var R_YMM4))) (Extract 47 40 (Var R_YMM8)) (Extract 47 40 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM8)) (Extract 39 32 (Var R_YMM4))) (Extract 39 32 (Var R_YMM8)) (Extract 39 32 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM8)) (Extract 31 24 (Var R_YMM4))) (Extract 31 24 (Var R_YMM8)) (Extract 31 24 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM8)) (Extract 23 16 (Var R_YMM4))) (Extract 23 16 (Var R_YMM8)) (Extract 23 16 (Var R_YMM4))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM8)) (Extract 15 8 (Var R_YMM4))) (Extract 15 8 (Var R_YMM8)) (Extract 15 8 (Var R_YMM4))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM8)) (Extract 7 0 (Var R_YMM4))) (Extract 7 0 (Var R_YMM8)) (Extract 7 0 (Var R_YMM4)))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d394: VPMINUB YMM5,YMM2,YMM1 *)
(*        404: VPMINUB YMM5,YMM2,YMM1 *)
| 0x194 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var R_YMM1))) (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var R_YMM1))) (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var R_YMM1))) (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var R_YMM1))) (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var R_YMM1))) (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var R_YMM1))) (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var R_YMM1))) (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var R_YMM1))) (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var R_YMM1))) (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var R_YMM1))) (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var R_YMM1))) (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var R_YMM1))) (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var R_YMM1))) (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var R_YMM1))) (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var R_YMM1))) (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var R_YMM1))) (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1))) (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1))) (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1))) (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1))) (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1))) (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1))) (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1))) (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1))) (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1))) (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1))) (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1))) (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1))) (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1))) (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1))) (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1))) (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1))) (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1)))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d398: VPMINUB YMM6,YMM4,YMM3 *)
(*        408: VPMINUB YMM6,YMM4,YMM3 *)
| 0x198 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM3))) (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM3))) (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM3))) (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM3))) (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM3))) (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM3))) (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM3))) (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM3))) (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM3))) (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM3))) (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM3))) (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM3))) (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM3))) (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM3))) (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM3))) (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM3))) (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM3))) (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM3))) (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM3))) (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM3))) (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM3))) (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM3))) (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM3))) (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM3))) (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM3))) (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM3))) (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM3))) (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM3))) (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM3))) (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM3))) (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM3))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM3))) (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM3))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM3))) (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM3)))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d39c: VPMINUB YMM6,YMM6,YMM5 *)
(*        412: VPMINUB YMM6,YMM6,YMM5 *)
| 0x19c => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM5))) (Extract 255 248 (Var R_YMM6)) (Extract 255 248 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM5))) (Extract 247 240 (Var R_YMM6)) (Extract 247 240 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM5))) (Extract 239 232 (Var R_YMM6)) (Extract 239 232 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM5))) (Extract 231 224 (Var R_YMM6)) (Extract 231 224 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM5))) (Extract 223 216 (Var R_YMM6)) (Extract 223 216 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM5))) (Extract 215 208 (Var R_YMM6)) (Extract 215 208 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM5))) (Extract 207 200 (Var R_YMM6)) (Extract 207 200 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM5))) (Extract 199 192 (Var R_YMM6)) (Extract 199 192 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM5))) (Extract 191 184 (Var R_YMM6)) (Extract 191 184 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM5))) (Extract 183 176 (Var R_YMM6)) (Extract 183 176 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM5))) (Extract 175 168 (Var R_YMM6)) (Extract 175 168 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM5))) (Extract 167 160 (Var R_YMM6)) (Extract 167 160 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM5))) (Extract 159 152 (Var R_YMM6)) (Extract 159 152 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM5))) (Extract 151 144 (Var R_YMM6)) (Extract 151 144 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM5))) (Extract 143 136 (Var R_YMM6)) (Extract 143 136 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM5))) (Extract 135 128 (Var R_YMM6)) (Extract 135 128 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM5))) (Extract 127 120 (Var R_YMM6)) (Extract 127 120 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM5))) (Extract 119 112 (Var R_YMM6)) (Extract 119 112 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM5))) (Extract 111 104 (Var R_YMM6)) (Extract 111 104 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM5))) (Extract 103 96 (Var R_YMM6)) (Extract 103 96 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM5))) (Extract 95 88 (Var R_YMM6)) (Extract 95 88 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM5))) (Extract 87 80 (Var R_YMM6)) (Extract 87 80 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM5))) (Extract 79 72 (Var R_YMM6)) (Extract 79 72 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM5))) (Extract 71 64 (Var R_YMM6)) (Extract 71 64 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM5))) (Extract 63 56 (Var R_YMM6)) (Extract 63 56 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM5))) (Extract 55 48 (Var R_YMM6)) (Extract 55 48 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM5))) (Extract 47 40 (Var R_YMM6)) (Extract 47 40 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM5))) (Extract 39 32 (Var R_YMM6)) (Extract 39 32 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM5))) (Extract 31 24 (Var R_YMM6)) (Extract 31 24 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM5))) (Extract 23 16 (Var R_YMM6)) (Extract 23 16 (Var R_YMM5))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM5))) (Extract 15 8 (Var R_YMM6)) (Extract 15 8 (Var R_YMM5))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM5))) (Extract 7 0 (Var R_YMM6)) (Extract 7 0 (Var R_YMM5)))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d3a0: VPCMPEQB YMM6,YMM9,YMM6 *)
(*        416: VPCMPEQB YMM6,YMM9,YMM6 *)
| 0x1a0 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM6)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM6)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM6)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d3a4: VPMOVMSKB ECX,YMM6 *)
(*        420: VPMOVMSKB ECX,YMM6 *)
| 0x1a4 => Some (4,
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
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x0029d3a8: SUB RDI,-0x80 *)
(*        424: SUB RDI,-0x80 *)
| 0x1a8 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d3ac: TEST ECX,ECX *)
(*        428: TEST ECX,ECX *)
| 0x1ac => Some (2,
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

(* 0x0029d3ae: JZ 0x0029d360 *)
(*        430: JZ 0x0029d360 *)
| 0x1ae => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x160 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d3b0: VPCMPEQB YMM1,YMM9,YMM1 *)
(*        432: VPCMPEQB YMM1,YMM9,YMM1 *)
| 0x1b0 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM1)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM1)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d3b4: VPMOVMSKB EAX,YMM1 *)
(*        436: VPMOVMSKB EAX,YMM1 *)
| 0x1b4 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d3b8: TEST EAX,EAX *)
(*        440: TEST EAX,EAX *)
| 0x1b8 => Some (2,
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

(* 0x0029d3ba: JNZ 0x0029d3f0 *)
(*        442: JNZ 0x0029d3f0 *)
| 0x1ba => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x1f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d3bc: VPCMPEQB YMM2,YMM9,YMM5 *)
(*        444: VPCMPEQB YMM2,YMM9,YMM5 *)
| 0x1bc => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM5)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM5)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d3c0: VPMOVMSKB EAX,YMM2 *)
(*        448: VPMOVMSKB EAX,YMM2 *)
| 0x1c0 => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d3c4: TEST EAX,EAX *)
(*        452: TEST EAX,EAX *)
| 0x1c4 => Some (2,
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

(* 0x0029d3c6: JNZ 0x0029d410 *)
(*        454: JNZ 0x0029d410 *)
| 0x1c6 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x210 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d3c8: VPCMPEQB YMM3,YMM9,YMM3 *)
(*        456: VPCMPEQB YMM3,YMM9,YMM3 *)
| 0x1c8 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM3)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM3)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d3cc: VPMOVMSKB EAX,YMM3 *)
(*        460: VPMOVMSKB EAX,YMM3 *)
| 0x1cc => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d3d0: SHL RCX,0x20 *)
(*        464: SHL RCX,0x20 *)
| 0x1d0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 64))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
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

(* 0x0029d3d4: OR RAX,RCX *)
(*        468: OR RAX,RCX *)
| 0x1d4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (Var R_RAX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d3d7: TZCNT RAX,RAX *)
(*        471: TZCNT RAX,RAX *)
| 0x1d7 => Some (5,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (Var R_RAX) $;
	Rep (Word 65 64) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 64))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 64))) (Word 0x8000000000000000 64)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move R_RAX (Var (V_TEMP 0))
)

(* 0x0029d3dc: SUB RDI,0x40 *)
(*        476: SUB RDI,0x40 *)
| 0x1dc => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d3e0: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        480: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x1e0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d3e4: JNZ 0x0029d405 *)
(*        484: JNZ 0x0029d405 *)
| 0x1e4 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x205 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d3e6: ADD RAX,RDI *)
(*        486: ADD RAX,RDI *)
| 0x1e6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d3e9: VZEROUPPER *)
(*        489: VZEROUPPER *)
| 0x1e9 => Some (3,
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

(* 0x0029d3ec: RET *)
(*        492: RET *)
| 0x1ec => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d3f0: TZCNT EAX,EAX *)
(*        496: TZCNT EAX,EAX *)
| 0x1f0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d3f4: ADD RDI,-0x80 *)
(*        500: ADD RDI,-0x80 *)
| 0x1f4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d3f8: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        504: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x1f8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d3fc: JNZ 0x0029d405 *)
(*        508: JNZ 0x0029d405 *)
| 0x1fc => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x205 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d3fe: ADD RAX,RDI *)
(*        510: ADD RAX,RDI *)
| 0x1fe => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d401: VZEROUPPER *)
(*        513: VZEROUPPER *)
| 0x201 => Some (3,
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

(* 0x0029d404: RET *)
(*        516: RET *)
| 0x204 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d405: XOR EAX,EAX *)
(*        517: XOR EAX,EAX *)
| 0x205 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d407: VZEROUPPER *)
(*        519: VZEROUPPER *)
| 0x207 => Some (3,
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

(* 0x0029d40a: RET *)
(*        522: RET *)
| 0x20a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d410: TZCNT EAX,EAX *)
(*        528: TZCNT EAX,EAX *)
| 0x210 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d414: SUB RDI,0x60 *)
(*        532: SUB RDI,0x60 *)
| 0x214 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x60 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x60 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x60 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x60 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x60 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d418: CMP SIL,byte ptr [RDI + RAX*0x1] *)
(*        536: CMP SIL,byte ptr [RDI + RAX*0x1] *)
| 0x218 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d41c: JNZ 0x0029d405 *)
(*        540: JNZ 0x0029d405 *)
| 0x21c => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x205 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d41e: ADD RAX,RDI *)
(*        542: ADD RAX,RDI *)
| 0x21e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d421: VZEROUPPER *)
(*        545: VZEROUPPER *)
| 0x221 => Some (3,
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

(* 0x0029d424: RET *)
(*        548: RET *)
| 0x224 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d430: MOV RDX,RDI *)
(*        560: MOV RDX,RDI *)
| 0x230 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x0029d433: OR RDI,0x1f *)
(*        563: OR RDI,0x1f *)
| 0x233 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_OR (Var R_RDI) (Word 0x1f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d437: VMOVDQA YMM8,ymmword ptr [RDI + -0x1f] *)
(*        567: VMOVDQA YMM8,ymmword ptr [RDI + -0x1f] *)
| 0x237 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffe1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Var (V_TEMP 1)) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM8)))
)

(* 0x0029d43c: VPCMPEQB YMM1,YMM0,YMM8 *)
(*        572: VPCMPEQB YMM1,YMM0,YMM8 *)
| 0x23c => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d441: VPCMPEQB YMM2,YMM9,YMM8 *)
(*        577: VPCMPEQB YMM2,YMM9,YMM8 *)
| 0x241 => Some (5,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM9)) (Extract 255 248 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM9)) (Extract 247 240 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM9)) (Extract 239 232 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM9)) (Extract 231 224 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM9)) (Extract 223 216 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM9)) (Extract 215 208 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM9)) (Extract 207 200 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM9)) (Extract 199 192 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM9)) (Extract 191 184 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM9)) (Extract 183 176 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM9)) (Extract 175 168 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM9)) (Extract 167 160 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM9)) (Extract 159 152 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM9)) (Extract 151 144 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM9)) (Extract 143 136 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM9)) (Extract 135 128 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM9)) (Extract 127 120 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM9)) (Extract 119 112 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM9)) (Extract 111 104 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM9)) (Extract 103 96 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM9)) (Extract 95 88 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM9)) (Extract 87 80 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM9)) (Extract 79 72 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM9)) (Extract 71 64 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM9)) (Extract 63 56 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM9)) (Extract 55 48 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM9)) (Extract 47 40 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM9)) (Extract 39 32 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM9)) (Extract 31 24 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM9)) (Extract 23 16 (Var R_YMM8)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM9)) (Extract 15 8 (Var R_YMM8)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM9)) (Extract 7 0 (Var R_YMM8)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d446: VPOR YMM1,YMM2,YMM1 *)
(*        582: VPOR YMM1,YMM2,YMM1 *)
| 0x246 => Some (4,
	Move (V_TEMP 0) (BinOp OP_OR (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d44a: VPMOVMSKB EAX,YMM1 *)
(*        586: VPMOVMSKB EAX,YMM1 *)
| 0x24a => Some (4,
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
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d44e: SARX EAX,EAX,EDX *)
(*        590: SARX EAX,EAX,EDX *)
| 0x24e => Some (5,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1f 32)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d453: TEST EAX,EAX *)
(*        595: TEST EAX,EAX *)
| 0x253 => Some (2,
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

(* 0x0029d455: JZ 0x0029d2e4 *)
(*        597: JZ 0x0029d2e4 *)
| 0x255 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0xe4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d45b: TZCNT EAX,EAX *)
(*        603: TZCNT EAX,EAX *)
| 0x25b => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d45f: XOR ECX,ECX *)
(*        607: XOR ECX,ECX *)
| 0x25f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_XOR (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d461: CMP SIL,byte ptr [RDX + RAX*0x1] *)
(*        609: CMP SIL,byte ptr [RDX + RAX*0x1] *)
| 0x261 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move (V_TEMP 3) (Var (V_TEMP 2)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_RSI)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 3)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 4) (BinOp OP_MINUS (Extract 7 0 (Var R_RSI)) (Var (V_TEMP 3))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0xff 8)) $;
	Move (V_TEMP 6) (UnOp OP_POPCOUNT (Var (V_TEMP 5))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 8))))
)

(* 0x0029d465: LEA RAX,[RDX + RAX*0x1] *)
(*        613: LEA RAX,[RDX + RAX*0x1] *)
| 0x265 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move R_RAX (Var (V_TEMP 1))
)

(* 0x0029d469: CMOVNZ RAX,RCX *)
(*        617: CMOVNZ RAX,RCX *)
| 0x269 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Var R_RCX) $;
	Move (V_TEMP 2) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x26d 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Var (V_TEMP 1))
)

(* 0x0029d46d: VZEROUPPER *)
(*        621: VZEROUPPER *)
| 0x26d => Some (3,
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

(* 0x0029d470: RET *)
(*        624: RET *)
| 0x270 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strchr_avx2_amd64.
Proof. Picinae_typecheck. Qed.

