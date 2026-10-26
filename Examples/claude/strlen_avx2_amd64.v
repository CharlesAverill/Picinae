(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_0029d860
entry: 0x29d860 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition strlen_avx2_amd64 : program := fun _ a => match a with

(* 0x0029d860: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x0029d864: MOV EAX,EDI *)
(*          4: MOV EAX,EDI *)
| 0x4 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d866: MOV RDX,RDI *)
(*          6: MOV RDX,RDI *)
| 0x6 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x0029d869: VPXOR XMM0,XMM0,XMM0 *)
(*          9: VPXOR XMM0,XMM0,XMM0 *)
| 0x9 => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d86d: AND EAX,0xfff *)
(*         13: AND EAX,0xfff *)
| 0xd => Some (5,
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

(* 0x0029d872: CMP EAX,0xfe0 *)
(*         18: CMP EAX,0xfe0 *)
| 0x12 => Some (5,
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

(* 0x0029d877: JA 0x0029d9b0 *)
(*         23: JA 0x0029d9b0 *)
| 0x17 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x150 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d87d: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI] *)
(*         29: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI] *)
| 0x1d => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x0029d881: VPMOVMSKB EAX,YMM1 *)
(*         33: VPMOVMSKB EAX,YMM1 *)
| 0x21 => Some (4,
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

(* 0x0029d885: TEST EAX,EAX *)
(*         37: TEST EAX,EAX *)
| 0x25 => Some (2,
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

(* 0x0029d887: JZ 0x0029d8e0 *)
(*         39: JZ 0x0029d8e0 *)
| 0x27 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x80 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d889: TZCNT EAX,EAX *)
(*         41: TZCNT EAX,EAX *)
| 0x29 => Some (4,
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

(* 0x0029d88d: VZEROUPPER *)
(*         45: VZEROUPPER *)
| 0x2d => Some (3,
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

(* 0x0029d890: RET *)
(*         48: RET *)
| 0x30 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d8a0: TZCNT EAX,EAX *)
(*         64: TZCNT EAX,EAX *)
| 0x40 => Some (4,
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

(* 0x0029d8a4: SUB EDI,EDX *)
(*         68: SUB EDI,EDX *)
| 0x44 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8a6: INC EDI *)
(*         70: INC EDI *)
| 0x46 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x1 32))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8a8: ADD EAX,EDI *)
(*         72: ADD EAX,EDI *)
| 0x48 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8aa: VZEROUPPER *)
(*         74: VZEROUPPER *)
| 0x4a => Some (3,
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

(* 0x0029d8ad: RET *)
(*         77: RET *)
| 0x4d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d8b0: TZCNT EAX,EAX *)
(*         80: TZCNT EAX,EAX *)
| 0x50 => Some (4,
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

(* 0x0029d8b4: SUB EDI,EDX *)
(*         84: SUB EDI,EDX *)
| 0x54 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8b6: ADD EDI,0x21 *)
(*         86: ADD EDI,0x21 *)
| 0x56 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x21 32)) (Extract 31 0 (Var R_RDI))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x21 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x21 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x21 32))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8b9: ADD EAX,EDI *)
(*         89: ADD EAX,EDI *)
| 0x59 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8bb: VZEROUPPER *)
(*         91: VZEROUPPER *)
| 0x5b => Some (3,
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

(* 0x0029d8be: RET *)
(*         94: RET *)
| 0x5e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d8c0: TZCNT EAX,EAX *)
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

(* 0x0029d8c4: SUB EDI,EDX *)
(*        100: SUB EDI,EDX *)
| 0x64 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8c6: ADD EDI,0x41 *)
(*        102: ADD EDI,0x41 *)
| 0x66 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x41 32)) (Extract 31 0 (Var R_RDI))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x41 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x41 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x41 32))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8c9: ADD EAX,EDI *)
(*        105: ADD EAX,EDI *)
| 0x69 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8cb: VZEROUPPER *)
(*        107: VZEROUPPER *)
| 0x6b => Some (3,
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

(* 0x0029d8ce: RET *)
(*        110: RET *)
| 0x6e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d8d0: TZCNT EAX,EAX *)
(*        112: TZCNT EAX,EAX *)
| 0x70 => Some (4,
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

(* 0x0029d8d4: SUB EDI,EDX *)
(*        116: SUB EDI,EDX *)
| 0x74 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDI)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8d6: ADD EDI,0x61 *)
(*        118: ADD EDI,0x61 *)
| 0x76 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x61 32)) (Extract 31 0 (Var R_RDI))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x61 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x61 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDI)) (Word 0x61 32))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8d9: ADD EAX,EDI *)
(*        121: ADD EAX,EDI *)
| 0x79 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDI)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d8db: VZEROUPPER *)
(*        123: VZEROUPPER *)
| 0x7b => Some (3,
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

(* 0x0029d8de: RET *)
(*        126: RET *)
| 0x7e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d8e0: OR RDI,0x1f *)
(*        128: OR RDI,0x1f *)
| 0x80 => Some (4,
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

(* 0x0029d8e4: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x1] *)
(*        132: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x1] *)
| 0x84 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d8e9: VPMOVMSKB EAX,YMM1 *)
(*        137: VPMOVMSKB EAX,YMM1 *)
| 0x89 => Some (4,
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

(* 0x0029d8ed: TEST EAX,EAX *)
(*        141: TEST EAX,EAX *)
| 0x8d => Some (2,
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

(* 0x0029d8ef: JNZ 0x0029d8a0 *)
(*        143: JNZ 0x0029d8a0 *)
| 0x8f => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x40 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d8f1: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x21] *)
(*        145: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x21] *)
| 0x91 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d8f6: VPMOVMSKB EAX,YMM1 *)
(*        150: VPMOVMSKB EAX,YMM1 *)
| 0x96 => Some (4,
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

(* 0x0029d8fa: TEST EAX,EAX *)
(*        154: TEST EAX,EAX *)
| 0x9a => Some (2,
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

(* 0x0029d8fc: JNZ 0x0029d8b0 *)
(*        156: JNZ 0x0029d8b0 *)
| 0x9c => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x50 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d8fe: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x41] *)
(*        158: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x41] *)
| 0x9e => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d903: VPMOVMSKB EAX,YMM1 *)
(*        163: VPMOVMSKB EAX,YMM1 *)
| 0xa3 => Some (4,
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

(* 0x0029d907: TEST EAX,EAX *)
(*        167: TEST EAX,EAX *)
| 0xa7 => Some (2,
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

(* 0x0029d909: JNZ 0x0029d8c0 *)
(*        169: JNZ 0x0029d8c0 *)
| 0xa9 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x60 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d90b: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x61] *)
(*        171: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + 0x61] *)
| 0xab => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d910: VPMOVMSKB EAX,YMM1 *)
(*        176: VPMOVMSKB EAX,YMM1 *)
| 0xb0 => Some (4,
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

(* 0x0029d914: TEST EAX,EAX *)
(*        180: TEST EAX,EAX *)
| 0xb4 => Some (2,
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

(* 0x0029d916: JNZ 0x0029d8d0 *)
(*        182: JNZ 0x0029d8d0 *)
| 0xb6 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x70 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d918: INC RDI *)
(*        184: INC RDI *)
| 0xb8 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d91b: OR RDI,0x7f *)
(*        187: OR RDI,0x7f *)
| 0xbb => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_OR (Var R_RDI) (Word 0x7f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d91f: NOP *)
(*        191: NOP *)
| 0xbf => Some (1,
	Nop
)

(* 0x0029d920: VMOVDQA YMM1,ymmword ptr [RDI + 0x1] *)
(*        192: VMOVDQA YMM1,ymmword ptr [RDI + 0x1] *)
| 0xc0 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Var (V_TEMP 1)) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM1)))
)

(* 0x0029d925: VPMINUB YMM2,YMM1,ymmword ptr [RDI + 0x21] *)
(*        197: VPMINUB YMM2,YMM1,ymmword ptr [RDI + 0x21] *)
| 0xc5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x21 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 1)))) (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 1)))) (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 1)))) (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 1)))) (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 1)))) (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 1)))) (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 1)))) (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 1)))) (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 1)))) (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 1)))) (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 1)))) (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 1)))) (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 1)))) (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 1)))) (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 1)))) (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 1)))) (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 1)))) (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 1)))) (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 1)))) (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 1)))) (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 1)))) (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 1)))) (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 1)))) (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 1)))) (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 1)))) (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 1)))) (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 1)))) (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 1)))) (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 1)))) (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 1)))) (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 1)))) (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 1)))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 1)))) (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 1))))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d92a: VMOVDQA YMM3,ymmword ptr [RDI + 0x41] *)
(*        202: VMOVDQA YMM3,ymmword ptr [RDI + 0x41] *)
| 0xca => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x41 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Var (V_TEMP 1)) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM3)))
)

(* 0x0029d92f: VPMINUB YMM4,YMM3,ymmword ptr [RDI + 0x61] *)
(*        207: VPMINUB YMM4,YMM3,ymmword ptr [RDI + 0x61] *)
| 0xcf => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x61 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1)))) (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1)))) (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1)))) (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1)))) (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1)))) (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1)))) (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1)))) (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1)))) (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1)))) (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1)))) (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1)))) (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1)))) (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1)))) (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1)))) (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1)))) (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1)))) (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1)))) (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1)))) (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1)))) (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1)))) (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1)))) (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1)))) (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1)))) (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1)))) (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1)))) (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1)))) (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1)))) (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1)))) (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1)))) (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1)))) (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1)))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1)))) (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1)))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1)))) (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d934: VPMINUB YMM5,YMM4,YMM2 *)
(*        212: VPMINUB YMM5,YMM4,YMM2 *)
| 0xd4 => Some (4,
	Move (V_TEMP 0) (Concat (Ite (BinOp OP_LT (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM2))) (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM2))) (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM2))) (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM2))) (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM2))) (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM2))) (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM2))) (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM2))) (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM2))) (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM2))) (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM2))) (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM2))) (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM2))) (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM2))) (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM2))) (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM2))) (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM2))) (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM2))) (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM2))) (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM2))) (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM2))) (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM2))) (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM2))) (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM2))) (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM2))) (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM2))) (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM2))) (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM2))) (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM2))) (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM2))) (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM2))) (Concat (Ite (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM2))) (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM2))) (Ite (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM2))) (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM2)))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d938: VPCMPEQB YMM5,YMM0,YMM5 *)
(*        216: VPCMPEQB YMM5,YMM0,YMM5 *)
| 0xd8 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM5)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM5)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM5)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d93c: VPMOVMSKB ECX,YMM5 *)
(*        220: VPMOVMSKB ECX,YMM5 *)
| 0xdc => Some (4,
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

(* 0x0029d940: SUB RDI,-0x80 *)
(*        224: SUB RDI,-0x80 *)
| 0xe0 => Some (4,
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

(* 0x0029d944: TEST ECX,ECX *)
(*        228: TEST ECX,ECX *)
| 0xe4 => Some (2,
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

(* 0x0029d946: JZ 0x0029d920 *)
(*        230: JZ 0x0029d920 *)
| 0xe6 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0xc0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d948: VPCMPEQB YMM1,YMM0,YMM1 *)
(*        232: VPCMPEQB YMM1,YMM0,YMM1 *)
| 0xe8 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d94c: VPMOVMSKB EAX,YMM1 *)
(*        236: VPMOVMSKB EAX,YMM1 *)
| 0xec => Some (4,
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

(* 0x0029d950: SUB RDI,RDX *)
(*        240: SUB RDI,RDX *)
| 0xf0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d953: TEST EAX,EAX *)
(*        243: TEST EAX,EAX *)
| 0xf3 => Some (2,
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

(* 0x0029d955: JNZ 0x0029d990 *)
(*        245: JNZ 0x0029d990 *)
| 0xf5 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x130 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d957: VPCMPEQB YMM2,YMM0,YMM2 *)
(*        247: VPCMPEQB YMM2,YMM0,YMM2 *)
| 0xf7 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM2)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM2)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM2)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d95b: VPMOVMSKB EAX,YMM2 *)
(*        251: VPMOVMSKB EAX,YMM2 *)
| 0xfb => Some (4,
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

(* 0x0029d95f: TEST EAX,EAX *)
(*        255: TEST EAX,EAX *)
| 0xff => Some (2,
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

(* 0x0029d961: JNZ 0x0029d9a0 *)
(*        257: JNZ 0x0029d9a0 *)
| 0x101 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x140 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d963: VPCMPEQB YMM3,YMM0,YMM3 *)
(*        259: VPCMPEQB YMM3,YMM0,YMM3 *)
| 0x103 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM3)))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM3)))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM3)))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x0029d967: VPMOVMSKB EAX,YMM3 *)
(*        263: VPMOVMSKB EAX,YMM3 *)
| 0x107 => Some (4,
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

(* 0x0029d96b: SHL RCX,0x20 *)
(*        267: SHL RCX,0x20 *)
| 0x10b => Some (4,
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

(* 0x0029d96f: OR RAX,RCX *)
(*        271: OR RAX,RCX *)
| 0x10f => Some (3,
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

(* 0x0029d972: TZCNT RAX,RAX *)
(*        274: TZCNT RAX,RAX *)
| 0x112 => Some (5,
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

(* 0x0029d977: SUB RDI,0x3f *)
(*        279: SUB RDI,0x3f *)
| 0x117 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x3f 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x3f 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x3f 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3f 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d97b: ADD RAX,RDI *)
(*        283: ADD RAX,RDI *)
| 0x11b => Some (3,
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

(* 0x0029d97e: VZEROUPPER *)
(*        286: VZEROUPPER *)
| 0x11e => Some (3,
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

(* 0x0029d981: RET *)
(*        289: RET *)
| 0x121 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d990: TZCNT EAX,EAX *)
(*        304: TZCNT EAX,EAX *)
| 0x130 => Some (4,
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

(* 0x0029d994: SUB RDI,0x7f *)
(*        308: SUB RDI,0x7f *)
| 0x134 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x7f 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x7f 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x7f 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x7f 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x7f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d998: ADD RAX,RDI *)
(*        312: ADD RAX,RDI *)
| 0x138 => Some (3,
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

(* 0x0029d99b: VZEROUPPER *)
(*        315: VZEROUPPER *)
| 0x13b => Some (3,
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

(* 0x0029d99e: RET *)
(*        318: RET *)
| 0x13e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d9a0: TZCNT EAX,EAX *)
(*        320: TZCNT EAX,EAX *)
| 0x140 => Some (4,
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

(* 0x0029d9a4: SUB RDI,0x5f *)
(*        324: SUB RDI,0x5f *)
| 0x144 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x5f 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x5f 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x5f 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5f 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x5f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x0029d9a8: ADD RAX,RDI *)
(*        328: ADD RAX,RDI *)
| 0x148 => Some (3,
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

(* 0x0029d9ab: VZEROUPPER *)
(*        331: VZEROUPPER *)
| 0x14b => Some (3,
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

(* 0x0029d9ae: RET *)
(*        334: RET *)
| 0x14e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x0029d9b0: OR RDI,0x1f *)
(*        336: OR RDI,0x1f *)
| 0x150 => Some (4,
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

(* 0x0029d9b4: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + -0x1f] *)
(*        340: VPCMPEQB YMM1,YMM0,ymmword ptr [RDI + -0x1f] *)
| 0x154 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffe1 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM0)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM0)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM0)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM0)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM0)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM0)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM0)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM0)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM0)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM0)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM0)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM0)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM0)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM0)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM0)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM0)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x0029d9b9: VPMOVMSKB EAX,YMM1 *)
(*        345: VPMOVMSKB EAX,YMM1 *)
| 0x159 => Some (4,
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

(* 0x0029d9bd: SARX EAX,EAX,EDX *)
(*        349: SARX EAX,EAX,EDX *)
| 0x15d => Some (5,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1f 32)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0029d9c2: TEST EAX,EAX *)
(*        354: TEST EAX,EAX *)
| 0x162 => Some (2,
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

(* 0x0029d9c4: JZ 0x0029d8e4 *)
(*        356: JZ 0x0029d8e4 *)
| 0x164 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x84 64)
	) (* else *) (
		Nop
	)
)

(* 0x0029d9ca: TZCNT EAX,EAX *)
(*        362: TZCNT EAX,EAX *)
| 0x16a => Some (4,
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

(* 0x0029d9ce: VZEROUPPER *)
(*        366: VZEROUPPER *)
| 0x16e => Some (3,
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

(* 0x0029d9d1: RET *)
(*        369: RET *)
| 0x171 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strlen_avx2_amd64.
Proof. Picinae_typecheck. Qed.

