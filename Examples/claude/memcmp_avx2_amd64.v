(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_00299b00
entry: 0x299b00 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition memcmp_avx2_amd64 : program := fun _ a => match a with

(* 0x00299b00: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00299b04: CMP RDX,0x20 *)
(*          4: CMP RDX,0x20 *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x20 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299b08: JC 0x00299de0 *)
(*          8: JC 0x00299de0 *)
| 0x8 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x2e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b0e: VMOVDQU YMM1,ymmword ptr [RSI] *)
(*         14: VMOVDQU YMM1,ymmword ptr [RSI] *)
| 0xe => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299b12: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
(*         18: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
| 0x12 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299b16: VPMOVMSKB EAX,YMM1 *)
(*         22: VPMOVMSKB EAX,YMM1 *)
| 0x16 => Some (4,
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

(* 0x00299b1a: INC EAX *)
(*         26: INC EAX *)
| 0x1a => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299b1c: JNZ 0x00299be0 *)
(*         28: JNZ 0x00299be0 *)
| 0x1c => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b22: CMP RDX,0x40 *)
(*         34: CMP RDX,0x40 *)
| 0x22 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299b26: JBE 0x00299d64 *)
(*         38: JBE 0x00299d64 *)
| 0x26 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x264 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b2c: VMOVDQU YMM2,ymmword ptr [RSI + 0x20] *)
(*         44: VMOVDQU YMM2,ymmword ptr [RSI + 0x20] *)
| 0x2c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299b31: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
(*         49: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
| 0x31 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299b36: VPMOVMSKB EAX,YMM2 *)
(*         54: VPMOVMSKB EAX,YMM2 *)
| 0x36 => Some (4,
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

(* 0x00299b3a: INC EAX *)
(*         58: INC EAX *)
| 0x3a => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299b3c: JNZ 0x00299c00 *)
(*         60: JNZ 0x00299c00 *)
| 0x3c => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x100 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b42: CMP RDX,0x80 *)
(*         66: CMP RDX,0x80 *)
| 0x42 => Some (7,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299b49: JBE 0x00299d50 *)
(*         73: JBE 0x00299d50 *)
| 0x49 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x250 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b4f: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
(*         79: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
| 0x4f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299b54: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
(*         84: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
| 0x54 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299b59: VPMOVMSKB EAX,YMM3 *)
(*         89: VPMOVMSKB EAX,YMM3 *)
| 0x59 => Some (4,
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

(* 0x00299b5d: INC EAX *)
(*         93: INC EAX *)
| 0x5d => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299b5f: JNZ 0x00299c20 *)
(*         95: JNZ 0x00299c20 *)
| 0x5f => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x120 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b65: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
(*        101: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
| 0x65 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299b6a: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
(*        106: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
| 0x6a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299b6f: VPMOVMSKB ECX,YMM4 *)
(*        111: VPMOVMSKB ECX,YMM4 *)
| 0x6f => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM4) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM4) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM4) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM4) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM4) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM4) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM4) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM4) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM4) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM4) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM4) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM4) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM4) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM4) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM4) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM4) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM4) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM4) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM4) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM4) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM4) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM4) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM4) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM4) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM4) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM4) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM4) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM4) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM4) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM4) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM4) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM4) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299b73: INC ECX *)
(*        115: INC ECX *)
| 0x73 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299b75: JNZ 0x00299c5b *)
(*        117: JNZ 0x00299c5b *)
| 0x75 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x15b 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b7b: CMP RDX,0x100 *)
(*        123: CMP RDX,0x100 *)
| 0x7b => Some (7,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x100 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299b82: JA 0x00299c70 *)
(*        130: JA 0x00299c70 *)
| 0x82 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x170 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299b88: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
(*        136: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x88 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299b8e: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
(*        142: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
| 0x8e => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299b94: LEA RDI,[RDI + RDX*0x1 + -0x80] *)
(*        148: LEA RDI,[RDI + RDX*0x1 + -0x80] *)
| 0x94 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDI (Var (V_TEMP 2))
)

(* 0x00299b99: LEA RSI,[RSI + RDX*0x1 + -0x80] *)
(*        153: LEA RSI,[RSI + RDX*0x1 + -0x80] *)
| 0x99 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RSI (Var (V_TEMP 2))
)

(* 0x00299b9e: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
(*        158: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
| 0x9e => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299ba2: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
(*        162: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
| 0xa2 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299ba7: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
(*        167: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
| 0xa7 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299bac: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
(*        172: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
| 0xac => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299bb1: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
(*        177: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
| 0xb1 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299bb6: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
(*        182: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
| 0xb6 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299bbb: VPAND YMM5,YMM2,YMM1 *)
(*        187: VPAND YMM5,YMM2,YMM1 *)
| 0xbb => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299bbf: VPAND YMM6,YMM4,YMM3 *)
(*        191: VPAND YMM6,YMM4,YMM3 *)
| 0xbf => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM4) (Var R_YMM3)) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299bc3: VPAND YMM7,YMM6,YMM5 *)
(*        195: VPAND YMM7,YMM6,YMM5 *)
| 0xc3 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM6) (Var R_YMM5)) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299bc7: VPMOVMSKB ECX,YMM7 *)
(*        199: VPMOVMSKB ECX,YMM7 *)
| 0xc7 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM7) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM7) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM7) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM7) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM7) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM7) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM7) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM7) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM7) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM7) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM7) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM7) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM7) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM7) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM7) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM7) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM7) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM7) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM7) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM7) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM7) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM7) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM7) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM7) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM7) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM7) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM7) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM7) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM7) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM7) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM7) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM7) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299bcb: INC ECX *)
(*        203: INC ECX *)
| 0xcb => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299bcd: JNZ 0x00299c43 *)
(*        205: JNZ 0x00299c43 *)
| 0xcd => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x143 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299bcf: VZEROUPPER *)
(*        207: VZEROUPPER *)
| 0xcf => Some (3,
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

(* 0x00299bd2: RET *)
(*        210: RET *)
| 0xd2 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299be0: TZCNT EAX,EAX *)
(*        224: TZCNT EAX,EAX *)
| 0xe0 => Some (4,
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

(* 0x00299be4: MOVZX ECX,byte ptr [RSI + RAX*0x1] *)
(*        228: MOVZX ECX,byte ptr [RSI + RAX*0x1] *)
| 0xe4 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299be8: MOVZX EAX,byte ptr [RDI + RAX*0x1] *)
(*        232: MOVZX EAX,byte ptr [RDI + RAX*0x1] *)
| 0xe8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 2)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299bec: SUB EAX,ECX *)
(*        236: SUB EAX,ECX *)
| 0xec => Some (2,
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

(* 0x00299bee: VZEROUPPER *)
(*        238: VZEROUPPER *)
| 0xee => Some (3,
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

(* 0x00299bf1: RET *)
(*        241: RET *)
| 0xf1 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299c00: TZCNT EAX,EAX *)
(*        256: TZCNT EAX,EAX *)
| 0x100 => Some (4,
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

(* 0x00299c04: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x20] *)
(*        260: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x20] *)
| 0x104 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299c09: MOVZX EAX,byte ptr [RDI + RAX*0x1 + 0x20] *)
(*        265: MOVZX EAX,byte ptr [RDI + RAX*0x1 + 0x20] *)
| 0x109 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299c0e: SUB EAX,ECX *)
(*        270: SUB EAX,ECX *)
| 0x10e => Some (2,
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

(* 0x00299c10: VZEROUPPER *)
(*        272: VZEROUPPER *)
| 0x110 => Some (3,
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

(* 0x00299c13: RET *)
(*        275: RET *)
| 0x113 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299c20: TZCNT EAX,EAX *)
(*        288: TZCNT EAX,EAX *)
| 0x120 => Some (4,
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

(* 0x00299c24: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x40] *)
(*        292: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x40] *)
| 0x124 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299c29: MOVZX EAX,byte ptr [RDI + RAX*0x1 + 0x40] *)
(*        297: MOVZX EAX,byte ptr [RDI + RAX*0x1 + 0x40] *)
| 0x129 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299c2e: SUB EAX,ECX *)
(*        302: SUB EAX,ECX *)
| 0x12e => Some (2,
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

(* 0x00299c30: VZEROUPPER *)
(*        304: VZEROUPPER *)
| 0x130 => Some (3,
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

(* 0x00299c33: RET *)
(*        307: RET *)
| 0x133 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299c40: ADD RSI,RDI *)
(*        320: ADD RSI,RDI *)
| 0x140 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c43: VPMOVMSKB EAX,YMM1 *)
(*        323: VPMOVMSKB EAX,YMM1 *)
| 0x143 => Some (4,
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

(* 0x00299c47: INC EAX *)
(*        327: INC EAX *)
| 0x147 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c49: JNZ 0x00299be0 *)
(*        329: JNZ 0x00299be0 *)
| 0x149 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299c4b: VPMOVMSKB EAX,YMM2 *)
(*        331: VPMOVMSKB EAX,YMM2 *)
| 0x14b => Some (4,
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

(* 0x00299c4f: INC EAX *)
(*        335: INC EAX *)
| 0x14f => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c51: JNZ 0x00299c00 *)
(*        337: JNZ 0x00299c00 *)
| 0x151 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x100 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299c53: VPMOVMSKB EAX,YMM3 *)
(*        339: VPMOVMSKB EAX,YMM3 *)
| 0x153 => Some (4,
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

(* 0x00299c57: INC EAX *)
(*        343: INC EAX *)
| 0x157 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c59: JNZ 0x00299c20 *)
(*        345: JNZ 0x00299c20 *)
| 0x159 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x120 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299c5b: TZCNT ECX,ECX *)
(*        347: TZCNT ECX,ECX *)
| 0x15b => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Rep (Word 33 32) (
		Move (V_TEMP 0) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 32))) $;
		Move (V_TEMP 1) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 1)) (BinOp OP_OR ((BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 32))) (Word 0x80000000 32)))
	) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299c5f: MOVZX EAX,byte ptr [RDI + RCX*0x1 + 0x60] *)
(*        351: MOVZX EAX,byte ptr [RDI + RCX*0x1 + 0x60] *)
| 0x15f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299c64: MOVZX ECX,byte ptr [RSI + RCX*0x1 + 0x60] *)
(*        356: MOVZX ECX,byte ptr [RSI + RCX*0x1 + 0x60] *)
| 0x164 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299c69: SUB EAX,ECX *)
(*        361: SUB EAX,ECX *)
| 0x169 => Some (2,
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

(* 0x00299c6b: VZEROUPPER *)
(*        363: VZEROUPPER *)
| 0x16b => Some (3,
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

(* 0x00299c6e: RET *)
(*        366: RET *)
| 0x16e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299c70: LEA RDX,[RDI + RDX*0x1 + -0x80] *)
(*        368: LEA RDX,[RDI + RDX*0x1 + -0x80] *)
| 0x170 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDX (Var (V_TEMP 2))
)

(* 0x00299c75: SUB RSI,RDI *)
(*        373: SUB RSI,RDI *)
| 0x175 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c78: AND RDI,-0x20 *)
(*        376: AND RDI,-0x20 *)
| 0x178 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xffffffffffffffe0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299c7c: SUB RDI,-0x80 *)
(*        380: SUB RDI,-0x80 *)
| 0x17c => Some (4,
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

(* 0x00299c80: VMOVDQU YMM1,ymmword ptr [RSI + RDI*0x1] *)
(*        384: VMOVDQU YMM1,ymmword ptr [RSI + RDI*0x1] *)
| 0x180 => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299c85: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
(*        389: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI] *)
| 0x185 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299c89: VMOVDQU YMM2,ymmword ptr [RSI + RDI*0x1 + 0x20] *)
(*        393: VMOVDQU YMM2,ymmword ptr [RSI + RDI*0x1 + 0x20] *)
| 0x189 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299c8f: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
(*        399: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI + 0x20] *)
| 0x18f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299c94: VMOVDQU YMM3,ymmword ptr [RSI + RDI*0x1 + 0x40] *)
(*        404: VMOVDQU YMM3,ymmword ptr [RSI + RDI*0x1 + 0x40] *)
| 0x194 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299c9a: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
(*        410: VPCMPEQB YMM3,YMM3,ymmword ptr [RDI + 0x40] *)
| 0x19a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299c9f: VMOVDQU YMM4,ymmword ptr [RSI + RDI*0x1 + 0x60] *)
(*        415: VMOVDQU YMM4,ymmword ptr [RSI + RDI*0x1 + 0x60] *)
| 0x19f => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299ca5: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
(*        421: VPCMPEQB YMM4,YMM4,ymmword ptr [RDI + 0x60] *)
| 0x1a5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299caa: VPAND YMM5,YMM2,YMM1 *)
(*        426: VPAND YMM5,YMM2,YMM1 *)
| 0x1aa => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299cae: VPAND YMM6,YMM4,YMM3 *)
(*        430: VPAND YMM6,YMM4,YMM3 *)
| 0x1ae => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM4) (Var R_YMM3)) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299cb2: VPAND YMM7,YMM6,YMM5 *)
(*        434: VPAND YMM7,YMM6,YMM5 *)
| 0x1b2 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM6) (Var R_YMM5)) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299cb6: VPMOVMSKB ECX,YMM7 *)
(*        438: VPMOVMSKB ECX,YMM7 *)
| 0x1b6 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM7) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM7) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM7) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM7) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM7) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM7) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM7) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM7) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM7) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM7) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM7) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM7) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM7) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM7) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM7) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM7) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM7) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM7) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM7) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM7) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM7) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM7) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM7) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM7) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM7) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM7) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM7) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM7) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM7) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM7) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM7) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM7) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299cba: INC ECX *)
(*        442: INC ECX *)
| 0x1ba => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299cbc: JNZ 0x00299c40 *)
(*        444: JNZ 0x00299c40 *)
| 0x1bc => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x140 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299cbe: SUB RDI,-0x80 *)
(*        446: SUB RDI,-0x80 *)
| 0x1be => Some (4,
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

(* 0x00299cc2: CMP RDI,RDX *)
(*        450: CMP RDI,RDX *)
| 0x1c2 => Some (3,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299cc5: JC 0x00299c80 *)
(*        453: JC 0x00299c80 *)
| 0x1c5 => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x180 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299cc7: SUB RDI,RDX *)
(*        455: SUB RDI,RDX *)
| 0x1c7 => Some (3,
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

(* 0x00299cca: CMP EDI,0x60 *)
(*        458: CMP EDI,0x60 *)
| 0x1ca => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDI)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x60 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x60 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x60 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x60 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x60 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299ccd: JNC 0x00299d30 *)
(*        461: JNC 0x00299d30 *)
| 0x1cd => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x230 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299ccf: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + 0x40] *)
(*        463: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + 0x40] *)
| 0x1cf => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x40 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299cd5: CMP EDI,0x40 *)
(*        469: CMP EDI,0x40 *)
| 0x1d5 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDI)) $;
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

(* 0x00299cd8: JNC 0x00299d20 *)
(*        472: JNC 0x00299d20 *)
| 0x1d8 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x220 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299cda: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1] *)
(*        474: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1] *)
| 0x1da => Some (5,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (Load (Var V_MEM64) (Var (V_TEMP 1)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299cdf: VPCMPEQB YMM1,YMM1,ymmword ptr [RDX] *)
(*        479: VPCMPEQB YMM1,YMM1,ymmword ptr [RDX] *)
| 0x1df => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDX) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299ce3: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + 0x20] *)
(*        483: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + 0x20] *)
| 0x1e3 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x20 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299ce9: VPCMPEQB YMM2,YMM2,ymmword ptr [RDX + 0x20] *)
(*        489: VPCMPEQB YMM2,YMM2,ymmword ptr [RDX + 0x20] *)
| 0x1e9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299cee: VPCMPEQB YMM3,YMM3,ymmword ptr [RDX + 0x40] *)
(*        494: VPCMPEQB YMM3,YMM3,ymmword ptr [RDX + 0x40] *)
| 0x1ee => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299cf3: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + 0x60] *)
(*        499: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + 0x60] *)
| 0x1f3 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299cf9: VPCMPEQB YMM4,YMM4,ymmword ptr [RDX + 0x60] *)
(*        505: VPCMPEQB YMM4,YMM4,ymmword ptr [RDX + 0x60] *)
| 0x1f9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299cfe: VPAND YMM5,YMM2,YMM1 *)
(*        510: VPAND YMM5,YMM2,YMM1 *)
| 0x1fe => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM2) (Var R_YMM1)) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299d02: VPAND YMM6,YMM4,YMM3 *)
(*        514: VPAND YMM6,YMM4,YMM3 *)
| 0x202 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM4) (Var R_YMM3)) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299d06: VPAND YMM7,YMM6,YMM5 *)
(*        518: VPAND YMM7,YMM6,YMM5 *)
| 0x206 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_YMM6) (Var R_YMM5)) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299d0a: VPMOVMSKB ECX,YMM7 *)
(*        522: VPMOVMSKB ECX,YMM7 *)
| 0x20a => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM7) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM7) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM7) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM7) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM7) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM7) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM7) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM7) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM7) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM7) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM7) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM7) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM7) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM7) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM7) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM7) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM7) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM7) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM7) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM7) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM7) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM7) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM7) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM7) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM7) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM7) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM7) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM7) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM7) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM7) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM7) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM7) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299d0e: MOV RDI,RDX *)
(*        526: MOV RDI,RDX *)
| 0x20e => Some (3,
	Move R_RDI (Var R_RDX)
)

(* 0x00299d11: INC ECX *)
(*        529: INC ECX *)
| 0x211 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d13: JNZ 0x00299c40 *)
(*        531: JNZ 0x00299c40 *)
| 0x213 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x140 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299d19: VZEROUPPER *)
(*        537: VZEROUPPER *)
| 0x219 => Some (3,
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

(* 0x00299d1c: RET *)
(*        540: RET *)
| 0x21c => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299d20: VPCMPEQB YMM3,YMM3,ymmword ptr [RDX + 0x40] *)
(*        544: VPCMPEQB YMM3,YMM3,ymmword ptr [RDX + 0x40] *)
| 0x220 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM3)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM3)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM3)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM3)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM3)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM3)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM3)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM3)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM3)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM3)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM3)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM3)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM3)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM3)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM3)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM3)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299d25: VPMOVMSKB EAX,YMM3 *)
(*        549: VPMOVMSKB EAX,YMM3 *)
| 0x225 => Some (4,
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

(* 0x00299d29: INC EAX *)
(*        553: INC EAX *)
| 0x229 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d2b: JNZ 0x00299d80 *)
(*        555: JNZ 0x00299d80 *)
| 0x22b => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x280 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299d2d: NOP dword ptr [RAX] *)
(*        557: NOP dword ptr [RAX] *)
| 0x22d => Some (3,
	Nop
)

(* 0x00299d30: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + 0x60] *)
(*        560: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + 0x60] *)
| 0x230 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299d36: VPCMPEQB YMM4,YMM4,ymmword ptr [RDX + 0x60] *)
(*        566: VPCMPEQB YMM4,YMM4,ymmword ptr [RDX + 0x60] *)
| 0x236 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move (V_TEMP 2) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM4)) (Extract 255 248 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM4)) (Extract 247 240 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM4)) (Extract 239 232 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM4)) (Extract 231 224 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM4)) (Extract 223 216 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM4)) (Extract 215 208 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM4)) (Extract 207 200 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM4)) (Extract 199 192 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM4)) (Extract 191 184 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM4)) (Extract 183 176 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM4)) (Extract 175 168 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM4)) (Extract 167 160 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM4)) (Extract 159 152 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM4)) (Extract 151 144 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM4)) (Extract 143 136 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM4)) (Extract 135 128 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var (V_TEMP 1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var (V_TEMP 1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var (V_TEMP 1))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 2))))
)

(* 0x00299d3b: VPMOVMSKB EAX,YMM4 *)
(*        571: VPMOVMSKB EAX,YMM4 *)
| 0x23b => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var R_YMM4) (Word 7 256)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffd 32)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Var R_YMM4) (Word 15 256)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffb 32)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Var R_YMM4) (Word 23 256)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffff7 32)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Var R_YMM4) (Word 31 256)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffef 32)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Var R_YMM4) (Word 39 256)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffdf 32)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Var R_YMM4) (Word 47 256)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffffbf 32)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Var R_YMM4) (Word 55 256)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffff7f 32)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Var R_YMM4) (Word 63 256)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffeff 32)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Var R_YMM4) (Word 71 256)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffdff 32)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Var R_YMM4) (Word 79 256)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffbff 32)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Var R_YMM4) (Word 87 256)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffff7ff 32)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Var R_YMM4) (Word 95 256)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffefff 32)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Var R_YMM4) (Word 103 256)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffdfff 32)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Var R_YMM4) (Word 111 256)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffffbfff 32)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Var R_YMM4) (Word 119 256)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff7fff 32)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Var R_YMM4) (Word 127 256)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move (V_TEMP 96) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffeffff 32)) $;
	Move (V_TEMP 97) (BinOp OP_RSHIFT (Var R_YMM4) (Word 135 256)) $;
	Move (V_TEMP 98) (Extract 7 0 (Var (V_TEMP 97))) $;
	Move (V_TEMP 99) (BinOp OP_AND (Var (V_TEMP 98)) (Word 0x1 8)) $;
	Move (V_TEMP 100) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 99))) $;
	Move (V_TEMP 101) (BinOp OP_LSHIFT (Var (V_TEMP 100)) (Word 16 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 96)) (Var (V_TEMP 101))) $;
	Move (V_TEMP 102) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffdffff 32)) $;
	Move (V_TEMP 103) (BinOp OP_RSHIFT (Var R_YMM4) (Word 143 256)) $;
	Move (V_TEMP 104) (Extract 7 0 (Var (V_TEMP 103))) $;
	Move (V_TEMP 105) (BinOp OP_AND (Var (V_TEMP 104)) (Word 0x1 8)) $;
	Move (V_TEMP 106) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 105))) $;
	Move (V_TEMP 107) (BinOp OP_LSHIFT (Var (V_TEMP 106)) (Word 17 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 102)) (Var (V_TEMP 107))) $;
	Move (V_TEMP 108) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffbffff 32)) $;
	Move (V_TEMP 109) (BinOp OP_RSHIFT (Var R_YMM4) (Word 151 256)) $;
	Move (V_TEMP 110) (Extract 7 0 (Var (V_TEMP 109))) $;
	Move (V_TEMP 111) (BinOp OP_AND (Var (V_TEMP 110)) (Word 0x1 8)) $;
	Move (V_TEMP 112) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 111))) $;
	Move (V_TEMP 113) (BinOp OP_LSHIFT (Var (V_TEMP 112)) (Word 18 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 108)) (Var (V_TEMP 113))) $;
	Move (V_TEMP 114) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7ffff 32)) $;
	Move (V_TEMP 115) (BinOp OP_RSHIFT (Var R_YMM4) (Word 159 256)) $;
	Move (V_TEMP 116) (Extract 7 0 (Var (V_TEMP 115))) $;
	Move (V_TEMP 117) (BinOp OP_AND (Var (V_TEMP 116)) (Word 0x1 8)) $;
	Move (V_TEMP 118) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 117))) $;
	Move (V_TEMP 119) (BinOp OP_LSHIFT (Var (V_TEMP 118)) (Word 19 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 114)) (Var (V_TEMP 119))) $;
	Move (V_TEMP 120) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffefffff 32)) $;
	Move (V_TEMP 121) (BinOp OP_RSHIFT (Var R_YMM4) (Word 167 256)) $;
	Move (V_TEMP 122) (Extract 7 0 (Var (V_TEMP 121))) $;
	Move (V_TEMP 123) (BinOp OP_AND (Var (V_TEMP 122)) (Word 0x1 8)) $;
	Move (V_TEMP 124) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 123))) $;
	Move (V_TEMP 125) (BinOp OP_LSHIFT (Var (V_TEMP 124)) (Word 20 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 120)) (Var (V_TEMP 125))) $;
	Move (V_TEMP 126) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdfffff 32)) $;
	Move (V_TEMP 127) (BinOp OP_RSHIFT (Var R_YMM4) (Word 175 256)) $;
	Move (V_TEMP 128) (Extract 7 0 (Var (V_TEMP 127))) $;
	Move (V_TEMP 129) (BinOp OP_AND (Var (V_TEMP 128)) (Word 0x1 8)) $;
	Move (V_TEMP 130) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 129))) $;
	Move (V_TEMP 131) (BinOp OP_LSHIFT (Var (V_TEMP 130)) (Word 21 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 126)) (Var (V_TEMP 131))) $;
	Move (V_TEMP 132) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbfffff 32)) $;
	Move (V_TEMP 133) (BinOp OP_RSHIFT (Var R_YMM4) (Word 183 256)) $;
	Move (V_TEMP 134) (Extract 7 0 (Var (V_TEMP 133))) $;
	Move (V_TEMP 135) (BinOp OP_AND (Var (V_TEMP 134)) (Word 0x1 8)) $;
	Move (V_TEMP 136) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 135))) $;
	Move (V_TEMP 137) (BinOp OP_LSHIFT (Var (V_TEMP 136)) (Word 22 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 132)) (Var (V_TEMP 137))) $;
	Move (V_TEMP 138) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7fffff 32)) $;
	Move (V_TEMP 139) (BinOp OP_RSHIFT (Var R_YMM4) (Word 191 256)) $;
	Move (V_TEMP 140) (Extract 7 0 (Var (V_TEMP 139))) $;
	Move (V_TEMP 141) (BinOp OP_AND (Var (V_TEMP 140)) (Word 0x1 8)) $;
	Move (V_TEMP 142) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 141))) $;
	Move (V_TEMP 143) (BinOp OP_LSHIFT (Var (V_TEMP 142)) (Word 23 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 138)) (Var (V_TEMP 143))) $;
	Move (V_TEMP 144) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeffffff 32)) $;
	Move (V_TEMP 145) (BinOp OP_RSHIFT (Var R_YMM4) (Word 199 256)) $;
	Move (V_TEMP 146) (Extract 7 0 (Var (V_TEMP 145))) $;
	Move (V_TEMP 147) (BinOp OP_AND (Var (V_TEMP 146)) (Word 0x1 8)) $;
	Move (V_TEMP 148) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 147))) $;
	Move (V_TEMP 149) (BinOp OP_LSHIFT (Var (V_TEMP 148)) (Word 24 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 144)) (Var (V_TEMP 149))) $;
	Move (V_TEMP 150) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdffffff 32)) $;
	Move (V_TEMP 151) (BinOp OP_RSHIFT (Var R_YMM4) (Word 207 256)) $;
	Move (V_TEMP 152) (Extract 7 0 (Var (V_TEMP 151))) $;
	Move (V_TEMP 153) (BinOp OP_AND (Var (V_TEMP 152)) (Word 0x1 8)) $;
	Move (V_TEMP 154) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 153))) $;
	Move (V_TEMP 155) (BinOp OP_LSHIFT (Var (V_TEMP 154)) (Word 25 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 150)) (Var (V_TEMP 155))) $;
	Move (V_TEMP 156) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbffffff 32)) $;
	Move (V_TEMP 157) (BinOp OP_RSHIFT (Var R_YMM4) (Word 215 256)) $;
	Move (V_TEMP 158) (Extract 7 0 (Var (V_TEMP 157))) $;
	Move (V_TEMP 159) (BinOp OP_AND (Var (V_TEMP 158)) (Word 0x1 8)) $;
	Move (V_TEMP 160) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 159))) $;
	Move (V_TEMP 161) (BinOp OP_LSHIFT (Var (V_TEMP 160)) (Word 26 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 156)) (Var (V_TEMP 161))) $;
	Move (V_TEMP 162) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ffffff 32)) $;
	Move (V_TEMP 163) (BinOp OP_RSHIFT (Var R_YMM4) (Word 223 256)) $;
	Move (V_TEMP 164) (Extract 7 0 (Var (V_TEMP 163))) $;
	Move (V_TEMP 165) (BinOp OP_AND (Var (V_TEMP 164)) (Word 0x1 8)) $;
	Move (V_TEMP 166) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 165))) $;
	Move (V_TEMP 167) (BinOp OP_LSHIFT (Var (V_TEMP 166)) (Word 27 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 162)) (Var (V_TEMP 167))) $;
	Move (V_TEMP 168) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefffffff 32)) $;
	Move (V_TEMP 169) (BinOp OP_RSHIFT (Var R_YMM4) (Word 231 256)) $;
	Move (V_TEMP 170) (Extract 7 0 (Var (V_TEMP 169))) $;
	Move (V_TEMP 171) (BinOp OP_AND (Var (V_TEMP 170)) (Word 0x1 8)) $;
	Move (V_TEMP 172) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 171))) $;
	Move (V_TEMP 173) (BinOp OP_LSHIFT (Var (V_TEMP 172)) (Word 28 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 168)) (Var (V_TEMP 173))) $;
	Move (V_TEMP 174) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfffffff 32)) $;
	Move (V_TEMP 175) (BinOp OP_RSHIFT (Var R_YMM4) (Word 239 256)) $;
	Move (V_TEMP 176) (Extract 7 0 (Var (V_TEMP 175))) $;
	Move (V_TEMP 177) (BinOp OP_AND (Var (V_TEMP 176)) (Word 0x1 8)) $;
	Move (V_TEMP 178) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 177))) $;
	Move (V_TEMP 179) (BinOp OP_LSHIFT (Var (V_TEMP 178)) (Word 29 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 174)) (Var (V_TEMP 179))) $;
	Move (V_TEMP 180) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfffffff 32)) $;
	Move (V_TEMP 181) (BinOp OP_RSHIFT (Var R_YMM4) (Word 247 256)) $;
	Move (V_TEMP 182) (Extract 7 0 (Var (V_TEMP 181))) $;
	Move (V_TEMP 183) (BinOp OP_AND (Var (V_TEMP 182)) (Word 0x1 8)) $;
	Move (V_TEMP 184) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 183))) $;
	Move (V_TEMP 185) (BinOp OP_LSHIFT (Var (V_TEMP 184)) (Word 30 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 180)) (Var (V_TEMP 185))) $;
	Move (V_TEMP 186) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fffffff 32)) $;
	Move (V_TEMP 187) (BinOp OP_RSHIFT (Var R_YMM4) (Word 255 256)) $;
	Move (V_TEMP 188) (Extract 7 0 (Var (V_TEMP 187))) $;
	Move (V_TEMP 189) (BinOp OP_AND (Var (V_TEMP 188)) (Word 0x1 8)) $;
	Move (V_TEMP 190) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 189))) $;
	Move (V_TEMP 191) (BinOp OP_LSHIFT (Var (V_TEMP 190)) (Word 31 32)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 186)) (Var (V_TEMP 191))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299d3f: INC EAX *)
(*        575: INC EAX *)
| 0x23f => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d41: JNZ 0x00299d84 *)
(*        577: JNZ 0x00299d84 *)
| 0x241 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x284 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299d43: VZEROUPPER *)
(*        579: VZEROUPPER *)
| 0x243 => Some (3,
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

(* 0x00299d46: RET *)
(*        582: RET *)
| 0x246 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299d50: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*        592: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x250 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299d56: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI + RDX*0x1 + -0x40] *)
(*        598: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI + RDX*0x1 + -0x40] *)
| 0x256 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move (V_TEMP 4) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 3))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 3))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 4))))
)

(* 0x00299d5c: VPMOVMSKB EAX,YMM1 *)
(*        604: VPMOVMSKB EAX,YMM1 *)
| 0x25c => Some (4,
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

(* 0x00299d60: INC EAX *)
(*        608: INC EAX *)
| 0x260 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d62: JNZ 0x00299da0 *)
(*        610: JNZ 0x00299da0 *)
| 0x262 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x2a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299d64: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*        612: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x264 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299d6a: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI + RDX*0x1 + -0x20] *)
(*        618: VPCMPEQB YMM1,YMM1,ymmword ptr [RDI + RDX*0x1 + -0x20] *)
| 0x26a => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move (V_TEMP 4) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM1)) (Extract 255 248 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM1)) (Extract 247 240 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM1)) (Extract 239 232 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM1)) (Extract 231 224 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM1)) (Extract 223 216 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM1)) (Extract 215 208 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM1)) (Extract 207 200 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM1)) (Extract 199 192 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM1)) (Extract 191 184 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM1)) (Extract 183 176 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM1)) (Extract 175 168 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM1)) (Extract 167 160 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM1)) (Extract 159 152 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM1)) (Extract 151 144 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM1)) (Extract 143 136 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM1)) (Extract 135 128 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Extract 127 120 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Extract 119 112 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Extract 111 104 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Extract 103 96 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Extract 95 88 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Extract 87 80 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Extract 79 72 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Extract 71 64 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Extract 63 56 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Extract 55 48 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Extract 47 40 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Extract 39 32 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Extract 31 24 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Extract 23 16 (Var (V_TEMP 3))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Extract 15 8 (Var (V_TEMP 3))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var (V_TEMP 3))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 4))))
)

(* 0x00299d70: VPMOVMSKB EAX,YMM1 *)
(*        624: VPMOVMSKB EAX,YMM1 *)
| 0x270 => Some (4,
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

(* 0x00299d74: INC EAX *)
(*        628: INC EAX *)
| 0x274 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d76: JNZ 0x00299dc0 *)
(*        630: JNZ 0x00299dc0 *)
| 0x276 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x2c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299d78: VZEROUPPER *)
(*        632: VZEROUPPER *)
| 0x278 => Some (3,
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

(* 0x00299d7b: RET *)
(*        635: RET *)
| 0x27b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299d80: SUB RDX,0x20 *)
(*        640: SUB RDX,0x20 *)
| 0x280 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x20 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x20 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x20 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x20 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d84: TZCNT EAX,EAX *)
(*        644: TZCNT EAX,EAX *)
| 0x284 => Some (4,
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

(* 0x00299d88: ADD RAX,RDX *)
(*        648: ADD RAX,RDX *)
| 0x288 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299d8b: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x60] *)
(*        651: MOVZX ECX,byte ptr [RSI + RAX*0x1 + 0x60] *)
| 0x28b => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x60 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299d90: MOVZX EAX,byte ptr [RAX + 0x60] *)
(*        656: MOVZX EAX,byte ptr [RAX + 0x60] *)
| 0x290 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RAX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 1)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299d94: SUB EAX,ECX *)
(*        660: SUB EAX,ECX *)
| 0x294 => Some (2,
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

(* 0x00299d96: VZEROUPPER *)
(*        662: VZEROUPPER *)
| 0x296 => Some (3,
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

(* 0x00299d99: RET *)
(*        665: RET *)
| 0x299 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299da0: TZCNT EAX,EAX *)
(*        672: TZCNT EAX,EAX *)
| 0x2a0 => Some (4,
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

(* 0x00299da4: ADD EAX,EDX *)
(*        676: ADD EAX,EDX *)
| 0x2a4 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299da6: MOVZX ECX,byte ptr [RSI + RAX*0x1 + -0x40] *)
(*        678: MOVZX ECX,byte ptr [RSI + RAX*0x1 + -0x40] *)
| 0x2a6 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299dab: MOVZX EAX,byte ptr [RDI + RAX*0x1 + -0x40] *)
(*        683: MOVZX EAX,byte ptr [RDI + RAX*0x1 + -0x40] *)
| 0x2ab => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299db0: SUB EAX,ECX *)
(*        688: SUB EAX,ECX *)
| 0x2b0 => Some (2,
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

(* 0x00299db2: VZEROUPPER *)
(*        690: VZEROUPPER *)
| 0x2b2 => Some (3,
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

(* 0x00299db5: RET *)
(*        693: RET *)
| 0x2b5 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299dc0: TZCNT EAX,EAX *)
(*        704: TZCNT EAX,EAX *)
| 0x2c0 => Some (4,
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

(* 0x00299dc4: ADD EAX,EDX *)
(*        708: ADD EAX,EDX *)
| 0x2c4 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299dc6: MOVZX ECX,byte ptr [RSI + RAX*0x1 + -0x20] *)
(*        710: MOVZX ECX,byte ptr [RSI + RAX*0x1 + -0x20] *)
| 0x2c6 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299dcb: MOVZX EAX,byte ptr [RDI + RAX*0x1 + -0x20] *)
(*        715: MOVZX EAX,byte ptr [RDI + RAX*0x1 + -0x20] *)
| 0x2cb => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299dd0: SUB EAX,ECX *)
(*        720: SUB EAX,ECX *)
| 0x2d0 => Some (2,
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

(* 0x00299dd2: VZEROUPPER *)
(*        722: VZEROUPPER *)
| 0x2d2 => Some (3,
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

(* 0x00299dd5: RET *)
(*        725: RET *)
| 0x2d5 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299de0: CMP EDX,0x1 *)
(*        736: CMP EDX,0x1 *)
| 0x2e0 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299de3: JBE 0x00299e60 *)
(*        739: JBE 0x00299e60 *)
| 0x2e3 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x360 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299de5: MOV EAX,EDI *)
(*        741: MOV EAX,EDI *)
| 0x2e5 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299de7: OR EAX,ESI *)
(*        743: OR EAX,ESI *)
| 0x2e7 => Some (2,
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

(* 0x00299de9: AND EAX,0xfff *)
(*        745: AND EAX,0xfff *)
| 0x2e9 => Some (5,
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

(* 0x00299dee: CMP EAX,0xfe0 *)
(*        750: CMP EAX,0xfe0 *)
| 0x2ee => Some (5,
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

(* 0x00299df3: JG 0x00299e20 *)
(*        755: JG 0x00299e20 *)
| 0x2f3 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 2))) (
		Jmp (Word 0x320 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299df5: VMOVDQU YMM2,ymmword ptr [RSI] *)
(*        757: VMOVDQU YMM2,ymmword ptr [RSI] *)
| 0x2f5 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299df9: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI] *)
(*        761: VPCMPEQB YMM2,YMM2,ymmword ptr [RDI] *)
| 0x2f9 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 32) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 255 248 (Var R_YMM2)) (Extract 255 248 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 247 240 (Var R_YMM2)) (Extract 247 240 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 239 232 (Var R_YMM2)) (Extract 239 232 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 231 224 (Var R_YMM2)) (Extract 231 224 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 223 216 (Var R_YMM2)) (Extract 223 216 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 215 208 (Var R_YMM2)) (Extract 215 208 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 207 200 (Var R_YMM2)) (Extract 207 200 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 199 192 (Var R_YMM2)) (Extract 199 192 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 191 184 (Var R_YMM2)) (Extract 191 184 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 183 176 (Var R_YMM2)) (Extract 183 176 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 175 168 (Var R_YMM2)) (Extract 175 168 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 167 160 (Var R_YMM2)) (Extract 167 160 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 159 152 (Var R_YMM2)) (Extract 159 152 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 151 144 (Var R_YMM2)) (Extract 151 144 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 143 136 (Var R_YMM2)) (Extract 143 136 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 135 128 (Var R_YMM2)) (Extract 135 128 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299dfd: VPMOVMSKB EAX,YMM2 *)
(*        765: VPMOVMSKB EAX,YMM2 *)
| 0x2fd => Some (4,
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

(* 0x00299e01: INC EAX *)
(*        769: INC EAX *)
| 0x301 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299e03: BZHI EDX,EAX,EDX *)
(*        771: BZHI EDX,EAX,EDX *)
| 0x303 => Some (5,
	Move (V_TEMP 0) (Extract 7 0 (Var R_RDX)) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Word 0x20 8))) $;
	Move (V_TEMP 2) (BinOp OP_MINUS (Word 0x20 8) (Var (V_TEMP 0))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Var (V_TEMP 1)) (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Extract 31 0 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_RSHIFT (Var (V_TEMP 4)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3))))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Word 0x1f 8) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8))
)

(* 0x00299e08: JNZ 0x00299be0 *)
(*        776: JNZ 0x00299be0 *)
| 0x308 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e0e: XOR EAX,EAX *)
(*        782: XOR EAX,EAX *)
| 0x30e => Some (2,
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

(* 0x00299e10: VZEROUPPER *)
(*        784: VZEROUPPER *)
| 0x310 => Some (3,
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

(* 0x00299e13: RET *)
(*        787: RET *)
| 0x313 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299e20: CMP EDX,0x10 *)
(*        800: CMP EDX,0x10 *)
| 0x320 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x10 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299e23: JNC 0x00299ed0 *)
(*        803: JNC 0x00299ed0 *)
| 0x323 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x3d0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e29: CMP EDX,0x8 *)
(*        809: CMP EDX,0x8 *)
| 0x329 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x8 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299e2c: JNC 0x00299e70 *)
(*        812: JNC 0x00299e70 *)
| 0x32c => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x370 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e2e: CMP EDX,0x4 *)
(*        814: CMP EDX,0x4 *)
| 0x32e => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x4 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x00299e31: JNC 0x00299f10 *)
(*        817: JNC 0x00299f10 *)
| 0x331 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x410 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e37: MOVZX EAX,word ptr [RDI] *)
(*        823: MOVZX EAX,word ptr [RDI] *)
| 0x337 => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299e3a: MOVZX ECX,word ptr [RSI] *)
(*        826: MOVZX ECX,word ptr [RSI] *)
| 0x33a => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 2) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299e3d: SHL EAX,0x8 *)
(*        829: SHL EAX,0x8 *)
| 0x33d => Some (3,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x8 32) (Word 0x1f 32)) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_LSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 32))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00299e40: SHL ECX,0x8 *)
(*        832: SHL ECX,0x8 *)
| 0x340 => Some (3,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x8 32) (Word 0x1f 32)) $;
	Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_LSHIFT (Extract 31 0 (Var R_RCX)) (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 32))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00299e43: BSWAP EAX *)
(*        835: BSWAP EAX *)
| 0x343 => Some (2,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff000000 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 24 32)) $;
	Move (V_TEMP 2) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff0000 32)) $;
	Move (V_TEMP 3) (BinOp OP_RSHIFT (Var (V_TEMP 2)) (Word 8 32)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff00 32)) $;
	Move (V_TEMP 5) (BinOp OP_LSHIFT (Var (V_TEMP 4)) (Word 8 32)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 7) (BinOp OP_LSHIFT (Var (V_TEMP 6)) (Word 24 32)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 7)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299e45: BSWAP ECX *)
(*        837: BSWAP ECX *)
| 0x345 => Some (2,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff000000 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 24 32)) $;
	Move (V_TEMP 2) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff0000 32)) $;
	Move (V_TEMP 3) (BinOp OP_RSHIFT (Var (V_TEMP 2)) (Word 8 32)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff00 32)) $;
	Move (V_TEMP 5) (BinOp OP_LSHIFT (Var (V_TEMP 4)) (Word 8 32)) $;
	Move (V_TEMP 1) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 7) (BinOp OP_LSHIFT (Var (V_TEMP 6)) (Word 24 32)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 7)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299e47: MOVZX EDI,byte ptr [RDI + RDX*0x1 + -0x1] *)
(*        839: MOVZX EDI,byte ptr [RDI + RDX*0x1 + -0x1] *)
| 0x347 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffff 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x00299e4c: MOVZX ESI,byte ptr [RSI + RDX*0x1 + -0x1] *)
(*        844: MOVZX ESI,byte ptr [RSI + RDX*0x1 + -0x1] *)
| 0x34c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffff 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 1) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00299e51: OR EAX,EDI *)
(*        849: OR EAX,EDI *)
| 0x351 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299e53: OR ECX,ESI *)
(*        851: OR ECX,ESI *)
| 0x353 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_OR (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RSI)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299e55: SUB EAX,ECX *)
(*        853: SUB EAX,ECX *)
| 0x355 => Some (2,
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

(* 0x00299e57: RET *)
(*        855: RET *)
| 0x357 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299e60: JC 0x00299ec0 *)
(*        864: JC 0x00299ec0 *)
| 0x360 => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x3c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e62: MOVZX ECX,byte ptr [RSI] *)
(*        866: MOVZX ECX,byte ptr [RSI] *)
| 0x362 => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00299e65: MOVZX EAX,byte ptr [RDI] *)
(*        869: MOVZX EAX,byte ptr [RDI] *)
| 0x365 => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 1) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299e68: SUB EAX,ECX *)
(*        872: SUB EAX,ECX *)
| 0x368 => Some (2,
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

(* 0x00299e6a: RET *)
(*        874: RET *)
| 0x36a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299e70: VMOVQ XMM1,qword ptr [RDI] *)
(*        880: VMOVQ XMM1,qword ptr [RDI] *)
| 0x370 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 0))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299e74: VMOVQ XMM2,qword ptr [RSI] *)
(*        884: VMOVQ XMM2,qword ptr [RSI] *)
| 0x374 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 0))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299e78: VPCMPEQB XMM2,XMM2,XMM1 *)
(*        888: VPCMPEQB XMM2,XMM2,XMM1 *)
| 0x378 => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM2))) (Extract 127 120 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM2))) (Extract 119 112 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM2))) (Extract 111 104 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM2))) (Extract 103 96 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM2))) (Extract 95 88 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM2))) (Extract 87 80 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM2))) (Extract 79 72 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM2))) (Extract 71 64 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM2))) (Extract 63 56 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM2))) (Extract 55 48 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM2))) (Extract 47 40 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM2))) (Extract 39 32 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM2))) (Extract 31 24 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM2))) (Extract 23 16 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM2))) (Extract 15 8 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM2))) (Extract 7 0 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299e7c: VPMOVMSKB EAX,XMM2 *)
(*        892: VPMOVMSKB EAX,XMM2 *)
| 0x37c => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299e80: SUB EAX,0xffff *)
(*        896: SUB EAX,0xffff *)
| 0x380 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299e85: JNZ 0x00299be0 *)
(*        901: JNZ 0x00299be0 *)
| 0x385 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299e8b: LEA RDI,[RDI + RDX*0x1 + -0x8] *)
(*        907: LEA RDI,[RDI + RDX*0x1 + -0x8] *)
| 0x38b => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDI (Var (V_TEMP 2))
)

(* 0x00299e90: LEA RSI,[RSI + RDX*0x1 + -0x8] *)
(*        912: LEA RSI,[RSI + RDX*0x1 + -0x8] *)
| 0x390 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RSI (Var (V_TEMP 2))
)

(* 0x00299e95: VMOVQ XMM1,qword ptr [RDI] *)
(*        917: VMOVQ XMM1,qword ptr [RDI] *)
| 0x395 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 0))) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299e99: VMOVQ XMM2,qword ptr [RSI] *)
(*        921: VMOVQ XMM2,qword ptr [RSI] *)
| 0x399 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move (V_TEMP 1) (Cast CAST_UNSIGNED 128 (Var (V_TEMP 0))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299e9d: VPCMPEQB XMM2,XMM2,XMM1 *)
(*        925: VPCMPEQB XMM2,XMM2,XMM1 *)
| 0x39d => Some (4,
	Move (V_TEMP 0) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM2))) (Extract 127 120 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM2))) (Extract 119 112 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM2))) (Extract 111 104 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM2))) (Extract 103 96 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM2))) (Extract 95 88 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM2))) (Extract 87 80 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM2))) (Extract 79 72 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM2))) (Extract 71 64 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM2))) (Extract 63 56 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM2))) (Extract 55 48 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM2))) (Extract 47 40 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM2))) (Extract 39 32 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM2))) (Extract 31 24 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM2))) (Extract 23 16 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM2))) (Extract 15 8 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM2))) (Extract 7 0 (Extract 127 0 (Var R_YMM1))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299ea1: VPMOVMSKB EAX,XMM2 *)
(*        929: VPMOVMSKB EAX,XMM2 *)
| 0x3a1 => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299ea5: SUB EAX,0xffff *)
(*        933: SUB EAX,0xffff *)
| 0x3a5 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299eaa: JNZ 0x00299be0 *)
(*        938: JNZ 0x00299be0 *)
| 0x3aa => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299eb0: RET *)
(*        944: RET *)
| 0x3b0 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299ec0: XOR EAX,EAX *)
(*        960: XOR EAX,EAX *)
| 0x3c0 => Some (2,
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

(* 0x00299ec2: RET *)
(*        962: RET *)
| 0x3c2 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299ed0: VMOVDQU XMM2,xmmword ptr [RSI] *)
(*        976: VMOVDQU XMM2,xmmword ptr [RSI] *)
| 0x3d0 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x00299ed4: VPCMPEQB XMM2,XMM2,xmmword ptr [RDI] *)
(*        980: VPCMPEQB XMM2,XMM2,xmmword ptr [RDI] *)
| 0x3d4 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM2))) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM2))) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM2))) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM2))) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM2))) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM2))) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM2))) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM2))) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM2))) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM2))) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM2))) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM2))) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM2))) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM2))) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM2))) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM2))) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299ed8: VPMOVMSKB EAX,XMM2 *)
(*        984: VPMOVMSKB EAX,XMM2 *)
| 0x3d8 => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299edc: SUB EAX,0xffff *)
(*        988: SUB EAX,0xffff *)
| 0x3dc => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299ee1: JNZ 0x00299be0 *)
(*        993: JNZ 0x00299be0 *)
| 0x3e1 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299ee7: VMOVDQU XMM2,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*        999: VMOVDQU XMM2,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x3e7 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 16) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x00299eed: LEA RDI,[RDI + RDX*0x1 + -0x10] *)
(*       1005: LEA RDI,[RDI + RDX*0x1 + -0x10] *)
| 0x3ed => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDI (Var (V_TEMP 2))
)

(* 0x00299ef2: LEA RSI,[RSI + RDX*0x1 + -0x10] *)
(*       1010: LEA RSI,[RSI + RDX*0x1 + -0x10] *)
| 0x3f2 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RSI (Var (V_TEMP 2))
)

(* 0x00299ef7: VPCMPEQB XMM2,XMM2,xmmword ptr [RDI] *)
(*       1015: VPCMPEQB XMM2,XMM2,xmmword ptr [RDI] *)
| 0x3f7 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move (V_TEMP 1) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Extract 127 0 (Var R_YMM2))) (Extract 127 120 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Extract 127 0 (Var R_YMM2))) (Extract 119 112 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Extract 127 0 (Var R_YMM2))) (Extract 111 104 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Extract 127 0 (Var R_YMM2))) (Extract 103 96 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Extract 127 0 (Var R_YMM2))) (Extract 95 88 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Extract 127 0 (Var R_YMM2))) (Extract 87 80 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Extract 127 0 (Var R_YMM2))) (Extract 79 72 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Extract 127 0 (Var R_YMM2))) (Extract 71 64 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Extract 127 0 (Var R_YMM2))) (Extract 63 56 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Extract 127 0 (Var R_YMM2))) (Extract 55 48 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Extract 127 0 (Var R_YMM2))) (Extract 47 40 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Extract 127 0 (Var R_YMM2))) (Extract 39 32 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Extract 127 0 (Var R_YMM2))) (Extract 31 24 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Extract 127 0 (Var R_YMM2))) (Extract 23 16 (Var (V_TEMP 0))))) (Word 0xff 8)) (Concat (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Extract 127 0 (Var R_YMM2))) (Extract 15 8 (Var (V_TEMP 0))))) (Word 0xff 8)) (BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Extract 127 0 (Var R_YMM2))) (Extract 7 0 (Var (V_TEMP 0))))) (Word 0xff 8))))))))))))))))) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x00299efb: VPMOVMSKB EAX,XMM2 *)
(*       1019: VPMOVMSKB EAX,XMM2 *)
| 0x3fb => Some (4,
	Move (V_TEMP 0) (Word 0x0 16) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffe 16)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 4))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffd 16)) $;
	Move (V_TEMP 7) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 8) (Extract 7 0 (Var (V_TEMP 7))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 8)) (Word 0x1 8)) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 9))) $;
	Move (V_TEMP 11) (BinOp OP_LSHIFT (Var (V_TEMP 10)) (Word 1 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 11))) $;
	Move (V_TEMP 12) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffb 16)) $;
	Move (V_TEMP 13) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 14) (Extract 7 0 (Var (V_TEMP 13))) $;
	Move (V_TEMP 15) (BinOp OP_AND (Var (V_TEMP 14)) (Word 0x1 8)) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 15))) $;
	Move (V_TEMP 17) (BinOp OP_LSHIFT (Var (V_TEMP 16)) (Word 2 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 12)) (Var (V_TEMP 17))) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfff7 16)) $;
	Move (V_TEMP 19) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 20) (Extract 7 0 (Var (V_TEMP 19))) $;
	Move (V_TEMP 21) (BinOp OP_AND (Var (V_TEMP 20)) (Word 0x1 8)) $;
	Move (V_TEMP 22) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 21))) $;
	Move (V_TEMP 23) (BinOp OP_LSHIFT (Var (V_TEMP 22)) (Word 3 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 23))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffef 16)) $;
	Move (V_TEMP 25) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 26) (Extract 7 0 (Var (V_TEMP 25))) $;
	Move (V_TEMP 27) (BinOp OP_AND (Var (V_TEMP 26)) (Word 0x1 8)) $;
	Move (V_TEMP 28) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 27))) $;
	Move (V_TEMP 29) (BinOp OP_LSHIFT (Var (V_TEMP 28)) (Word 4 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 24)) (Var (V_TEMP 29))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffdf 16)) $;
	Move (V_TEMP 31) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 32) (Extract 7 0 (Var (V_TEMP 31))) $;
	Move (V_TEMP 33) (BinOp OP_AND (Var (V_TEMP 32)) (Word 0x1 8)) $;
	Move (V_TEMP 34) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 33))) $;
	Move (V_TEMP 35) (BinOp OP_LSHIFT (Var (V_TEMP 34)) (Word 5 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 30)) (Var (V_TEMP 35))) $;
	Move (V_TEMP 36) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffbf 16)) $;
	Move (V_TEMP 37) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 38) (Extract 7 0 (Var (V_TEMP 37))) $;
	Move (V_TEMP 39) (BinOp OP_AND (Var (V_TEMP 38)) (Word 0x1 8)) $;
	Move (V_TEMP 40) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 39))) $;
	Move (V_TEMP 41) (BinOp OP_LSHIFT (Var (V_TEMP 40)) (Word 6 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 36)) (Var (V_TEMP 41))) $;
	Move (V_TEMP 42) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff7f 16)) $;
	Move (V_TEMP 43) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 44) (Extract 7 0 (Var (V_TEMP 43))) $;
	Move (V_TEMP 45) (BinOp OP_AND (Var (V_TEMP 44)) (Word 0x1 8)) $;
	Move (V_TEMP 46) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 45))) $;
	Move (V_TEMP 47) (BinOp OP_LSHIFT (Var (V_TEMP 46)) (Word 7 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 42)) (Var (V_TEMP 47))) $;
	Move (V_TEMP 48) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfeff 16)) $;
	Move (V_TEMP 49) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 50) (Extract 7 0 (Var (V_TEMP 49))) $;
	Move (V_TEMP 51) (BinOp OP_AND (Var (V_TEMP 50)) (Word 0x1 8)) $;
	Move (V_TEMP 52) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 51))) $;
	Move (V_TEMP 53) (BinOp OP_LSHIFT (Var (V_TEMP 52)) (Word 8 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 48)) (Var (V_TEMP 53))) $;
	Move (V_TEMP 54) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfdff 16)) $;
	Move (V_TEMP 55) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 56) (Extract 7 0 (Var (V_TEMP 55))) $;
	Move (V_TEMP 57) (BinOp OP_AND (Var (V_TEMP 56)) (Word 0x1 8)) $;
	Move (V_TEMP 58) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 57))) $;
	Move (V_TEMP 59) (BinOp OP_LSHIFT (Var (V_TEMP 58)) (Word 9 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 54)) (Var (V_TEMP 59))) $;
	Move (V_TEMP 60) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfbff 16)) $;
	Move (V_TEMP 61) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 62) (Extract 7 0 (Var (V_TEMP 61))) $;
	Move (V_TEMP 63) (BinOp OP_AND (Var (V_TEMP 62)) (Word 0x1 8)) $;
	Move (V_TEMP 64) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 63))) $;
	Move (V_TEMP 65) (BinOp OP_LSHIFT (Var (V_TEMP 64)) (Word 10 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 60)) (Var (V_TEMP 65))) $;
	Move (V_TEMP 66) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 67) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 68) (Extract 7 0 (Var (V_TEMP 67))) $;
	Move (V_TEMP 69) (BinOp OP_AND (Var (V_TEMP 68)) (Word 0x1 8)) $;
	Move (V_TEMP 70) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 69))) $;
	Move (V_TEMP 71) (BinOp OP_LSHIFT (Var (V_TEMP 70)) (Word 11 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 66)) (Var (V_TEMP 71))) $;
	Move (V_TEMP 72) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xefff 16)) $;
	Move (V_TEMP 73) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 74) (Extract 7 0 (Var (V_TEMP 73))) $;
	Move (V_TEMP 75) (BinOp OP_AND (Var (V_TEMP 74)) (Word 0x1 8)) $;
	Move (V_TEMP 76) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 75))) $;
	Move (V_TEMP 77) (BinOp OP_LSHIFT (Var (V_TEMP 76)) (Word 12 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 72)) (Var (V_TEMP 77))) $;
	Move (V_TEMP 78) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xdfff 16)) $;
	Move (V_TEMP 79) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 80) (Extract 7 0 (Var (V_TEMP 79))) $;
	Move (V_TEMP 81) (BinOp OP_AND (Var (V_TEMP 80)) (Word 0x1 8)) $;
	Move (V_TEMP 82) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 81))) $;
	Move (V_TEMP 83) (BinOp OP_LSHIFT (Var (V_TEMP 82)) (Word 13 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 78)) (Var (V_TEMP 83))) $;
	Move (V_TEMP 84) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xbfff 16)) $;
	Move (V_TEMP 85) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 86) (Extract 7 0 (Var (V_TEMP 85))) $;
	Move (V_TEMP 87) (BinOp OP_AND (Var (V_TEMP 86)) (Word 0x1 8)) $;
	Move (V_TEMP 88) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 87))) $;
	Move (V_TEMP 89) (BinOp OP_LSHIFT (Var (V_TEMP 88)) (Word 14 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 84)) (Var (V_TEMP 89))) $;
	Move (V_TEMP 90) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0x7fff 16)) $;
	Move (V_TEMP 91) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 92) (Extract 7 0 (Var (V_TEMP 91))) $;
	Move (V_TEMP 93) (BinOp OP_AND (Var (V_TEMP 92)) (Word 0x1 8)) $;
	Move (V_TEMP 94) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 93))) $;
	Move (V_TEMP 95) (BinOp OP_LSHIFT (Var (V_TEMP 94)) (Word 15 16)) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 90)) (Var (V_TEMP 95))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00299eff: SUB EAX,0xffff *)
(*       1023: SUB EAX,0xffff *)
| 0x3ff => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0xffff 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299f04: JNZ 0x00299be0 *)
(*       1028: JNZ 0x00299be0 *)
| 0x404 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299f0a: RET *)
(*       1034: RET *)
| 0x40a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00299f10: MOVBE EAX,dword ptr [RDI] *)
(*       1040: MOVBE EAX,dword ptr [RDI] *)
| 0x410 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Concat (Extract 7 0 (Var (V_TEMP 0))) (Concat (Extract 15 8 (Var (V_TEMP 0))) (Concat (Extract 23 16 (Var (V_TEMP 0))) (Extract 31 24 (Var (V_TEMP 0)))))))
)

(* 0x00299f14: MOVBE ECX,dword ptr [RSI] *)
(*       1044: MOVBE ECX,dword ptr [RSI] *)
| 0x414 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Concat (Extract 7 0 (Var (V_TEMP 0))) (Concat (Extract 15 8 (Var (V_TEMP 0))) (Concat (Extract 23 16 (Var (V_TEMP 0))) (Extract 31 24 (Var (V_TEMP 0)))))))
)

(* 0x00299f18: SHL RAX,0x20 *)
(*       1048: SHL RAX,0x20 *)
| 0x418 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_RAX) $;
	Move R_RAX (BinOp OP_LSHIFT (Var R_RAX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 4)) (Word 0x0 64))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 6)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 5))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 7)) (Var (V_TEMP 8)))) $;
	Move (V_TEMP 9) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 11) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 10))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 9)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 9)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x00299f1c: SHL RCX,0x20 *)
(*       1052: SHL RCX,0x20 *)
| 0x41c => Some (4,
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

(* 0x00299f20: MOVBE EDI,dword ptr [RDI + RDX*0x1 + -0x4] *)
(*       1056: MOVBE EDI,dword ptr [RDI + RDX*0x1 + -0x4] *)
| 0x420 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 4) $;
	Move R_RDI (Concat (Extract 63 32 (Var R_RDI)) (Concat (Extract 7 0 (Var (V_TEMP 3))) (Concat (Extract 15 8 (Var (V_TEMP 3))) (Concat (Extract 23 16 (Var (V_TEMP 3))) (Extract 31 24 (Var (V_TEMP 3)))))))
)

(* 0x00299f26: MOVBE ESI,dword ptr [RSI + RDX*0x1 + -0x4] *)
(*       1062: MOVBE ESI,dword ptr [RSI + RDX*0x1 + -0x4] *)
| 0x426 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Concat (Extract 7 0 (Var (V_TEMP 3))) (Concat (Extract 15 8 (Var (V_TEMP 3))) (Concat (Extract 23 16 (Var (V_TEMP 3))) (Extract 31 24 (Var (V_TEMP 3)))))))
)

(* 0x00299f2c: OR RAX,RDI *)
(*       1068: OR RAX,RDI *)
| 0x42c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_OR (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299f2f: OR RCX,RSI *)
(*       1071: OR RCX,RSI *)
| 0x42f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299f32: SUB RAX,RCX *)
(*       1074: SUB RAX,RCX *)
| 0x432 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299f35: JZ 0x00299f3c *)
(*       1077: JZ 0x00299f3c *)
| 0x435 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x43c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00299f37: SBB EAX,EAX *)
(*       1079: SBB EAX,EAX *)
| 0x437 => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 32 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 1)) (Var (V_TEMP 0)))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 2)))) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_OF)) (Var (V_TEMP 3)))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 0)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 5) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 4)))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 5)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 6)) (Word 0x0 8))))
)

(* 0x00299f39: OR EAX,0x1 *)
(*       1081: OR EAX,0x1 *)
| 0x439 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x00299f3c: RET *)
(*       1084: RET *)
| 0x43c => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx memcmp_avx2_amd64.
Proof. Picinae_typecheck. Qed.

