(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: FUN_001ba950 at 0x1ba950
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition strlen_sse2_amd64 : program := fun _ a => match a with

(* ---- FUN_001ba950 ---- *)

(* 0x001ba950: ENDBR64 *)
(*    1812816: ENDBR64 *)
| 0x1ba950 => Some (4,
	Nop
)

(* 0x001ba954: PXOR XMM0,XMM0 *)
(*    1812820: PXOR XMM0,XMM0 *)
| 0x1ba954 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))))
)

(* 0x001ba958: PXOR XMM1,XMM1 *)
(*    1812824: PXOR XMM1,XMM1 *)
| 0x1ba958 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM1))))
)

(* 0x001ba95c: PXOR XMM2,XMM2 *)
(*    1812828: PXOR XMM2,XMM2 *)
| 0x1ba95c => Some (4,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM2))))
)

(* 0x001ba960: PXOR XMM3,XMM3 *)
(*    1812832: PXOR XMM3,XMM3 *)
| 0x1ba960 => Some (4,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))))
)

(* 0x001ba964: MOV RAX,RDI *)
(*    1812836: MOV RAX,RDI *)
| 0x1ba964 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001ba967: MOV RCX,RDI *)
(*    1812839: MOV RCX,RDI *)
| 0x1ba967 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001ba96a: AND RCX,0xfff *)
(*    1812842: AND RCX,0xfff *)
| 0x1ba96a => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_AND (Var R_RCX) (Word 0xfff 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba971: CMP RCX,0xfcf *)
(*    1812849: CMP RCX,0xfcf *)
| 0x1ba971 => Some (7,
	Move (V_TEMP 0x3e680) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e680)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfcf 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3e780) (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e780)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba978: JA 0x001ba9e0 *)
(*    1812856: JA 0x001ba9e0 *)
| 0x1ba978 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1ba9e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001ba97a: MOVDQU XMM4,xmmword ptr [RAX] *)
(*    1812858: MOVDQU XMM4,xmmword ptr [RAX] *)
| 0x1ba97a => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Var (V_TEMP 0x6c80)))
)

(* 0x001ba97e: PCMPEQB XMM4,XMM0 *)
(*    1812862: PCMPEQB XMM4,XMM0 *)
| 0x1ba97e => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 8 (Var R_YMM4)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 16 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 24 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 40 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 48 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 56 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 72 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 80 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 88 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 104 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 112 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 120 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM0)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM4))))
)

(* 0x001ba982: PMOVMSKB EDX,XMM4 *)
(*    1812866: PMOVMSKB EDX,XMM4 *)
| 0x1ba982 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001ba986: TEST EDX,EDX *)
(*    1812870: TEST EDX,EDX *)
| 0x1ba986 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba988: JZ 0x001ba98e *)
(*    1812872: JZ 0x001ba98e *)
| 0x1ba988 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1ba98e 64)
	) (* else *) (
		Nop
	)
)

(* 0x001ba98a: BSF EAX,EDX *)
(*    1812874: BSF EAX,EDX *)
| 0x1ba98a => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001ba98d: RET *)
(*    1812877: RET *)
| 0x1ba98d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001ba98e: AND RAX,-0x10 *)
(*    1812878: AND RAX,-0x10 *)
| 0x1ba98e => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xfffffffffffffff0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba992: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1812882: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1ba992 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001ba997: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1812887: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1ba997 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001ba99c: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1812892: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1ba99c => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001ba9a1: PMOVMSKB EDX,XMM1 *)
(*    1812897: PMOVMSKB EDX,XMM1 *)
| 0x1ba9a1 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001ba9a5: PMOVMSKB R8D,XMM2 *)
(*    1812901: PMOVMSKB R8D,XMM2 *)
| 0x1ba9a5 => Some (5,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001ba9aa: PMOVMSKB ECX,XMM3 *)
(*    1812906: PMOVMSKB ECX,XMM3 *)
| 0x1ba9aa => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001ba9ae: SHL RDX,0x10 *)
(*    1812910: SHL RDX,0x10 *)
| 0x1ba9ae => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001ba9b2: SHL RCX,0x10 *)
(*    1812914: SHL RCX,0x10 *)
| 0x1ba9b2 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001ba9b6: OR RCX,R8 *)
(*    1812918: OR RCX,R8 *)
| 0x1ba9b6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9b9: SHL RCX,0x20 *)
(*    1812921: SHL RCX,0x20 *)
| 0x1ba9b9 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001ba9bd: OR RDX,RCX *)
(*    1812925: OR RDX,RCX *)
| 0x1ba9bd => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9c0: MOV RCX,RDI *)
(*    1812928: MOV RCX,RDI *)
| 0x1ba9c0 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001ba9c3: XOR RCX,RAX *)
(*    1812931: XOR RCX,RAX *)
| 0x1ba9c3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_XOR (Var R_RCX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9c6: AND RAX,-0x40 *)
(*    1812934: AND RAX,-0x40 *)
| 0x1ba9c6 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9ca: SAR RDX,CL *)
(*    1812938: SAR RDX,CL *)
| 0x1ba9ca => Some (3,
	Move (V_TEMP 0x68900) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x68980) (Var R_RDX) $;
	Move R_RDX (BinOp OP_ARSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68900)))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68980)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68900)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001ba9cd: TEST RDX,RDX *)
(*    1812941: TEST RDX,RDX *)
| 0x1ba9cd => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9d0: JZ 0x001baa50 *)
(*    1812944: JZ 0x001baa50 *)
| 0x1ba9d0 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1baa50 64)
	) (* else *) (
		Nop
	)
)

(* 0x001ba9d2: BSF RAX,RDX *)
(*    1812946: BSF RAX,RDX *)
| 0x1ba9d2 => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001ba9d6: RET *)
(*    1812950: RET *)
| 0x1ba9d6 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001ba9e0: AND RAX,-0x40 *)
(*    1812960: AND RAX,-0x40 *)
| 0x1ba9e0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001ba9e4: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1812964: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1ba9e4 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001ba9e8: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1812968: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1ba9e8 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001ba9ed: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1812973: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1ba9ed => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001ba9f2: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1812978: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1ba9f2 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001ba9f7: PMOVMSKB ESI,XMM0 *)
(*    1812983: PMOVMSKB ESI,XMM0 *)
| 0x1ba9f7 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001ba9fb: PMOVMSKB EDX,XMM1 *)
(*    1812987: PMOVMSKB EDX,XMM1 *)
| 0x1ba9fb => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001ba9ff: PMOVMSKB R8D,XMM2 *)
(*    1812991: PMOVMSKB R8D,XMM2 *)
| 0x1ba9ff => Some (5,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001baa04: PMOVMSKB ECX,XMM3 *)
(*    1812996: PMOVMSKB ECX,XMM3 *)
| 0x1baa04 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001baa08: SHL RDX,0x10 *)
(*    1813000: SHL RDX,0x10 *)
| 0x1baa08 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baa0c: SHL RCX,0x10 *)
(*    1813004: SHL RCX,0x10 *)
| 0x1baa0c => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baa10: OR RDX,RSI *)
(*    1813008: OR RDX,RSI *)
| 0x1baa10 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa13: OR RCX,R8 *)
(*    1813011: OR RCX,R8 *)
| 0x1baa13 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa16: SHL RCX,0x20 *)
(*    1813014: SHL RCX,0x20 *)
| 0x1baa16 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baa1a: OR RDX,RCX *)
(*    1813018: OR RDX,RCX *)
| 0x1baa1a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa1d: MOV RCX,RDI *)
(*    1813021: MOV RCX,RDI *)
| 0x1baa1d => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001baa20: XOR RCX,RAX *)
(*    1813024: XOR RCX,RAX *)
| 0x1baa20 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_XOR (Var R_RCX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa23: AND RAX,-0x40 *)
(*    1813027: AND RAX,-0x40 *)
| 0x1baa23 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa27: SAR RDX,CL *)
(*    1813031: SAR RDX,CL *)
| 0x1baa27 => Some (3,
	Move (V_TEMP 0x68900) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x68980) (Var R_RDX) $;
	Move R_RDX (BinOp OP_ARSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68900)))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68980)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68900)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baa2a: TEST RDX,RDX *)
(*    1813034: TEST RDX,RDX *)
| 0x1baa2a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa2d: JZ 0x001baa40 *)
(*    1813037: JZ 0x001baa40 *)
| 0x1baa2d => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1baa40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001baa2f: BSF RAX,RDX *)
(*    1813039: BSF RAX,RDX *)
| 0x1baa2f => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001baa33: RET *)
(*    1813043: RET *)
| 0x1baa33 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001baa40: PXOR XMM1,XMM1 *)
(*    1813056: PXOR XMM1,XMM1 *)
| 0x1baa40 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM1))))
)

(* 0x001baa44: PXOR XMM2,XMM2 *)
(*    1813060: PXOR XMM2,XMM2 *)
| 0x1baa44 => Some (4,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM2))))
)

(* 0x001baa48: PXOR XMM3,XMM3 *)
(*    1813064: PXOR XMM3,XMM3 *)
| 0x1baa48 => Some (4,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))))
)

(* 0x001baa4c: NOP dword ptr [RAX] *)
(*    1813068: NOP dword ptr [RAX] *)
| 0x1baa4c => Some (4,
	Nop
)

(* 0x001baa50: MOVDQA XMM0,xmmword ptr [RAX + 0x40] *)
(*    1813072: MOVDQA XMM0,xmmword ptr [RAX + 0x40] *)
| 0x1baa50 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001baa55: PMINUB XMM0,xmmword ptr [RAX + 0x50] *)
(*    1813077: PMINUB XMM0,xmmword ptr [RAX + 0x50] *)
| 0x1baa55 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x50 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa5a: PMINUB XMM0,xmmword ptr [RAX + 0x60] *)
(*    1813082: PMINUB XMM0,xmmword ptr [RAX + 0x60] *)
| 0x1baa5a => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x60 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa5f: PMINUB XMM0,xmmword ptr [RAX + 0x70] *)
(*    1813087: PMINUB XMM0,xmmword ptr [RAX + 0x70] *)
| 0x1baa5f => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x70 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa64: PCMPEQB XMM0,XMM3 *)
(*    1813092: PCMPEQB XMM0,XMM3 *)
| 0x1baa64 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa68: PMOVMSKB EDX,XMM0 *)
(*    1813096: PMOVMSKB EDX,XMM0 *)
| 0x1baa68 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001baa6c: TEST EDX,EDX *)
(*    1813100: TEST EDX,EDX *)
| 0x1baa6c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa6e: JNZ 0x001baaa0 *)
(*    1813102: JNZ 0x001baaa0 *)
| 0x1baa6e => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1baaa0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001baa70: SUB RAX,-0x80 *)
(*    1813104: SUB RAX,-0x80 *)
| 0x1baa70 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa74: MOVDQA XMM0,xmmword ptr [RAX] *)
(*    1813108: MOVDQA XMM0,xmmword ptr [RAX] *)
| 0x1baa74 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001baa78: PMINUB XMM0,xmmword ptr [RAX + 0x10] *)
(*    1813112: PMINUB XMM0,xmmword ptr [RAX + 0x10] *)
| 0x1baa78 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa7d: PMINUB XMM0,xmmword ptr [RAX + 0x20] *)
(*    1813117: PMINUB XMM0,xmmword ptr [RAX + 0x20] *)
| 0x1baa7d => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa82: PMINUB XMM0,xmmword ptr [RAX + 0x30] *)
(*    1813122: PMINUB XMM0,xmmword ptr [RAX + 0x30] *)
| 0x1baa82 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa87: PCMPEQB XMM0,XMM3 *)
(*    1813127: PCMPEQB XMM0,XMM3 *)
| 0x1baa87 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baa8b: PMOVMSKB EDX,XMM0 *)
(*    1813131: PMOVMSKB EDX,XMM0 *)
| 0x1baa8b => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001baa8f: TEST EDX,EDX *)
(*    1813135: TEST EDX,EDX *)
| 0x1baa8f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baa91: JNZ 0x001baaa4 *)
(*    1813137: JNZ 0x001baaa4 *)
| 0x1baa91 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1baaa4 64)
	) (* else *) (
		Nop
	)
)

(* 0x001baa93: JMP 0x001baa50 *)
(*    1813139: JMP 0x001baa50 *)
| 0x1baa93 => Some (2,
	Jmp (Word 0x1baa50 64)
)

(* 0x001baaa0: ADD RAX,0x40 *)
(*    1813152: ADD RAX,0x40 *)
| 0x1baaa0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baaa4: PXOR XMM0,XMM0 *)
(*    1813156: PXOR XMM0,XMM0 *)
| 0x1baaa4 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))))
)

(* 0x001baaa8: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1813160: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1baaa8 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baaac: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1813164: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1baaac => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001baab1: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1813169: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1baab1 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001baab6: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1813174: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1baab6 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001baabb: PMOVMSKB ESI,XMM0 *)
(*    1813179: PMOVMSKB ESI,XMM0 *)
| 0x1baabb => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001baabf: PMOVMSKB EDX,XMM1 *)
(*    1813183: PMOVMSKB EDX,XMM1 *)
| 0x1baabf => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001baac3: PMOVMSKB R8D,XMM2 *)
(*    1813187: PMOVMSKB R8D,XMM2 *)
| 0x1baac3 => Some (5,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001baac8: PMOVMSKB ECX,XMM3 *)
(*    1813192: PMOVMSKB ECX,XMM3 *)
| 0x1baac8 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001baacc: SHL RDX,0x10 *)
(*    1813196: SHL RDX,0x10 *)
| 0x1baacc => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baad0: SHL RCX,0x10 *)
(*    1813200: SHL RCX,0x10 *)
| 0x1baad0 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baad4: OR RDX,RSI *)
(*    1813204: OR RDX,RSI *)
| 0x1baad4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baad7: OR RCX,R8 *)
(*    1813207: OR RCX,R8 *)
| 0x1baad7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baada: SHL RCX,0x20 *)
(*    1813210: SHL RCX,0x20 *)
| 0x1baada => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001baade: OR RDX,RCX *)
(*    1813214: OR RDX,RCX *)
| 0x1baade => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baae1: BSF RDX,RDX *)
(*    1813217: BSF RDX,RDX *)
| 0x1baae1 => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RDX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RDX (Var (V_TEMP 0x34580))
	)
)

(* 0x001baae5: ADD RAX,RDX *)
(*    1813221: ADD RAX,RDX *)
| 0x1baae5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baae8: SUB RAX,RDI *)
(*    1813224: SUB RAX,RDI *)
| 0x1baae8 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baaeb: RET *)
(*    1813227: RET *)
| 0x1baaeb => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx strlen_sse2_amd64.
Proof. Picinae_typecheck. Qed.
