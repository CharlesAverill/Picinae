(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: cfmakeraw at 0x21a220
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition cfmakeraw_amd64 : program := fun _ a => match a with

(* ---- cfmakeraw ---- *)

(* 0x0021a220: ENDBR64 *)
(*    2204192: ENDBR64 *)
| 0x21a220 => Some (4,
	Nop
)

(* 0x0021a224: MOV EAX,dword ptr [RDI] *)
(*    2204196: MOV EAX,dword ptr [RDI] *)
| 0x21a224 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0021a226: MOV EDX,dword ptr [RDI + 0x4] *)
(*    2204198: MOV EDX,dword ptr [RDI + 0x4] *)
| 0x21a226 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0021a229: MOV ECX,dword ptr [RDI + 0xc] *)
(*    2204201: MOV ECX,dword ptr [RDI + 0xc] *)
| 0x21a229 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xc 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x0021a22c: AND EAX,0xfffffa14 *)
(*    2204204: AND EAX,0xfffffa14 *)
| 0x21a22c => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xfffffa14 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021a231: AND EDX,0xfffffffe *)
(*    2204209: AND EDX,0xfffffffe *)
| 0x21a231 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xfffffffe 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021a234: MOVD XMM0,EAX *)
(*    2204212: MOVD XMM0,EAX *)
| 0x21a234 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RAX))))
)

(* 0x0021a238: MOV EAX,dword ptr [RDI + 0x8] *)
(*    2204216: MOV EAX,dword ptr [RDI + 0x8] *)
| 0x21a238 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0021a23b: AND ECX,0xffff7fb4 *)
(*    2204219: AND ECX,0xffff7fb4 *)
| 0x21a23b => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xffff7fb4 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021a241: MOVD XMM3,EDX *)
(*    2204225: MOVD XMM3,EDX *)
| 0x21a241 => Some (4,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RDX))))
)

(* 0x0021a245: MOVD XMM2,ECX *)
(*    2204229: MOVD XMM2,ECX *)
| 0x21a245 => Some (4,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RCX))))
)

(* 0x0021a249: PUNPCKLDQ XMM0,XMM3 *)
(*    2204233: PUNPCKLDQ XMM0,XMM3 *)
| 0x21a249 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 63 32 (Var R_YMM3)) (Extract 95 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 63 32 (Var R_YMM0)) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 31 0 (Var R_YMM3)) (Extract 31 0 (Var R_YMM0))))
)

(* 0x0021a24d: AND EAX,0xfffffecf *)
(*    2204237: AND EAX,0xfffffecf *)
| 0x21a24d => Some (5,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xfffffecf 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021a252: OR EAX,0x30 *)
(*    2204242: OR EAX,0x30 *)
| 0x21a252 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Extract 31 0 (Var R_RAX)) (Word 0x30 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021a255: MOVD XMM1,EAX *)
(*    2204245: MOVD XMM1,EAX *)
| 0x21a255 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RAX))))
)

(* 0x0021a259: MOV EAX,0x100 *)
(*    2204249: MOV EAX,0x100 *)
| 0x21a259 => Some (5,
	Move R_RAX (Word 0x100 64)
)

(* 0x0021a25e: PUNPCKLDQ XMM1,XMM2 *)
(*    2204254: PUNPCKLDQ XMM1,XMM2 *)
| 0x21a25e => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 63 32 (Var R_YMM2)) (Extract 95 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 63 32 (Var R_YMM1)) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 31 0 (Var R_YMM2)) (Extract 31 0 (Var R_YMM1))))
)

(* 0x0021a262: MOV word ptr [RDI + 0x16],AX *)
(*    2204258: MOV word ptr [RDI + 0x16],AX *)
| 0x21a262 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x16 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x0021a266: PUNPCKLQDQ XMM0,XMM1 *)
(*    2204262: PUNPCKLQDQ XMM0,XMM1 *)
| 0x21a266 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 63 0 (Var R_YMM1)) (Extract 63 0 (Var R_YMM0))))
)

(* 0x0021a26a: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    2204266: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x21a26a => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x0021a26d: RET *)
(*    2204269: RET *)
| 0x21a26d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx cfmakeraw_amd64.
Proof. Picinae_typecheck. Qed.
