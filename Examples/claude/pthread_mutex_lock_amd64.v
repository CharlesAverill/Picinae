(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: pthread_mutex_lock at 0x197ef0
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition pthread_mutex_lock_amd64 : program := fun _ a => match a with

(* ---- pthread_mutex_lock ---- *)

(* 0x00197ef0: ENDBR64 *)
(*    1670896: ENDBR64 *)
| 0x197ef0 => Some (4,
	Nop
)

(* 0x00197ef4: MOV EAX,dword ptr [RDI + 0x10] *)
(*    1670900: MOV EAX,dword ptr [RDI + 0x10] *)
| 0x197ef4 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197ef7: MOV EDX,EAX *)
(*    1670903: MOV EDX,EAX *)
| 0x197ef7 => Some (2,
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00197ef9: AND EDX,0x17f *)
(*    1670905: AND EDX,0x17f *)
| 0x197ef9 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x17f 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197eff: NOP *)
(*    1670911: NOP *)
| 0x197eff => Some (1,
	Nop
)

(* 0x00197f00: AND EAX,0x7c *)
(*    1670912: AND EAX,0x7c *)
| 0x197f00 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x7c 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f03: JNZ 0x00197fb0 *)
(*    1670915: JNZ 0x00197fb0 *)
| 0x197f03 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197fb0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f09: PUSH RBX *)
(*    1670921: PUSH RBX *)
| 0x197f09 => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00197f0a: SUB RSP,0x10 *)
(*    1670922: SUB RSP,0x10 *)
| 0x197f0a => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSP) (Word 0x10 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f0e: TEST EDX,EDX *)
(*    1670926: TEST EDX,EDX *)
| 0x197f0e => Some (2,
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

(* 0x00197f10: JNZ 0x00197fb8 *)
(*    1670928: JNZ 0x00197fb8 *)
| 0x197f10 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197fb8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f16: MOV R9D,dword ptr [0x0031ca94] *)
(*    1670934: MOV R9D,dword ptr [0x0031ca94] *)
| 0x197f16 => Some (7,
	Move R_R9 (Concat (Extract 63 32 (Var R_R9)) (Load (Var V_MEM64) (Word 0x31ca94 64) LittleE 4)) $;
	Move R_R9 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R9)))
)

(* 0x00197f1d: TEST R9D,R9D *)
(*    1670941: TEST R9D,R9D *)
| 0x197f1d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_R9)) (Extract 31 0 (Var R_R9))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f20: JNZ 0x00197f80 *)
(*    1670944: JNZ 0x00197f80 *)
| 0x197f20 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197f80 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f22: MOV ESI,dword ptr [RDI + 0x10] *)
(*    1670946: MOV ESI,dword ptr [RDI + 0x10] *)
| 0x197f22 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00197f25: AND ESI,0x80 *)
(*    1670949: AND ESI,0x80 *)
| 0x197f25 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0x80 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f2b: JNZ 0x00197f39 *)
(*    1670955: JNZ 0x00197f39 *)
| 0x197f2b => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197f39 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f2d: MOV EAX,dword ptr FS:[0x18] *)
(*    1670957: MOV EAX,dword ptr FS:[0x18] *)
| 0x197f2d => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x18 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197f35: TEST EAX,EAX *)
(*    1670965: TEST EAX,EAX *)
| 0x197f35 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f37: JZ 0x00197f70 *)
(*    1670967: JZ 0x00197f70 *)
| 0x197f37 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x197f70 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f39: XOR EAX,EAX *)
(*    1670969: XOR EAX,EAX *)
| 0x197f39 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f3b: MOV EDX,0x1 *)
(*    1670971: MOV EDX,0x1 *)
| 0x197f3b => Some (5,
	Move R_RDX (Word 0x1 64)
)

(* 0x00197f40: CMPXCHG.LOCK dword ptr [RDI],EDX *)
(*    1670976: CMPXCHG.LOCK dword ptr [RDI],EDX *)
| 0x197f40 => Some (4,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe5980) (Var (V_TEMP 0x6b00)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xe5980)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xe5a80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0xe5a80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))) $;
	If (Var R_ZF) (
		Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDX)) $;
		Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
	) (* else *) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x00197f44: JNZ 0x00197ff8 *)
(*    1670980: JNZ 0x00197ff8 *)
| 0x197f44 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197ff8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f4a: MOV ECX,dword ptr [RDI + 0x8] *)
(*    1670986: MOV ECX,dword ptr [RDI + 0x8] *)
| 0x197f4a => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00197f4d: TEST ECX,ECX *)
(*    1670989: TEST ECX,ECX *)
| 0x197f4d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f4f: JNZ 0x001980b1 *)
(*    1670991: JNZ 0x001980b1 *)
| 0x197f4f => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1980b1 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f55: MOV EAX,dword ptr FS:[0x2d0] *)
(*    1670997: MOV EAX,dword ptr FS:[0x2d0] *)
| 0x197f55 => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x2d0 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197f5d: MOV dword ptr [RDI + 0x8],EAX *)
(*    1671005: MOV dword ptr [RDI + 0x8],EAX *)
| 0x197f5d => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00197f60: ADD dword ptr [RDI + 0xc],0x1 *)
(*    1671008: ADD dword ptr [RDI + 0xc],0x1 *)
| 0x197f60 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xc 64)) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Var (V_TEMP 0x6b00))))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b00)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b00)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (BinOp OP_PLUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6b00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f64: NOP *)
(*    1671012: NOP *)
| 0x197f64 => Some (1,
	Nop
)

(* 0x00197f65: XOR EAX,EAX *)
(*    1671013: XOR EAX,EAX *)
| 0x197f65 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f67: ADD RSP,0x10 *)
(*    1671015: ADD RSP,0x10 *)
| 0x197f67 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f6b: POP RBX *)
(*    1671019: POP RBX *)
| 0x197f6b => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55480))
)

(* 0x00197f6c: RET *)
(*    1671020: RET *)
| 0x197f6c => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00197f70: MOV R8D,dword ptr [RDI] *)
(*    1671024: MOV R8D,dword ptr [RDI] *)
| 0x197f70 => Some (3,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Var (V_TEMP 0x11f80))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x00197f73: TEST R8D,R8D *)
(*    1671027: TEST R8D,R8D *)
| 0x197f73 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_R8)) (Extract 31 0 (Var R_R8))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f76: JNZ 0x00197f39 *)
(*    1671030: JNZ 0x00197f39 *)
| 0x197f76 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197f39 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f78: MOV dword ptr [RDI],0x1 *)
(*    1671032: MOV dword ptr [RDI],0x1 *)
| 0x197f78 => Some (6,
	Move (V_TEMP 0x6b00) (Word 0x1 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00197f7e: JMP 0x00197f4a *)
(*    1671038: JMP 0x00197f4a *)
| 0x197f7e => Some (2,
	Jmp (Word 0x197f4a 64)
)

(* 0x00197f80: MOV EAX,dword ptr [RDI + 0x10] *)
(*    1671040: MOV EAX,dword ptr [RDI + 0x10] *)
| 0x197f80 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197f83: TEST AH,0x3 *)
(*    1671043: TEST AH,0x3 *)
| 0x197f83 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6fe80) (BinOp OP_AND (Extract 15 8 (Var R_RAX)) (Word 0x3 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6fe80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f86: JZ 0x00197f90 *)
(*    1671046: JZ 0x00197f90 *)
| 0x197f86 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x197f90 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f88: TEST AH,0x1 *)
(*    1671048: TEST AH,0x1 *)
| 0x197f88 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6fe80) (BinOp OP_AND (Extract 15 8 (Var R_RAX)) (Word 0x1 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6fe80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f8b: JZ 0x00197f22 *)
(*    1671051: JZ 0x00197f22 *)
| 0x197f8b => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x197f22 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197f8d: JMP 0x00197f96 *)
(*    1671053: JMP 0x00197f96 *)
| 0x197f8d => Some (2,
	Jmp (Word 0x197f96 64)
)

(* 0x00197f90: OR AH,0x1 *)
(*    1671056: OR AH,0x1 *)
| 0x197f90 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 16 (Var R_RAX)) (Concat (BinOp OP_OR (Extract 15 8 (Var R_RAX)) (Word 0x1 8)) (Extract 7 0 (Var R_RAX)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 15 8 (Var R_RAX)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_RAX)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 15 8 (Var R_RAX)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f93: MOV dword ptr [RDI + 0x10],EAX *)
(*    1671059: MOV dword ptr [RDI + 0x10],EAX *)
| 0x197f93 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00197f96: MOV EDX,dword ptr [RDI + 0x10] *)
(*    1671062: MOV EDX,dword ptr [RDI + 0x10] *)
| 0x197f96 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00197f99: ADD RSP,0x10 *)
(*    1671065: ADD RSP,0x10 *)
| 0x197f99 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197f9d: LEA RSI,[RDI + 0x16] *)
(*    1671069: LEA RSI,[RDI + 0x16] *)
| 0x197f9d => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x16 64)) $;
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x00197fa1: POP RBX *)
(*    1671073: POP RBX *)
| 0x197fa1 => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55480))
)

(* 0x00197fa2: AND EDX,0x80 *)
(*    1671074: AND EDX,0x80 *)
| 0x197fa2 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x80 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fa8: JMP 0x00190d10 *)
(*    1671080: JMP 0x00190d10 *)
| 0x197fa8 => Some (5,
	Jmp (Word 0x190d10 64)
)

(* 0x00197fb0: JMP 0x001977a0 *)
(*    1671088: JMP 0x001977a0 *)
| 0x197fb0 => Some (5,
	Jmp (Word 0x1977a0 64)
)

(* 0x00197fb8: CMP EDX,0x100 *)
(*    1671096: CMP EDX,0x100 *)
| 0x197fb8 => Some (6,
	Move (V_TEMP 0x3e500) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e500)) (Word 0x100 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e600) (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fbe: JZ 0x00197f96 *)
(*    1671102: JZ 0x00197f96 *)
| 0x197fbe => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x197f96 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197fc0: MOV EDX,dword ptr [RDI + 0x10] *)
(*    1671104: MOV EDX,dword ptr [RDI + 0x10] *)
| 0x197fc0 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00197fc3: AND EDX,0x7f *)
(*    1671107: AND EDX,0x7f *)
| 0x197fc3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x7f 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fc6: CMP EDX,0x1 *)
(*    1671110: CMP EDX,0x1 *)
| 0x197fc6 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fc9: JNZ 0x00198064 *)
(*    1671113: JNZ 0x00198064 *)
| 0x197fc9 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x198064 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197fcf: MOV EAX,dword ptr FS:[0x2d0] *)
(*    1671119: MOV EAX,dword ptr FS:[0x2d0] *)
| 0x197fcf => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x2d0 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197fd7: CMP dword ptr [RDI + 0x8],EAX *)
(*    1671127: CMP dword ptr [RDI + 0x8],EAX *)
| 0x197fd7 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x3ef80) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fda: JNZ 0x0019800c *)
(*    1671130: JNZ 0x0019800c *)
| 0x197fda => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x19800c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197fdc: MOV EAX,dword ptr [RDI + 0x4] *)
(*    1671132: MOV EAX,dword ptr [RDI + 0x4] *)
| 0x197fdc => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00197fdf: CMP EAX,-0x1 *)
(*    1671135: CMP EAX,-0x1 *)
| 0x197fdf => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0xffffffff 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0xffffffff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0xffffffff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffff 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0xffffffff 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197fe2: JZ 0x001980a7 *)
(*    1671138: JZ 0x001980a7 *)
| 0x197fe2 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x1980a7 64)
	) (* else *) (
		Nop
	)
)

(* 0x00197fe8: ADD EAX,0x1 *)
(*    1671144: ADD EAX,0x1 *)
| 0x197fe8 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197feb: MOV dword ptr [RDI + 0x4],EAX *)
(*    1671147: MOV dword ptr [RDI + 0x4],EAX *)
| 0x197feb => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00197fee: XOR EAX,EAX *)
(*    1671150: XOR EAX,EAX *)
| 0x197fee => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00197ff0: JMP 0x00197f67 *)
(*    1671152: JMP 0x00197f67 *)
| 0x197ff0 => Some (5,
	Jmp (Word 0x197f67 64)
)

(* 0x00197ff8: MOV qword ptr [RSP + 0x8],RDI *)
(*    1671160: MOV qword ptr [RSP + 0x8],RDI *)
| 0x197ff8 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00197ffd: CALL 0x00191290 *)
(*    1671165: CALL 0x00191290 *)
| 0x197ffd => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x198002 64) LittleE 8) $;
	Jmp (Word 0x191290 64)
)

(* 0x00198002: MOV RDI,qword ptr [RSP + 0x8] *)
(*    1671170: MOV RDI,qword ptr [RSP + 0x8] *)
| 0x198002 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x00198007: JMP 0x00197f4a *)
(*    1671175: JMP 0x00197f4a *)
| 0x198007 => Some (5,
	Jmp (Word 0x197f4a 64)
)

(* 0x0019800c: MOV ESI,dword ptr [RDI + 0x10] *)
(*    1671180: MOV ESI,dword ptr [RDI + 0x10] *)
| 0x19800c => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x0019800f: AND ESI,0x80 *)
(*    1671183: AND ESI,0x80 *)
| 0x19800f => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0x80 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198015: JNZ 0x00198046 *)
(*    1671189: JNZ 0x00198046 *)
| 0x198015 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x198046 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198017: MOV EAX,dword ptr FS:[0x18] *)
(*    1671191: MOV EAX,dword ptr FS:[0x18] *)
| 0x198017 => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x18 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0019801f: TEST EAX,EAX *)
(*    1671199: TEST EAX,EAX *)
| 0x19801f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198021: JNZ 0x00198046 *)
(*    1671201: JNZ 0x00198046 *)
| 0x198021 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x198046 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198023: MOV EDX,dword ptr [RDI] *)
(*    1671203: MOV EDX,dword ptr [RDI] *)
| 0x198023 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198025: TEST EDX,EDX *)
(*    1671205: TEST EDX,EDX *)
| 0x198025 => Some (2,
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

(* 0x00198027: JNZ 0x00198046 *)
(*    1671207: JNZ 0x00198046 *)
| 0x198027 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x198046 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198029: MOV dword ptr [RDI],0x1 *)
(*    1671209: MOV dword ptr [RDI],0x1 *)
| 0x198029 => Some (6,
	Move (V_TEMP 0x6b00) (Word 0x1 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x0019802f: MOV EAX,dword ptr [RDI + 0x8] *)
(*    1671215: MOV EAX,dword ptr [RDI + 0x8] *)
| 0x19802f => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00198032: TEST EAX,EAX *)
(*    1671218: TEST EAX,EAX *)
| 0x198032 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198034: JNZ 0x0019816e *)
(*    1671220: JNZ 0x0019816e *)
| 0x198034 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x19816e 64)
	) (* else *) (
		Nop
	)
)

(* 0x0019803a: MOV dword ptr [RDI + 0x4],0x1 *)
(*    1671226: MOV dword ptr [RDI + 0x4],0x1 *)
| 0x19803a => Some (7,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x6b00) (Word 0x1 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00198041: JMP 0x00197f55 *)
(*    1671233: JMP 0x00197f55 *)
| 0x198041 => Some (5,
	Jmp (Word 0x197f55 64)
)

(* 0x00198046: XOR EAX,EAX *)
(*    1671238: XOR EAX,EAX *)
| 0x198046 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198048: MOV EDX,0x1 *)
(*    1671240: MOV EDX,0x1 *)
| 0x198048 => Some (5,
	Move R_RDX (Word 0x1 64)
)

(* 0x0019804d: CMPXCHG.LOCK dword ptr [RDI],EDX *)
(*    1671245: CMPXCHG.LOCK dword ptr [RDI],EDX *)
| 0x19804d => Some (4,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe5980) (Var (V_TEMP 0x6b00)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xe5980)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xe5a80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0xe5a80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))) $;
	If (Var R_ZF) (
		Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDX)) $;
		Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
	) (* else *) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x00198051: JZ 0x0019802f *)
(*    1671249: JZ 0x0019802f *)
| 0x198051 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x19802f 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198053: MOV qword ptr [RSP + 0x8],RDI *)
(*    1671251: MOV qword ptr [RSP + 0x8],RDI *)
| 0x198053 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00198058: CALL 0x00191290 *)
(*    1671256: CALL 0x00191290 *)
| 0x198058 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x19805d 64) LittleE 8) $;
	Jmp (Word 0x191290 64)
)

(* 0x0019805d: MOV RDI,qword ptr [RSP + 0x8] *)
(*    1671261: MOV RDI,qword ptr [RSP + 0x8] *)
| 0x19805d => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x00198062: JMP 0x0019802f *)
(*    1671266: JMP 0x0019802f *)
| 0x198062 => Some (2,
	Jmp (Word 0x19802f 64)
)

(* 0x00198064: MOV EDX,dword ptr [RDI + 0x10] *)
(*    1671268: MOV EDX,dword ptr [RDI + 0x10] *)
| 0x198064 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198067: AND EDX,0x7f *)
(*    1671271: AND EDX,0x7f *)
| 0x198067 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x7f 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0019806a: CMP EDX,0x3 *)
(*    1671274: CMP EDX,0x3 *)
| 0x19806a => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x3 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0019806d: JNZ 0x00198121 *)
(*    1671277: JNZ 0x00198121 *)
| 0x19806d => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x198121 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198073: MOV EDX,0x1 *)
(*    1671283: MOV EDX,0x1 *)
| 0x198073 => Some (5,
	Move R_RDX (Word 0x1 64)
)

(* 0x00198078: CMPXCHG.LOCK dword ptr [RDI],EDX *)
(*    1671288: CMPXCHG.LOCK dword ptr [RDI],EDX *)
| 0x198078 => Some (4,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe5980) (Var (V_TEMP 0x6b00)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xe5980)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xe5a80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0xe5a80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))) $;
	If (Var R_ZF) (
		Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDX)) $;
		Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
	) (* else *) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x0019807c: JNZ 0x001980d0 *)
(*    1671292: JNZ 0x001980d0 *)
| 0x19807c => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1980d0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0019807e: CMP dword ptr [RDI + 0x8],0x0 *)
(*    1671294: CMP dword ptr [RDI + 0x8],0x0 *)
| 0x19807e => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x3e980) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198082: JZ 0x00197f55 *)
(*    1671298: JZ 0x00197f55 *)
| 0x198082 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x197f55 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198088: LEA RCX,[0x2e1840] *)
(*    1671304: LEA RCX,[0x2e1840] *)
| 0x198088 => Some (7,
	Move R_RCX (Word 0x2e1840 64)
)

(* 0x0019808f: MOV EDX,0x9b *)
(*    1671311: MOV EDX,0x9b *)
| 0x19808f => Some (5,
	Move R_RDX (Word 0x9b 64)
)

(* 0x00198094: LEA RSI,[0x2d956e] *)
(*    1671316: LEA RSI,[0x2d956e] *)
| 0x198094 => Some (7,
	Move R_RSI (Word 0x2d956e 64)
)

(* 0x0019809b: LEA RDI,[0x2d9599] *)
(*    1671323: LEA RDI,[0x2d9599] *)
| 0x19809b => Some (7,
	Move R_RDI (Word 0x2d9599 64)
)

(* 0x001980a2: CALL 0x00139e50 *)
(*    1671330: CALL 0x00139e50 *)
| 0x1980a2 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1980a7 64) LittleE 8) $;
	Jmp (Word 0x139e50 64)
)

(* 0x001980a7: MOV EAX,0xb *)
(*    1671335: MOV EAX,0xb *)
| 0x1980a7 => Some (5,
	Move R_RAX (Word 0xb 64)
)

(* 0x001980ac: JMP 0x00197f67 *)
(*    1671340: JMP 0x00197f67 *)
| 0x1980ac => Some (5,
	Jmp (Word 0x197f67 64)
)

(* 0x001980b1: LEA RCX,[0x2e1840] *)
(*    1671345: LEA RCX,[0x2e1840] *)
| 0x1980b1 => Some (7,
	Move R_RCX (Word 0x2e1840 64)
)

(* 0x001980b8: MOV EDX,0x5e *)
(*    1671352: MOV EDX,0x5e *)
| 0x1980b8 => Some (5,
	Move R_RDX (Word 0x5e 64)
)

(* 0x001980bd: LEA RSI,[0x2d956e] *)
(*    1671357: LEA RSI,[0x2d956e] *)
| 0x1980bd => Some (7,
	Move R_RSI (Word 0x2d956e 64)
)

(* 0x001980c4: LEA RDI,[0x2d9599] *)
(*    1671364: LEA RDI,[0x2d9599] *)
| 0x1980c4 => Some (7,
	Move R_RDI (Word 0x2d9599 64)
)

(* 0x001980cb: CALL 0x00139e50 *)
(*    1671371: CALL 0x00139e50 *)
| 0x1980cb => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1980d0 64) LittleE 8) $;
	Jmp (Word 0x139e50 64)
)

(* 0x001980d0: MOVSX EAX,word ptr [RDI + 0x14] *)
(*    1671376: MOVSX EAX,word ptr [RDI + 0x14] *)
| 0x1980d0 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x14 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_SIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001980d4: MOVSX EDX,word ptr [0x0031a2ac] *)
(*    1671380: MOVSX EDX,word ptr [0x0031a2ac] *)
| 0x1980d4 => Some (7,
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_SIGNED 32 (Load (Var V_MEM64) (Word 0x31a2ac 64) LittleE 2))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001980db: MOV ECX,0x1 *)
(*    1671387: MOV ECX,0x1 *)
| 0x1980db => Some (5,
	Move R_RCX (Word 0x1 64)
)

(* 0x001980e0: LEA EAX,[RAX + RAX*0x1 + 0xa] *)
(*    1671392: LEA EAX,[RAX + RAX*0x1 + 0xa] *)
| 0x1980e0 => Some (4,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xa 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var (V_TEMP 0x5080)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001980e4: CMP EAX,EDX *)
(*    1671396: CMP EAX,EDX *)
| 0x1980e4 => Some (2,
	Move (V_TEMP 0x3ef80) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001980e6: CMOVLE EDX,EAX *)
(*    1671398: CMOVLE EDX,EAX *)
| 0x1980e6 => Some (3,
	Move (V_TEMP 0x12f80) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 0x13080) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Var (V_TEMP 0x12f80))) $;
	Move (V_TEMP 0x3dc00) (Extract 31 0 (Var R_RAX)) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x3dc80) (BinOp OP_XOR (Var (V_TEMP 0x13080)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x1980e9 64)
	) (* else *) (
		Nop
	) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x3dc00)))
)

(* 0x001980e9: XOR EAX,EAX *)
(*    1671401: XOR EAX,EAX *)
| 0x1980e9 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001980eb: LEA EBX,[RAX + 0x1] *)
(*    1671403: LEA EBX,[RAX + 0x1] *)
| 0x1980eb => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_RBX (Concat (Extract 63 32 (Var R_RBX)) (Extract 31 0 (Var (V_TEMP 0x4780)))) $;
	Move R_RBX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBX)))
)

(* 0x001980ee: CMP EAX,EDX *)
(*    1671406: CMP EAX,EDX *)
| 0x1980ee => Some (2,
	Move (V_TEMP 0x3ef80) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001980f0: JGE 0x00198147 *)
(*    1671408: JGE 0x00198147 *)
| 0x1980f0 => Some (2,
	Move (V_TEMP 0x12f00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12f00))) (
		Jmp (Word 0x198147 64)
	) (* else *) (
		Nop
	)
)

(* 0x001980f2: PAUSE *)
(*    1671410: PAUSE *)
| 0x1980f2 => Some (2,
	Nop
)

(* 0x001980f4: MOV EAX,dword ptr [RDI] *)
(*    1671412: MOV EAX,dword ptr [RDI] *)
| 0x1980f4 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001980f6: TEST EAX,EAX *)
(*    1671414: TEST EAX,EAX *)
| 0x1980f6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001980f8: JZ 0x001980fe *)
(*    1671416: JZ 0x001980fe *)
| 0x1980f8 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1980fe 64)
	) (* else *) (
		Nop
	)
)

(* 0x001980fa: MOV EAX,EBX *)
(*    1671418: MOV EAX,EBX *)
| 0x1980fa => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RBX))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001980fc: JMP 0x001980eb *)
(*    1671420: JMP 0x001980eb *)
| 0x1980fc => Some (2,
	Jmp (Word 0x1980eb 64)
)

(* 0x001980fe: CMPXCHG.LOCK dword ptr [RDI],ECX *)
(*    1671422: CMPXCHG.LOCK dword ptr [RDI],ECX *)
| 0x1980fe => Some (4,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe5980) (Var (V_TEMP 0x6b00)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xe5980)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xe5a80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0xe5a80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))) $;
	If (Var R_ZF) (
		Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RCX)) $;
		Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
	) (* else *) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x00198102: JNZ 0x001980fa *)
(*    1671426: JNZ 0x001980fa *)
| 0x198102 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1980fa 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198104: MOVSX EDX,word ptr [RDI + 0x14] *)
(*    1671428: MOVSX EDX,word ptr [RDI + 0x14] *)
| 0x198104 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x14 64)) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 2) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_SIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198108: MOV EAX,EBX *)
(*    1671432: MOV EAX,EBX *)
| 0x198108 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RBX))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0019810a: MOV ESI,0x8 *)
(*    1671434: MOV ESI,0x8 *)
| 0x19810a => Some (5,
	Move R_RSI (Word 0x8 64)
)

(* 0x0019810f: SUB EAX,EDX *)
(*    1671439: SUB EAX,EDX *)
| 0x19810f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198111: MOV ECX,EDX *)
(*    1671441: MOV ECX,EDX *)
| 0x198111 => Some (2,
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00198113: CDQ *)
(*    1671443: CDQ *)
| 0x198113 => Some (1,
	Move (V_TEMP 0x3d700) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 63 32 (Var (V_TEMP 0x3d700)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198114: IDIV ESI *)
(*    1671444: IDIV ESI *)
| 0x198114 => Some (2,
	Move (V_TEMP 0x49700) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move (V_TEMP 0x49780) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x49800) (BinOp OP_LSHIFT (Var (V_TEMP 0x49780)) (Word 32 64)) $;
	Move (V_TEMP 0x49880) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49980) (BinOp OP_OR (Var (V_TEMP 0x49800)) (Var (V_TEMP 0x49880))) $;
	Move (V_TEMP 0x49a80) (BinOp OP_SDIVIDE (Var (V_TEMP 0x49980)) (Var (V_TEMP 0x49700))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var (V_TEMP 0x49a80)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49c00) (BinOp OP_SMOD (Var (V_TEMP 0x49980)) (Var (V_TEMP 0x49700))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var (V_TEMP 0x49c00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198116: ADD ECX,EAX *)
(*    1671446: ADD ECX,EAX *)
| 0x198116 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RAX))) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RAX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198118: MOV word ptr [RDI + 0x14],CX *)
(*    1671448: MOV word ptr [RDI + 0x14],CX *)
| 0x198118 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x14 64)) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x0019811c: JMP 0x0019807e *)
(*    1671452: JMP 0x0019807e *)
| 0x19811c => Some (5,
	Jmp (Word 0x19807e 64)
)

(* 0x00198121: MOV EDX,dword ptr FS:[0x2d0] *)
(*    1671457: MOV EDX,dword ptr FS:[0x2d0] *)
| 0x198121 => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x2d0 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00198129: MOV EAX,dword ptr [RDI + 0x10] *)
(*    1671465: MOV EAX,dword ptr [RDI + 0x10] *)
| 0x198129 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x0019812c: AND EAX,0x7f *)
(*    1671468: AND EAX,0x7f *)
| 0x19812c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x7f 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0019812f: CMP EAX,0x2 *)
(*    1671471: CMP EAX,0x2 *)
| 0x19812f => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x2 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198132: JNZ 0x0019818d *)
(*    1671474: JNZ 0x0019818d *)
| 0x198132 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x19818d 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198134: CMP dword ptr [RDI + 0x8],EDX *)
(*    1671476: CMP dword ptr [RDI + 0x8],EDX *)
| 0x198134 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x3ef80) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198137: JNZ 0x00197f22 *)
(*    1671479: JNZ 0x00197f22 *)
| 0x198137 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x197f22 64)
	) (* else *) (
		Nop
	)
)

(* 0x0019813d: MOV EAX,0x23 *)
(*    1671485: MOV EAX,0x23 *)
| 0x19813d => Some (5,
	Move R_RAX (Word 0x23 64)
)

(* 0x00198142: JMP 0x00197f67 *)
(*    1671490: JMP 0x00197f67 *)
| 0x198142 => Some (5,
	Jmp (Word 0x197f67 64)
)

(* 0x00198147: XOR EAX,EAX *)
(*    1671495: XOR EAX,EAX *)
| 0x198147 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198149: MOV EDX,0x1 *)
(*    1671497: MOV EDX,0x1 *)
| 0x198149 => Some (5,
	Move R_RDX (Word 0x1 64)
)

(* 0x0019814e: CMPXCHG.LOCK dword ptr [RDI],EDX *)
(*    1671502: CMPXCHG.LOCK dword ptr [RDI],EDX *)
| 0x19814e => Some (4,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe5980) (Var (V_TEMP 0x6b00)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xe5980)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xe5a80) (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe5a80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0xe5a80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8)))) $;
	If (Var R_ZF) (
		Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDX)) $;
		Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
	) (* else *) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0xe5980))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x00198152: JZ 0x00198104 *)
(*    1671506: JZ 0x00198104 *)
| 0x198152 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x198104 64)
	) (* else *) (
		Nop
	)
)

(* 0x00198154: MOV ESI,dword ptr [RDI + 0x10] *)
(*    1671508: MOV ESI,dword ptr [RDI + 0x10] *)
| 0x198154 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00198157: MOV qword ptr [RSP + 0x8],RDI *)
(*    1671511: MOV qword ptr [RSP + 0x8],RDI *)
| 0x198157 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0019815c: AND ESI,0x80 *)
(*    1671516: AND ESI,0x80 *)
| 0x19815c => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0x80 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00198162: CALL 0x00191290 *)
(*    1671522: CALL 0x00191290 *)
| 0x198162 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x198167 64) LittleE 8) $;
	Jmp (Word 0x191290 64)
)

(* 0x00198167: MOV RDI,qword ptr [RSP + 0x8] *)
(*    1671527: MOV RDI,qword ptr [RSP + 0x8] *)
| 0x198167 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x0019816c: JMP 0x00198104 *)
(*    1671532: JMP 0x00198104 *)
| 0x19816c => Some (2,
	Jmp (Word 0x198104 64)
)

(* 0x0019816e: LEA RCX,[0x2e1840] *)
(*    1671534: LEA RCX,[0x2e1840] *)
| 0x19816e => Some (7,
	Move R_RCX (Word 0x2e1840 64)
)

(* 0x00198175: MOV EDX,0x82 *)
(*    1671541: MOV EDX,0x82 *)
| 0x198175 => Some (5,
	Move R_RDX (Word 0x82 64)
)

(* 0x0019817a: LEA RSI,[0x2d956e] *)
(*    1671546: LEA RSI,[0x2d956e] *)
| 0x19817a => Some (7,
	Move R_RSI (Word 0x2d956e 64)
)

(* 0x00198181: LEA RDI,[0x2d9599] *)
(*    1671553: LEA RDI,[0x2d9599] *)
| 0x198181 => Some (7,
	Move R_RDI (Word 0x2d9599 64)
)

(* 0x00198188: CALL 0x00139e50 *)
(*    1671560: CALL 0x00139e50 *)
| 0x198188 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x19818d 64) LittleE 8) $;
	Jmp (Word 0x139e50 64)
)

(* 0x0019818d: LEA RCX,[0x2e1840] *)
(*    1671565: LEA RCX,[0x2e1840] *)
| 0x19818d => Some (7,
	Move R_RCX (Word 0x2e1840 64)
)

(* 0x00198194: MOV EDX,0xa0 *)
(*    1671572: MOV EDX,0xa0 *)
| 0x198194 => Some (5,
	Move R_RDX (Word 0xa0 64)
)

(* 0x00198199: LEA RSI,[0x2d956e] *)
(*    1671577: LEA RSI,[0x2d956e] *)
| 0x198199 => Some (7,
	Move R_RSI (Word 0x2d956e 64)
)

(* 0x001981a0: LEA RDI,[0x2ddea0] *)
(*    1671584: LEA RDI,[0x2ddea0] *)
| 0x1981a0 => Some (7,
	Move R_RDI (Word 0x2ddea0 64)
)

(* 0x001981a7: CALL 0x00139e50 *)
(*    1671591: CALL 0x00139e50 *)
| 0x1981a7 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1981ac 64) LittleE 8) $;
	Jmp (Word 0x139e50 64)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx pthread_mutex_lock_amd64.
Proof. Picinae_typecheck. Qed.
