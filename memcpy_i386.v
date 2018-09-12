Require Import Picinae_i386.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0xc0000040: movl %edi, %eax *)
| 0 => Some (2,
    Move R_EAX (Var R_EDI)
  )

(* 0xc0000042: movl 0x4(%esp), %edi *)
| 2 => Some (4,
    Move R_EDI (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) LittleE 4)
  )

(* 0xc0000046: movl %esi, %edx *)
| 6 => Some (2,
    Move R_EDX (Var R_ESI)
  )

(* 0xc0000048: movl 0x8(%esp), %esi *)
| 8 => Some (4,
    Move R_ESI (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 8 32)) LittleE 4)
  )

(* 0xc000004c: movl %edi, %ecx *)
| 12 => Some (2,
    Move R_ECX (Var R_EDI)
  )

(* 0xc000004e: xorl %esi, %ecx *)
| 14 => Some (2, 
    Move R_ECX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 0 (* v76 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 0 (* v76 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 0 (* v76 *))) (Word 2 32)) (Var (V_TEMP 0 (* v76 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 0 (* v76 *))) (Word 1 32)) (Var (V_TEMP 0 (* v76 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc0000050: andl $0x3, %ecx *)
| 16 => Some (3, 
    Move R_ECX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 1 (* v78 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 1 (* v78 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v78 *))) (Word 2 32)) (Var (V_TEMP 1 (* v78 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v78 *))) (Word 1 32)) (Var (V_TEMP 1 (* v78 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc0000053: movl 0xc(%esp), %ecx *)
| 19 => Some (4,
    Move R_ECX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 12 32)) LittleE 4)
  )

(* 0xc0000057: cld *)
| 23 => Some (1,
    Move R_DF (Word 0 1)
  )

(* 0xc0000058: jne 0x3c *)
| 24 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 86 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000005a: cmpl $0x3, %ecx *)
| 26 => Some (3, 
    Move (V_TEMP 2 (* v92 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 2 (* v92 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 2 (* v92 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 3 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* v93 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v92 *))) (Word 4 32)) (Var (V_TEMP 2 (* v92 *)))) (Let (V_TEMP 3 (* v93 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v93 *))) (Word 2 32)) (Var (V_TEMP 3 (* v93 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v93 *))) (Word 1 32)) (Var (V_TEMP 3 (* v93 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v92 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 2 (* v92 *))))
  )

(* 0xc000005d: jbe 0x37 *)
| 29 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 86 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000005f: testl $0x3, %esi *)
| 31 => Some (6, 
    Move (V_TEMP 4 (* v80 *)) (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ESI)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 5 (* v81 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v80 *))) (Word 4 32)) (Var (V_TEMP 4 (* v80 *)))) (Let (V_TEMP 5 (* v81 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v81 *))) (Word 2 32)) (Var (V_TEMP 5 (* v81 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v81 *))) (Word 1 32)) (Var (V_TEMP 5 (* v81 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v80 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 4 (* v80 *))))
  )

(* 0xc0000065: je 0x16 *)
| 37 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 61 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000067: movsb (%esi), %es:(%edi) *)
| 39 => Some (1, 
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) LittleE 1) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 1 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967295 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 1 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967295 32))
    )
  )

(* 0xc0000068: decl %ecx *)
| 40 => Some (1, 
    Move (V_TEMP 6 (* v116 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 6 (* v116 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 6 (* v116 *))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 6 (* v116 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v117 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 7 (* v117 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v117 *))) (Word 2 32)) (Var (V_TEMP 7 (* v117 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v117 *))) (Word 1 32)) (Var (V_TEMP 7 (* v117 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc0000069: testl $0x3, %esi *)
| 41 => Some (6, 
    Move (V_TEMP 8 (* v120 *)) (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ESI)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 9 (* v121 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v120 *))) (Word 4 32)) (Var (V_TEMP 8 (* v120 *)))) (Let (V_TEMP 9 (* v121 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v121 *))) (Word 2 32)) (Var (V_TEMP 9 (* v121 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v121 *))) (Word 1 32)) (Var (V_TEMP 9 (* v121 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 8 (* v120 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 8 (* v120 *))))
  )

(* 0xc000006f: je 0xc *)
| 47 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 61 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000071: movsb (%esi), %es:(%edi) *)
| 49 => Some (1, 
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) LittleE 1) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 1 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967295 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 1 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967295 32))
    )
  )

(* 0xc0000072: decl %ecx *)
| 50 => Some (1, 
    Move (V_TEMP 10 (* v100 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 10 (* v100 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 10 (* v100 *))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 10 (* v100 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 11 (* v101 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 11 (* v101 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v101 *))) (Word 2 32)) (Var (V_TEMP 11 (* v101 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v101 *))) (Word 1 32)) (Var (V_TEMP 11 (* v101 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc0000073: testl $0x3, %esi *)
| 51 => Some (6, 
    Move (V_TEMP 12 (* v104 *)) (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ESI)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 13 (* v105 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 12 (* v104 *))) (Word 4 32)) (Var (V_TEMP 12 (* v104 *)))) (Let (V_TEMP 13 (* v105 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v105 *))) (Word 2 32)) (Var (V_TEMP 13 (* v105 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v105 *))) (Word 1 32)) (Var (V_TEMP 13 (* v105 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v104 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 12 (* v104 *))))
  )

(* 0xc0000079: je 0x2 *)
| 57 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 61 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007b: movsb (%esi), %es:(%edi) *)
| 59 => Some (1, 
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) LittleE 1) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 1 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967295 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 1 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967295 32))
    )
  )

(* 0xc000007c: decl %ecx *)
| 60 => Some (1, 
    Move (V_TEMP 14 (* v96 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 14 (* v96 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 14 (* v96 *))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 14 (* v96 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 15 (* v97 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 15 (* v97 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v97 *))) (Word 2 32)) (Var (V_TEMP 15 (* v97 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v97 *))) (Word 1 32)) (Var (V_TEMP 15 (* v97 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc000007d: pushl %eax *)
| 61 => Some (1, 
    Move (V_TEMP 16 (* v108 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 16 (* v108 *))) LittleE 4)
  )

(* 0xc000007e: movl %ecx, %eax *)
| 62 => Some (2,
    Move R_EAX (Var R_ECX)
  )

(* 0xc0000080: shrl $0x2, %ecx *)
| 64 => Some (3, 
    Move (V_TEMP 17 (* tmp110 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 17 (* tmp110 *))) (Word 32 32)) (BinOp OP_AND (Word 2 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 18 (* v111 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 18 (* v111 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v111 *))) (Word 2 32)) (Var (V_TEMP 18 (* v111 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v111 *))) (Word 1 32)) (Var (V_TEMP 18 (* v111 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Unknown 1)
  )

(* 0xc0000083: andl $0x3, %eax *)
| 67 => Some (3, 
    Move R_EAX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EAX)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 19 (* v114 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 19 (* v114 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v114 *))) (Word 2 32)) (Var (V_TEMP 19 (* v114 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v114 *))) (Word 1 32)) (Var (V_TEMP 19 (* v114 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc0000086: movsl (%esi), %es:(%edi) *)
| 70 => Some (2, 
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 72 32)
    ) (* else *) (
      Nop
    ) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 4) LittleE 4) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967292 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967292 32))
    ) $;
    Move R_ECX (BinOp OP_MINUS (Var R_ECX) (Word 1 32)) $;
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 72 32)
    ) (* else *) (
      Nop
    ) $;
    Jmp (Word 70 32)
  )

(* 0xc0000088: movl %eax, %ecx *)
| 72 => Some (2,
    Move R_ECX (Var R_EAX)
  )

(* 0xc000008a: movsb (%esi), %es:(%edi) *)
| 74 => Some (2, 
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 76 32)
    ) (* else *) (
      Nop
    ) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) LittleE 1) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 1 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967295 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 1 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967295 32))
    ) $;
    Move R_ECX (BinOp OP_MINUS (Var R_ECX) (Word 1 32)) $;
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 76 32)
    ) (* else *) (
      Nop
    ) $;
    Jmp (Word 74 32)
  )

(* 0xc000008c: popl %eax *)
| 76 => Some (1, 
    Move R_EAX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc000008d: movl %eax, %edi *)
| 77 => Some (2,
    Move R_EDI (Var R_EAX)
  )

(* 0xc000008f: movl %edx, %esi *)
| 79 => Some (2,
    Move R_ESI (Var R_EDX)
  )

(* 0xc0000091: movl 0x4(%esp), %eax *)
| 81 => Some (4,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) LittleE 4)
  )

(* 0xc0000095: retl *)
| 85 => Some (1, 
    Move (V_TEMP 20 (* v74 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 20 (* v74 *)))
  )

(* 0xc0000096: shrl %ecx *)
| 86 => Some (2, 
    Move (V_TEMP 21 (* tmp84 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 21 (* tmp84 *))) (Word 32 32)) (BinOp OP_AND (Word 1 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 22 (* v85 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 22 (* v85 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v85 *))) (Word 2 32)) (Var (V_TEMP 22 (* v85 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v85 *))) (Word 1 32)) (Var (V_TEMP 22 (* v85 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Cast CAST_HIGH 1 (Var (V_TEMP 21 (* tmp84 *))))
  )

(* 0xc0000098: jae 0x1 *)
| 88 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 91 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009a: movsb (%esi), %es:(%edi) *)
| 90 => Some (1, 
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) LittleE 1) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 1 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967295 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 1 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967295 32))
    )
  )

(* 0xc000009b: shrl %ecx *)
| 91 => Some (2, 
    Move (V_TEMP 23 (* tmp88 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 23 (* tmp88 *))) (Word 32 32)) (BinOp OP_AND (Word 1 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 24 (* v89 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 24 (* v89 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v89 *))) (Word 2 32)) (Var (V_TEMP 24 (* v89 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v89 *))) (Word 1 32)) (Var (V_TEMP 24 (* v89 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Cast CAST_HIGH 1 (Var (V_TEMP 23 (* tmp88 *))))
  )

(* 0xc000009d: jae 0x2 *)
| 93 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 97 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009f: movsw (%esi), %es:(%edi) *)
| 95 => Some (2, 
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 2) LittleE 2) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 2 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967294 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 2 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967294 32))
    )
  )

(* 0xc00000a1: movsl (%esi), %es:(%edi) *)
| 97 => Some (2, 
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 99 32)
    ) (* else *) (
      Nop
    ) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Load (Var V_MEM32) (Var R_ESI) LittleE 4) LittleE 4) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4 32))
    ) (* else *) (
      Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 4294967292 32))
    ) $;
    If (BinOp OP_EQ (Var R_DF) (Word 0 1)) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4 32))
    ) (* else *) (
      Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 4294967292 32))
    ) $;
    Move R_ECX (BinOp OP_MINUS (Var R_ECX) (Word 1 32)) $;
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 99 32)
    ) (* else *) (
      Nop
    ) $;
    Jmp (Word 97 32)
  )

(* 0xc00000a3: jmp -0x18 *)
| 99 => Some (2,
    Jmp (Word 77 32)
  )

| _ => None
end.
