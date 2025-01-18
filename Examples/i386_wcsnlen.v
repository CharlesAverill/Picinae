Require Import Picinae_i386.
Require Import NArith.
Open Scope N.

Definition i386_wcsnlen : program := fun _ a => match a with

(* 0xc0000040: pushl %ebx *)
| 0 => Some (1,
    Move (V_TEMP 0 (* v69 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 0 (* v69 *))) LittleE 4)
  )

(* 0xc0000041: movl 0xc(%esp), %ecx *)
| 1 => Some (4,
    Move R_ECX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 12 32)) LittleE 4)
  )

(* 0xc0000045: movl 0x8(%esp), %ebx *)
| 5 => Some (4,
    Move R_EBX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 8 32)) LittleE 4)
  )

(* 0xc0000049: testl %ecx, %ecx *)
| 9 => Some (2,
    Move (V_TEMP 1 (* v70 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 2 (* v71 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v70 *))) (Word 4 32)) (Var (V_TEMP 1 (* v70 *)))) (Let (V_TEMP 2 (* v71 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v71 *))) (Word 2 32)) (Var (V_TEMP 2 (* v71 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v71 *))) (Word 1 32)) (Var (V_TEMP 2 (* v71 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 1 (* v70 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 1 (* v70 *))))
  )

(* 0xc000004b: je 0x63 *)
| 11 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 112 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000004d: movl (%ebx), %edx *)
| 13 => Some (2,
    Move R_EDX (Load (Var V_MEM32) (Var R_EBX) LittleE 4)
  )

(* 0xc000004f: testl %edx, %edx *)
| 15 => Some (2,
    Move (V_TEMP 3 (* v93 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 4 (* v94 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v93 *))) (Word 4 32)) (Var (V_TEMP 3 (* v93 *)))) (Let (V_TEMP 4 (* v94 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v94 *))) (Word 2 32)) (Var (V_TEMP 4 (* v94 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v94 *))) (Word 1 32)) (Var (V_TEMP 4 (* v94 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 3 (* v93 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 3 (* v93 *))))
  )

(* 0xc0000051: je 0x5d *)
| 17 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 112 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000053: cmpl $0x1, %ecx *)
| 19 => Some (3,
    Move (V_TEMP 5 (* v78 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 5 (* v78 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 5 (* v78 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 6 (* v79 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v78 *))) (Word 4 32)) (Var (V_TEMP 5 (* v78 *)))) (Let (V_TEMP 6 (* v79 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v79 *))) (Word 2 32)) (Var (V_TEMP 6 (* v79 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v79 *))) (Word 1 32)) (Var (V_TEMP 6 (* v79 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* v78 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 5 (* v78 *))))
  )

(* 0xc0000056: je 0x5c *)
| 22 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 116 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000058: movl 0x4(%ebx), %eax *)
| 24 => Some (3,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EBX) (Word 4 32)) LittleE 4)
  )

(* 0xc000005b: testl %eax, %eax *)
| 27 => Some (2,
    Move (V_TEMP 7 (* v72 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* v73 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v72 *))) (Word 4 32)) (Var (V_TEMP 7 (* v72 *)))) (Let (V_TEMP 8 (* v73 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v73 *))) (Word 2 32)) (Var (V_TEMP 8 (* v73 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v73 *))) (Word 1 32)) (Var (V_TEMP 8 (* v73 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 7 (* v72 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 7 (* v72 *))))
  )

(* 0xc000005d: je 0x55 *)
| 29 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 116 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000005f: cmpl $0x2, %ecx *)
| 31 => Some (3,
    Move (V_TEMP 9 (* v76 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 9 (* v76 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 9 (* v76 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 2 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 10 (* v77 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v76 *))) (Word 4 32)) (Var (V_TEMP 9 (* v76 *)))) (Let (V_TEMP 10 (* v77 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* v77 *))) (Word 2 32)) (Var (V_TEMP 10 (* v77 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* v77 *))) (Word 1 32)) (Var (V_TEMP 10 (* v77 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 9 (* v76 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 9 (* v76 *))))
  )

(* 0xc0000062: je 0x57 *)
| 34 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 123 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000064: movl $0x2, %edx *)
| 36 => Some (5,
    Move R_EDX (Word 2 32)
  )

(* 0xc0000069: jmp 0x3a *)
| 41 => Some (2,
    Jmp (Word 101 32)
  )

(* 0xc0000070: cmpl $0x3, %ecx *)
| 48 => Some (3,
    Move (V_TEMP 11 (* v74 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 3 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 11 (* v74 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 11 (* v74 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 3 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 12 (* v75 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v74 *))) (Word 4 32)) (Var (V_TEMP 11 (* v74 *)))) (Let (V_TEMP 12 (* v75 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 12 (* v75 *))) (Word 2 32)) (Var (V_TEMP 12 (* v75 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 12 (* v75 *))) (Word 1 32)) (Var (V_TEMP 12 (* v75 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 11 (* v74 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 11 (* v74 *))))
  )

(* 0xc0000073: leal 0x1(%edx), %eax *)
| 51 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) (Word 1 32)))
  )

(* 0xc0000076: je 0x36 *)
| 54 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000078: cmpl $0x0, 0x4(%ebx,%edx,4) *)
| 56 => Some (5,
    Move (V_TEMP 13 (* v95 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 4 32)) LittleE 4) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 4 32)) LittleE 4) (Word 0 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 4 32)) LittleE 4) (Word 0 32)) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 4 32)) LittleE 4) (Var (V_TEMP 13 (* v95 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (Var (V_TEMP 13 (* v95 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 4 32)) LittleE 4)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 14 (* v96 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v95 *))) (Word 4 32)) (Var (V_TEMP 13 (* v95 *)))) (Let (V_TEMP 14 (* v96 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* v96 *))) (Word 2 32)) (Var (V_TEMP 14 (* v96 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* v96 *))) (Word 1 32)) (Var (V_TEMP 14 (* v96 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 13 (* v95 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 13 (* v95 *))))
  )

(* 0xc000007d: je 0x2f *)
| 61 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007f: subl $0x4, %ecx *)
| 63 => Some (3,
    Move (V_TEMP 15 (* v97 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 15 (* v97 *))) (Word 4 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 15 (* v97 *))) (Word 4 32)) (BinOp OP_XOR (Var (V_TEMP 15 (* v97 *))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 15 (* v97 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 16 (* v99 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 16 (* v99 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* v99 *))) (Word 2 32)) (Var (V_TEMP 16 (* v99 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* v99 *))) (Word 1 32)) (Var (V_TEMP 16 (* v99 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc0000082: leal 0x2(%edx), %eax *)
| 66 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) (Word 2 32)))
  )

(* 0xc0000085: je 0x27 *)
| 69 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000087: cmpl $0x0, 0x8(%ebx,%edx,4) *)
| 71 => Some (5,
    Move (V_TEMP 17 (* v89 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 8 32)) LittleE 4) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 8 32)) LittleE 4) (Word 0 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 8 32)) LittleE 4) (Word 0 32)) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 8 32)) LittleE 4) (Var (V_TEMP 17 (* v89 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (Var (V_TEMP 17 (* v89 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 8 32)) LittleE 4)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 18 (* v90 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v89 *))) (Word 4 32)) (Var (V_TEMP 17 (* v89 *)))) (Let (V_TEMP 18 (* v90 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v90 *))) (Word 2 32)) (Var (V_TEMP 18 (* v90 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v90 *))) (Word 1 32)) (Var (V_TEMP 18 (* v90 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 17 (* v89 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 17 (* v89 *))))
  )

(* 0xc000008c: je 0x20 *)
| 76 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000008e: cmpl $0x1, %ecx *)
| 78 => Some (3,
    Move (V_TEMP 19 (* v91 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 19 (* v91 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 19 (* v91 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 20 (* v92 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v91 *))) (Word 4 32)) (Var (V_TEMP 19 (* v91 *)))) (Let (V_TEMP 20 (* v92 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v92 *))) (Word 2 32)) (Var (V_TEMP 20 (* v92 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v92 *))) (Word 1 32)) (Var (V_TEMP 20 (* v92 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 19 (* v91 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 19 (* v91 *))))
  )

(* 0xc0000091: leal 0x3(%edx), %eax *)
| 81 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) (Word 3 32)))
  )

(* 0xc0000094: je 0x18 *)
| 84 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000096: cmpl $0x0, 0xc(%ebx,%edx,4) *)
| 86 => Some (5,
    Move (V_TEMP 21 (* v80 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 12 32)) LittleE 4) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 12 32)) LittleE 4) (Word 0 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 12 32)) LittleE 4) (Word 0 32)) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 12 32)) LittleE 4) (Var (V_TEMP 21 (* v80 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (Var (V_TEMP 21 (* v80 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32))) (Word 12 32)) LittleE 4)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 22 (* v81 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 21 (* v80 *))) (Word 4 32)) (Var (V_TEMP 21 (* v80 *)))) (Let (V_TEMP 22 (* v81 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v81 *))) (Word 2 32)) (Var (V_TEMP 22 (* v81 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v81 *))) (Word 1 32)) (Var (V_TEMP 22 (* v81 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 21 (* v80 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 21 (* v80 *))))
  )

(* 0xc000009b: je 0x11 *)
| 91 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 110 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009d: addl $0x4, %edx *)
| 93 => Some (3,
    Move (V_TEMP 23 (* v83 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 23 (* v83 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 23 (* v83 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 23 (* v83 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 23 (* v83 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 24 (* v85 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 24 (* v85 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v85 *))) (Word 2 32)) (Var (V_TEMP 24 (* v85 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v85 *))) (Word 1 32)) (Var (V_TEMP 24 (* v85 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc00000a0: cmpl $0x2, %ecx *)
| 96 => Some (3,
    Move (V_TEMP 25 (* v86 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Word 2 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 25 (* v86 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 25 (* v86 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Word 2 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 26 (* v87 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* v86 *))) (Word 4 32)) (Var (V_TEMP 25 (* v86 *)))) (Let (V_TEMP 26 (* v87 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v87 *))) (Word 2 32)) (Var (V_TEMP 26 (* v87 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v87 *))) (Word 1 32)) (Var (V_TEMP 26 (* v87 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 25 (* v86 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 25 (* v86 *))))
  )

(* 0xc00000a3: je 0x7 *)
| 99 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 108 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a5: movl (%ebx,%edx,4), %eax *)
| 101 => Some (3,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EBX) (BinOp OP_LSHIFT (Var R_EDX) (Word 2 32))) LittleE 4)
  )

(* 0xc00000a8: testl %eax, %eax *)
| 104 => Some (2,
    Move (V_TEMP 27 (* v67 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 28 (* v68 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 27 (* v67 *))) (Word 4 32)) (Var (V_TEMP 27 (* v67 *)))) (Let (V_TEMP 28 (* v68 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v68 *))) (Word 2 32)) (Var (V_TEMP 28 (* v68 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v68 *))) (Word 1 32)) (Var (V_TEMP 28 (* v68 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 27 (* v67 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 27 (* v67 *))))
  )

(* 0xc00000aa: jne -0x3c *)
| 106 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 48 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000ac: movl %edx, %eax *)
| 108 => Some (2,
    Move R_EAX (Var R_EDX)
  )

(* 0xc00000ae: popl %ebx *)
| 110 => Some (1,
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00000af: retl *)
| 111 => Some (1,
    Move (V_TEMP 29 (* v82 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 29 (* v82 *)))
  )

(* 0xc00000b0: xorl %eax, %eax *)
| 112 => Some (2,
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc00000b2: popl %ebx *)
| 114 => Some (1,
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00000b3: retl *)
| 115 => Some (1,
    Move (V_TEMP 30 (* v88 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 30 (* v88 *)))
  )

(* 0xc00000b4: movl $0x1, %eax *)
| 116 => Some (5,
    Move R_EAX (Word 1 32)
  )

(* 0xc00000b9: popl %ebx *)
| 121 => Some (1,
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00000ba: retl *)
| 122 => Some (1,
    Move (V_TEMP 31 (* v100 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 31 (* v100 *)))
  )

(* 0xc00000bb: movl $0x2, %eax *)
| 123 => Some (5,
    Move R_EAX (Word 2 32)
  )

(* 0xc00000c0: popl %ebx *)
| 128 => Some (1,
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00000c1: retl *)
| 129 => Some (1,
    Move (V_TEMP 32 (* v101 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 32 (* v101 *)))
  )

| _ => None
end.
