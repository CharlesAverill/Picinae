Require Import Picinae_i386.
Require Import NArith.
Open Scope N.

Definition wcsspn_i386 : program := fun _ a => match a with

(* 0xc0000040: pushl %ebp *)
| 0 => Some (1, 
    Move (V_TEMP 0 (* v53 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 0 (* v53 *))) LittleE 4)
  )

(* 0xc0000041: pushl %edi *)
| 1 => Some (1, 
    Move (V_TEMP 1 (* v54 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 1 (* v54 *))) LittleE 4)
  )

(* 0xc0000042: xorl %eax, %eax *)
| 2 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000044: pushl %esi *)
| 4 => Some (1, 
    Move (V_TEMP 2 (* v55 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 2 (* v55 *))) LittleE 4)
  )

(* 0xc0000045: pushl %ebx *)
| 5 => Some (1, 
    Move (V_TEMP 3 (* v56 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 3 (* v56 *))) LittleE 4)
  )

(* 0xc0000046: movl 0x14(%esp), %edi *)
| 6 => Some (4,
    Move R_EDI (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 20 32)) LittleE 4)
  )

(* 0xc000004a: movl 0x18(%esp), %ebp *)
| 10 => Some (4,
    Move R_EBP (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 24 32)) LittleE 4)
  )

(* 0xc000004e: movl (%edi), %ebx *)
| 14 => Some (2,
    Move R_EBX (Load (Var V_MEM32) (Var R_EDI) LittleE 4)
  )

(* 0xc0000050: testl %ebx, %ebx *)
| 16 => Some (2, 
    Move (V_TEMP 4 (* v57 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 5 (* v58 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v57 *))) (Word 4 32)) (Var (V_TEMP 4 (* v57 *)))) (Let (V_TEMP 5 (* v58 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v58 *))) (Word 2 32)) (Var (V_TEMP 5 (* v58 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v58 *))) (Word 1 32)) (Var (V_TEMP 5 (* v58 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v57 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 4 (* v57 *))))
  )

(* 0xc0000052: je 0x29 *)
| 18 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 61 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000054: movl (%ebp), %esi *)
| 20 => Some (3,
    Move R_ESI (Load (Var V_MEM32) (Var R_EBP) LittleE 4)
  )

(* 0xc0000057: xorl %eax, %eax *)
| 23 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000059: leal (%esi), %esi *)
| 25 => Some (7,
    Move R_ESI (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Word 0 32)))
  )

(* 0xc0000060: testl %esi, %esi *)
| 32 => Some (2, 
    Move (V_TEMP 6 (* v69 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v70 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v69 *))) (Word 4 32)) (Var (V_TEMP 6 (* v69 *)))) (Let (V_TEMP 7 (* v70 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v70 *))) (Word 2 32)) (Var (V_TEMP 7 (* v70 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v70 *))) (Word 1 32)) (Var (V_TEMP 7 (* v70 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v69 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 6 (* v69 *))))
  )

(* 0xc0000062: je 0x19 *)
| 34 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 61 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000064: cmpl %ebx, %esi *)
| 36 => Some (2, 
    Move (V_TEMP 8 (* v61 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 8 (* v61 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 8 (* v61 *))) (Cast CAST_LOW 32 (Var R_ESI))) (Cast CAST_LOW 32 (Var R_EBX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 9 (* v62 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v61 *))) (Word 4 32)) (Var (V_TEMP 8 (* v61 *)))) (Let (V_TEMP 9 (* v62 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v62 *))) (Word 2 32)) (Var (V_TEMP 9 (* v62 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v62 *))) (Word 1 32)) (Var (V_TEMP 9 (* v62 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 8 (* v61 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 8 (* v61 *))))
  )

(* 0xc0000066: je 0x20 *)
| 38 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 72 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000068: movl %ebp, %edx *)
| 40 => Some (2,
    Move R_EDX (Var R_EBP)
  )

(* 0xc000006a: jmp 0x8 *)
| 42 => Some (2,
    Jmp (Word 52 32)
  )

(* 0xc0000070: cmpl %ebx, %ecx *)
| 48 => Some (2, 
    Move (V_TEMP 10 (* v59 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_EBX))) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 10 (* v59 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 10 (* v59 *))) (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 32 (Var R_EBX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 11 (* v60 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* v59 *))) (Word 4 32)) (Var (V_TEMP 10 (* v59 *)))) (Let (V_TEMP 11 (* v60 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v60 *))) (Word 2 32)) (Var (V_TEMP 11 (* v60 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v60 *))) (Word 1 32)) (Var (V_TEMP 11 (* v60 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v59 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 10 (* v59 *))))
  )

(* 0xc0000072: je 0x14 *)
| 50 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 72 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000074: addl $0x4, %edx *)
| 52 => Some (3, 
    Move (V_TEMP 12 (* v63 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 12 (* v63 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v63 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v63 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 12 (* v63 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 13 (* v65 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 13 (* v65 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v65 *))) (Word 2 32)) (Var (V_TEMP 13 (* v65 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v65 *))) (Word 1 32)) (Var (V_TEMP 13 (* v65 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc0000077: movl (%edx), %ecx *)
| 55 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EDX) LittleE 4)
  )

(* 0xc0000079: testl %ecx, %ecx *)
| 57 => Some (2, 
    Move (V_TEMP 14 (* v66 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 15 (* v67 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* v66 *))) (Word 4 32)) (Var (V_TEMP 14 (* v66 *)))) (Let (V_TEMP 15 (* v67 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v67 *))) (Word 2 32)) (Var (V_TEMP 15 (* v67 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v67 *))) (Word 1 32)) (Var (V_TEMP 15 (* v67 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 14 (* v66 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 14 (* v66 *))))
  )

(* 0xc000007b: jne -0xd *)
| 59 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 48 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007d: popl %ebx *)
| 61 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc000007e: popl %esi *)
| 62 => Some (1, 
    Move R_ESI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc000007f: popl %edi *)
| 63 => Some (1, 
    Move R_EDI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000080: popl %ebp *)
| 64 => Some (1, 
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000081: retl *)
| 65 => Some (1, 
    Move (V_TEMP 16 (* v68 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 16 (* v68 *)))
  )

(* 0xc0000088: addl $0x1, %eax *)
| 72 => Some (3, 
    Move (V_TEMP 17 (* v48 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 17 (* v48 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 17 (* v48 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 17 (* v48 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 17 (* v48 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 18 (* v50 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 18 (* v50 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v50 *))) (Word 2 32)) (Var (V_TEMP 18 (* v50 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v50 *))) (Word 1 32)) (Var (V_TEMP 18 (* v50 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc000008b: movl (%edi,%eax,4), %ebx *)
| 75 => Some (3,
    Move R_EBX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EDI) (BinOp OP_LSHIFT (Var R_EAX) (Word 2 32))) LittleE 4)
  )

(* 0xc000008e: testl %ebx, %ebx *)
| 78 => Some (2, 
    Move (V_TEMP 19 (* v51 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 20 (* v52 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v51 *))) (Word 4 32)) (Var (V_TEMP 19 (* v51 *)))) (Let (V_TEMP 20 (* v52 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v52 *))) (Word 2 32)) (Var (V_TEMP 20 (* v52 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v52 *))) (Word 1 32)) (Var (V_TEMP 20 (* v52 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 19 (* v51 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 19 (* v51 *))))
  )

(* 0xc0000090: jne -0x32 *)
| 80 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 32 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000092: popl %ebx *)
| 82 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000093: popl %esi *)
| 83 => Some (1, 
    Move R_ESI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000094: popl %edi *)
| 84 => Some (1, 
    Move R_EDI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000095: popl %ebp *)
| 85 => Some (1, 
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000096: retl *)
| 86 => Some (1, 
    Move (V_TEMP 21 (* v47 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 21 (* v47 *)))
  )

| _ => None
end.
