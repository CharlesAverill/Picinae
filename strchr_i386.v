Require Import Picinae_i386.
Require Import NArith.
Open Scope N.

Definition strchr_i386 : program := fun _ a => match a with

(* 0xc0000070: pushl %edi *)
| 0 => Some (1, 
    Move (V_TEMP 0 (* v327 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 0 (* v327 *))) LittleE 4)
  )

(* 0xc0000071: pushl %esi *)
| 1 => Some (1, 
    Move (V_TEMP 1 (* v328 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 1 (* v328 *))) LittleE 4)
  )

(* 0xc0000072: pushl %ebx *)
| 2 => Some (1, 
    Move (V_TEMP 2 (* v329 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 2 (* v329 *))) LittleE 4)
  )

(* 0xc0000073: pushl %ebp *)
| 3 => Some (1, 
    Move (V_TEMP 3 (* v330 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 3 (* v330 *))) LittleE 4)
  )

(* 0xc0000074: movl 0x14(%esp), %eax *)
| 4 => Some (4,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 20 32)) LittleE 4)
  )

(* 0xc0000078: movl 0x18(%esp), %edx *)
| 8 => Some (4,
    Move R_EDX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 24 32)) LittleE 4)
  )

(* 0xc000007c: movl %eax, %edi *)
| 12 => Some (2,
    Move R_EDI (Var R_EAX)
  )

(* 0xc000007e: xorl %ecx, %ecx *)
| 14 => Some (2, 
    Move R_ECX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000080: movb %dl, %dh *)
| 16 => Some (2,
    Move R_EDX (Concat (Cast CAST_HIGH 16 (Var R_EDX)) (Concat (Cast CAST_LOW 8 (Var R_EDX)) (Cast CAST_LOW 8 (Var R_EDX))))
  )

(* 0xc0000082: movb %dl, %cl *)
| 18 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Cast CAST_LOW 8 (Var R_EDX)))
  )

(* 0xc0000084: shll $0x10, %edx *)
| 20 => Some (3, 
    Move (V_TEMP 4 (* tmp331 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 16 32)) $;
    Move R_CF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 4 (* tmp331 *))) (BinOp OP_MINUS (Word 32 32) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32)))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 5 (* v332 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 5 (* v332 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v332 *))) (Word 2 32)) (Var (V_TEMP 5 (* v332 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v332 *))) (Word 1 32)) (Var (V_TEMP 5 (* v332 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Unknown 1)
  )

(* 0xc0000087: movb %cl, %ch *)
| 23 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 16 (Var R_ECX)) (Concat (Cast CAST_LOW 8 (Var R_ECX)) (Cast CAST_LOW 8 (Var R_ECX))))
  )

(* 0xc0000089: orl %ecx, %edx *)
| 25 => Some (2, 
    Move R_EDX (BinOp OP_OR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 6 (* v333 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 6 (* v333 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v333 *))) (Word 2 32)) (Var (V_TEMP 6 (* v333 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v333 *))) (Word 1 32)) (Var (V_TEMP 6 (* v333 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc000008b: andl $0x3, %edi *)
| 27 => Some (3, 
    Move R_EDI (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDI)) (Word 3 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v334 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 7 (* v334 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v334 *))) (Word 2 32)) (Var (V_TEMP 7 (* v334 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v334 *))) (Word 1 32)) (Var (V_TEMP 7 (* v334 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc000008e: je 0x41 *)
| 30 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 97 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000090: movb %dl, %cl *)
| 32 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Cast CAST_LOW 8 (Var R_EDX)))
  )

(* 0xc0000092: jp 0x29 *)
| 34 => Some (2,
    If (Var R_PF) (
      Jmp (Word 77 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000094: xorb (%eax), %cl *)
| 36 => Some (2, 
    Move R_ECX (Concat (Extract 31 8 (Var R_ECX)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* v316 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 4 8)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Let (V_TEMP 8 (* v316 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v316 *))) (Word 2 8)) (Var (V_TEMP 8 (* v316 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v316 *))) (Word 1 8)) (Var (V_TEMP 8 (* v316 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))))
  )

(* 0xc0000096: je 0x161 *)
| 38 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009c: xorb %dl, %cl *)
| 44 => Some (2, 
    Move R_ECX (Concat (Extract 31 8 (Var R_ECX)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 9 (* v426 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 4 8)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Let (V_TEMP 9 (* v426 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v426 *))) (Word 2 8)) (Var (V_TEMP 9 (* v426 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v426 *))) (Word 1 8)) (Var (V_TEMP 9 (* v426 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))))
  )

(* 0xc000009e: je 0x186 *)
| 46 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a4: movb 0x1(%eax), %cl *)
| 52 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 1 32)) LittleE 1))
  )

(* 0xc00000a7: incl %eax *)
| 55 => Some (1, 
    Move (V_TEMP 10 (* v373 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v373 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v373 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 10 (* v373 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 11 (* v374 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 11 (* v374 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v374 *))) (Word 2 32)) (Var (V_TEMP 11 (* v374 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v374 *))) (Word 1 32)) (Var (V_TEMP 11 (* v374 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000a8: cmpb %cl, %dl *)
| 56 => Some (2, 
    Move (V_TEMP 12 (* v375 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Var (V_TEMP 12 (* v375 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 12 (* v375 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 13 (* v376 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 12 (* v375 *))) (Word 4 8)) (Var (V_TEMP 12 (* v375 *)))) (Let (V_TEMP 13 (* v376 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v376 *))) (Word 2 8)) (Var (V_TEMP 13 (* v376 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v376 *))) (Word 1 8)) (Var (V_TEMP 13 (* v376 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v375 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 12 (* v375 *))))
  )

(* 0xc00000aa: je 0x14d *)
| 58 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b0: cmpb $0x0, %cl *)
| 64 => Some (3, 
    Move (V_TEMP 14 (* v377 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 14 (* v377 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 14 (* v377 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 15 (* v378 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* v377 *))) (Word 4 8)) (Var (V_TEMP 14 (* v377 *)))) (Let (V_TEMP 15 (* v378 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v378 *))) (Word 2 8)) (Var (V_TEMP 15 (* v378 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v378 *))) (Word 1 8)) (Var (V_TEMP 15 (* v378 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 14 (* v377 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 14 (* v377 *))))
  )

(* 0xc00000b3: je 0x171 *)
| 67 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b9: incl %eax *)
| 73 => Some (1, 
    Move (V_TEMP 16 (* v413 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v413 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v413 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 16 (* v413 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 17 (* v414 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 17 (* v414 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v414 *))) (Word 2 32)) (Var (V_TEMP 17 (* v414 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v414 *))) (Word 1 32)) (Var (V_TEMP 17 (* v414 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000ba: decl %edi *)
| 74 => Some (1, 
    Move (V_TEMP 18 (* v415 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move R_EDI (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDI)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 18 (* v415 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 18 (* v415 *))) (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 18 (* v415 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 19 (* v416 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 19 (* v416 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v416 *))) (Word 2 32)) (Var (V_TEMP 19 (* v416 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v416 *))) (Word 1 32)) (Var (V_TEMP 19 (* v416 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc00000bb: jne 0x14 *)
| 75 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 97 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000bd: movb (%eax), %cl *)
| 77 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (Var R_EAX) LittleE 1))
  )

(* 0xc00000bf: cmpb %cl, %dl *)
| 79 => Some (2, 
    Move (V_TEMP 20 (* v317 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX))) (Var (V_TEMP 20 (* v317 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 20 (* v317 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 21 (* v318 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v317 *))) (Word 4 8)) (Var (V_TEMP 20 (* v317 *)))) (Let (V_TEMP 21 (* v318 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 21 (* v318 *))) (Word 2 8)) (Var (V_TEMP 21 (* v318 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 21 (* v318 *))) (Word 1 8)) (Var (V_TEMP 21 (* v318 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 20 (* v317 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 20 (* v317 *))))
  )

(* 0xc00000c1: je 0x136 *)
| 81 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000c7: cmpb $0x0, %cl *)
| 87 => Some (3, 
    Move (V_TEMP 22 (* v446 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 22 (* v446 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 22 (* v446 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 23 (* v447 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v446 *))) (Word 4 8)) (Var (V_TEMP 22 (* v446 *)))) (Let (V_TEMP 23 (* v447 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 23 (* v447 *))) (Word 2 8)) (Var (V_TEMP 23 (* v447 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 23 (* v447 *))) (Word 1 8)) (Var (V_TEMP 23 (* v447 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 22 (* v446 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 22 (* v446 *))))
  )

(* 0xc00000ca: je 0x15a *)
| 90 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000d0: incl %eax *)
| 96 => Some (1, 
    Move (V_TEMP 24 (* v323 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* v323 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* v323 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 24 (* v323 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 25 (* v324 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 25 (* v324 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* v324 *))) (Word 2 32)) (Var (V_TEMP 25 (* v324 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* v324 *))) (Word 1 32)) (Var (V_TEMP 25 (* v324 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000d1: movl (%eax), %ecx *)
| 97 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0xc00000d3: movl $0xfefefeff, %ebp *)
| 99 => Some (5,
    Move R_EBP (Word 4278124287 32)
  )

(* 0xc00000d8: movl $0xfefefeff, %edi *)
| 104 => Some (5,
    Move R_EDI (Word 4278124287 32)
  )

(* 0xc00000dd: addl %ecx, %ebp *)
| 109 => Some (2, 
    Move (V_TEMP 26 (* v417 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move (V_TEMP 27 (* v418 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 27 (* v418 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 26 (* v417 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* v417 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 27 (* v418 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* v417 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 26 (* v417 *)))) (Var (V_TEMP 27 (* v418 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 28 (* v419 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 28 (* v419 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v419 *))) (Word 2 32)) (Var (V_TEMP 28 (* v419 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v419 *))) (Word 1 32)) (Var (V_TEMP 28 (* v419 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00000df: xorl %ecx, %ebp *)
| 111 => Some (2, 
    Move R_EBP (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 29 (* v452 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 29 (* v452 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 29 (* v452 *))) (Word 2 32)) (Var (V_TEMP 29 (* v452 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 29 (* v452 *))) (Word 1 32)) (Var (V_TEMP 29 (* v452 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00000e1: addl %ecx, %edi *)
| 113 => Some (2, 
    Move (V_TEMP 30 (* v453 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move (V_TEMP 31 (* v454 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EDI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 31 (* v454 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 30 (* v453 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v453 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 31 (* v454 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v453 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 30 (* v453 *)))) (Var (V_TEMP 31 (* v454 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 32 (* v455 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 32 (* v455 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 32 (* v455 *))) (Word 2 32)) (Var (V_TEMP 32 (* v455 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 32 (* v455 *))) (Word 1 32)) (Var (V_TEMP 32 (* v455 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc00000e3: leal 0x4(%eax), %eax *)
| 115 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) (Word 4 32)))
  )

(* 0xc00000e6: jae 0x116 *)
| 118 => Some (6,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000ec: movl %ecx, %ebx *)
| 124 => Some (2,
    Move R_EBX (Var R_ECX)
  )

(* 0xc00000ee: orl $0xfefefeff, %ebp *)
| 126 => Some (6, 
    Move R_EBP (BinOp OP_OR (Cast CAST_LOW 32 (Var R_EBP)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 33 (* v385 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 33 (* v385 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v385 *))) (Word 2 32)) (Var (V_TEMP 33 (* v385 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v385 *))) (Word 1 32)) (Var (V_TEMP 33 (* v385 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00000f4: addl $0x1, %ebp *)
| 132 => Some (3, 
    Move (V_TEMP 34 (* v386 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 34 (* v386 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 34 (* v386 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 34 (* v386 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 34 (* v386 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 35 (* v388 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 35 (* v388 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v388 *))) (Word 2 32)) (Var (V_TEMP 35 (* v388 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v388 *))) (Word 1 32)) (Var (V_TEMP 35 (* v388 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00000f7: jne 0x105 *)
| 135 => Some (6,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000fd: movl $0xfefefeff, %esi *)
| 141 => Some (5,
    Move R_ESI (Word 4278124287 32)
  )

(* 0xc0000102: xorl %edx, %ebx *)
| 146 => Some (2, 
    Move R_EBX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 36 (* v365 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 36 (* v365 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 36 (* v365 *))) (Word 2 32)) (Var (V_TEMP 36 (* v365 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 36 (* v365 *))) (Word 1 32)) (Var (V_TEMP 36 (* v365 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0xc0000104: movl (%eax), %ecx *)
| 148 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0xc0000106: addl %ebx, %esi *)
| 150 => Some (2, 
    Move (V_TEMP 37 (* v366 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move (V_TEMP 38 (* v367 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 38 (* v367 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 37 (* v366 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 37 (* v366 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 38 (* v367 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 37 (* v366 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 37 (* v366 *)))) (Var (V_TEMP 38 (* v367 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 39 (* v368 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 39 (* v368 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v368 *))) (Word 2 32)) (Var (V_TEMP 39 (* v368 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v368 *))) (Word 1 32)) (Var (V_TEMP 39 (* v368 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000108: movl $0xfefefeff, %edi *)
| 152 => Some (5,
    Move R_EDI (Word 4278124287 32)
  )

(* 0xc000010d: jae 0xd4 *)
| 157 => Some (6,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000113: movl %edi, %ebp *)
| 163 => Some (2,
    Move R_EBP (Var R_EDI)
  )

(* 0xc0000115: xorl %ebx, %esi *)
| 165 => Some (2, 
    Move R_ESI (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 40 (* v339 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 40 (* v339 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 40 (* v339 *))) (Word 2 32)) (Var (V_TEMP 40 (* v339 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 40 (* v339 *))) (Word 1 32)) (Var (V_TEMP 40 (* v339 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000117: addl %ecx, %ebp *)
| 167 => Some (2, 
    Move (V_TEMP 41 (* v340 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move (V_TEMP 42 (* v341 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 42 (* v341 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 41 (* v340 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 41 (* v340 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* v341 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 41 (* v340 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 41 (* v340 *)))) (Var (V_TEMP 42 (* v341 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 43 (* v342 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 43 (* v342 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 43 (* v342 *))) (Word 2 32)) (Var (V_TEMP 43 (* v342 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 43 (* v342 *))) (Word 1 32)) (Var (V_TEMP 43 (* v342 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc0000119: orl $0xfefefeff, %esi *)
| 169 => Some (6, 
    Move R_ESI (BinOp OP_OR (Cast CAST_LOW 32 (Var R_ESI)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 44 (* v343 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 44 (* v343 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 44 (* v343 *))) (Word 2 32)) (Var (V_TEMP 44 (* v343 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 44 (* v343 *))) (Word 1 32)) (Var (V_TEMP 44 (* v343 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc000011f: addl $0x1, %esi *)
| 175 => Some (3, 
    Move (V_TEMP 45 (* v344 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 45 (* v344 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 45 (* v344 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 45 (* v344 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 45 (* v344 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 46 (* v346 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 46 (* v346 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 46 (* v346 *))) (Word 2 32)) (Var (V_TEMP 46 (* v346 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 46 (* v346 *))) (Word 1 32)) (Var (V_TEMP 46 (* v346 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000122: jne 0xbf *)
| 178 => Some (6,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000128: xorl %ecx, %ebp *)
| 184 => Some (2, 
    Move R_EBP (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 47 (* v369 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 47 (* v369 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 47 (* v369 *))) (Word 2 32)) (Var (V_TEMP 47 (* v369 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 47 (* v369 *))) (Word 1 32)) (Var (V_TEMP 47 (* v369 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc000012a: addl %ecx, %edi *)
| 186 => Some (2, 
    Move (V_TEMP 48 (* v370 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move (V_TEMP 49 (* v371 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EDI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 49 (* v371 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 48 (* v370 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 48 (* v370 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 49 (* v371 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 48 (* v370 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 48 (* v370 *)))) (Var (V_TEMP 49 (* v371 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 50 (* v372 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 50 (* v372 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 50 (* v372 *))) (Word 2 32)) (Var (V_TEMP 50 (* v372 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 50 (* v372 *))) (Word 1 32)) (Var (V_TEMP 50 (* v372 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc000012c: leal 0x4(%eax), %eax *)
| 188 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) (Word 4 32)))
  )

(* 0xc000012f: jae 0xcd *)
| 191 => Some (6,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000135: movl %ecx, %ebx *)
| 197 => Some (2,
    Move R_EBX (Var R_ECX)
  )

(* 0xc0000137: orl $0xfefefeff, %ebp *)
| 199 => Some (6, 
    Move R_EBP (BinOp OP_OR (Cast CAST_LOW 32 (Var R_EBP)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 51 (* v308 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 51 (* v308 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 51 (* v308 *))) (Word 2 32)) (Var (V_TEMP 51 (* v308 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 51 (* v308 *))) (Word 1 32)) (Var (V_TEMP 51 (* v308 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc000013d: addl $0x1, %ebp *)
| 205 => Some (3, 
    Move (V_TEMP 52 (* v309 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 52 (* v309 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* v309 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* v309 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 52 (* v309 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 53 (* v311 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 53 (* v311 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 53 (* v311 *))) (Word 2 32)) (Var (V_TEMP 53 (* v311 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 53 (* v311 *))) (Word 1 32)) (Var (V_TEMP 53 (* v311 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc0000140: jne 0xbc *)
| 208 => Some (6,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000146: movl $0xfefefeff, %esi *)
| 214 => Some (5,
    Move R_ESI (Word 4278124287 32)
  )

(* 0xc000014b: xorl %edx, %ebx *)
| 219 => Some (2, 
    Move R_EBX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 54 (* v304 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 54 (* v304 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 54 (* v304 *))) (Word 2 32)) (Var (V_TEMP 54 (* v304 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 54 (* v304 *))) (Word 1 32)) (Var (V_TEMP 54 (* v304 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0xc000014d: movl (%eax), %ecx *)
| 221 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0xc000014f: addl %ebx, %esi *)
| 223 => Some (2, 
    Move (V_TEMP 55 (* v305 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move (V_TEMP 56 (* v306 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 56 (* v306 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 55 (* v305 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 55 (* v305 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 56 (* v306 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 55 (* v305 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 55 (* v305 *)))) (Var (V_TEMP 56 (* v306 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 57 (* v307 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 57 (* v307 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 57 (* v307 *))) (Word 2 32)) (Var (V_TEMP 57 (* v307 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 57 (* v307 *))) (Word 1 32)) (Var (V_TEMP 57 (* v307 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000151: movl $0xfefefeff, %edi *)
| 225 => Some (5,
    Move R_EDI (Word 4278124287 32)
  )

(* 0xc0000156: jae 0x8b *)
| 230 => Some (6,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000015c: movl %edi, %ebp *)
| 236 => Some (2,
    Move R_EBP (Var R_EDI)
  )

(* 0xc000015e: xorl %ebx, %esi *)
| 238 => Some (2, 
    Move R_ESI (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 58 (* v432 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 58 (* v432 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 58 (* v432 *))) (Word 2 32)) (Var (V_TEMP 58 (* v432 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 58 (* v432 *))) (Word 1 32)) (Var (V_TEMP 58 (* v432 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000160: addl %ecx, %ebp *)
| 240 => Some (2, 
    Move (V_TEMP 59 (* v433 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move (V_TEMP 60 (* v434 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 60 (* v434 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 59 (* v433 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59 (* v433 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 60 (* v434 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59 (* v433 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 59 (* v433 *)))) (Var (V_TEMP 60 (* v434 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 61 (* v435 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 61 (* v435 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 61 (* v435 *))) (Word 2 32)) (Var (V_TEMP 61 (* v435 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 61 (* v435 *))) (Word 1 32)) (Var (V_TEMP 61 (* v435 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc0000162: orl $0xfefefeff, %esi *)
| 242 => Some (6, 
    Move R_ESI (BinOp OP_OR (Cast CAST_LOW 32 (Var R_ESI)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 62 (* v436 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 62 (* v436 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 62 (* v436 *))) (Word 2 32)) (Var (V_TEMP 62 (* v436 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 62 (* v436 *))) (Word 1 32)) (Var (V_TEMP 62 (* v436 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000168: addl $0x1, %esi *)
| 248 => Some (3, 
    Move (V_TEMP 63 (* v437 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 63 (* v437 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 63 (* v437 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 63 (* v437 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 63 (* v437 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 64 (* v439 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 64 (* v439 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 64 (* v439 *))) (Word 2 32)) (Var (V_TEMP 64 (* v439 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 64 (* v439 *))) (Word 1 32)) (Var (V_TEMP 64 (* v439 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc000016b: jne 0x7a *)
| 251 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000016d: xorl %ecx, %ebp *)
| 253 => Some (2, 
    Move R_EBP (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 65 (* v422 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 65 (* v422 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 65 (* v422 *))) (Word 2 32)) (Var (V_TEMP 65 (* v422 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 65 (* v422 *))) (Word 1 32)) (Var (V_TEMP 65 (* v422 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc000016f: addl %ecx, %edi *)
| 255 => Some (2, 
    Move (V_TEMP 66 (* v423 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move (V_TEMP 67 (* v424 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EDI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 67 (* v424 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 66 (* v423 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 66 (* v423 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 67 (* v424 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 66 (* v423 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 66 (* v423 *)))) (Var (V_TEMP 67 (* v424 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 68 (* v425 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 68 (* v425 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 68 (* v425 *))) (Word 2 32)) (Var (V_TEMP 68 (* v425 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 68 (* v425 *))) (Word 1 32)) (Var (V_TEMP 68 (* v425 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc0000171: leal 0x4(%eax), %eax *)
| 257 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) (Word 4 32)))
  )

(* 0xc0000174: jae 0x88 *)
| 260 => Some (6,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000017a: movl %ecx, %ebx *)
| 266 => Some (2,
    Move R_EBX (Var R_ECX)
  )

(* 0xc000017c: orl $0xfefefeff, %ebp *)
| 268 => Some (6, 
    Move R_EBP (BinOp OP_OR (Cast CAST_LOW 32 (Var R_EBP)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 69 (* v349 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 69 (* v349 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 69 (* v349 *))) (Word 2 32)) (Var (V_TEMP 69 (* v349 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 69 (* v349 *))) (Word 1 32)) (Var (V_TEMP 69 (* v349 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc0000182: addl $0x1, %ebp *)
| 274 => Some (3, 
    Move (V_TEMP 70 (* v350 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 70 (* v350 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 70 (* v350 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 70 (* v350 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 70 (* v350 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 71 (* v352 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 71 (* v352 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 71 (* v352 *))) (Word 2 32)) (Var (V_TEMP 71 (* v352 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 71 (* v352 *))) (Word 1 32)) (Var (V_TEMP 71 (* v352 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc0000185: jne 0x7b *)
| 277 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000187: movl $0xfefefeff, %esi *)
| 279 => Some (5,
    Move R_ESI (Word 4278124287 32)
  )

(* 0xc000018c: xorl %edx, %ebx *)
| 284 => Some (2, 
    Move R_EBX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 72 (* v448 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 72 (* v448 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 72 (* v448 *))) (Word 2 32)) (Var (V_TEMP 72 (* v448 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 72 (* v448 *))) (Word 1 32)) (Var (V_TEMP 72 (* v448 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0xc000018e: movl (%eax), %ecx *)
| 286 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0xc0000190: addl %ebx, %esi *)
| 288 => Some (2, 
    Move (V_TEMP 73 (* v449 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move (V_TEMP 74 (* v450 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 74 (* v450 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 73 (* v449 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 73 (* v449 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 74 (* v450 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 73 (* v449 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 73 (* v449 *)))) (Var (V_TEMP 74 (* v450 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 75 (* v451 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 75 (* v451 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 75 (* v451 *))) (Word 2 32)) (Var (V_TEMP 75 (* v451 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 75 (* v451 *))) (Word 1 32)) (Var (V_TEMP 75 (* v451 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc0000192: movl $0xfefefeff, %edi *)
| 290 => Some (5,
    Move R_EDI (Word 4278124287 32)
  )

(* 0xc0000197: jae 0x4e *)
| 295 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000199: movl %edi, %ebp *)
| 297 => Some (2,
    Move R_EBP (Var R_EDI)
  )

(* 0xc000019b: xorl %ebx, %esi *)
| 299 => Some (2, 
    Move R_ESI (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 76 (* v357 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 76 (* v357 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 76 (* v357 *))) (Word 2 32)) (Var (V_TEMP 76 (* v357 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 76 (* v357 *))) (Word 1 32)) (Var (V_TEMP 76 (* v357 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc000019d: addl %ecx, %ebp *)
| 301 => Some (2, 
    Move (V_TEMP 77 (* v358 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move (V_TEMP 78 (* v359 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 78 (* v359 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 77 (* v358 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 77 (* v358 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 78 (* v359 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 77 (* v358 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 77 (* v358 *)))) (Var (V_TEMP 78 (* v359 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 79 (* v360 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 79 (* v360 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 79 (* v360 *))) (Word 2 32)) (Var (V_TEMP 79 (* v360 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 79 (* v360 *))) (Word 1 32)) (Var (V_TEMP 79 (* v360 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc000019f: orl $0xfefefeff, %esi *)
| 303 => Some (6, 
    Move R_ESI (BinOp OP_OR (Cast CAST_LOW 32 (Var R_ESI)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 80 (* v361 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 80 (* v361 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 80 (* v361 *))) (Word 2 32)) (Var (V_TEMP 80 (* v361 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 80 (* v361 *))) (Word 1 32)) (Var (V_TEMP 80 (* v361 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001a5: addl $0x1, %esi *)
| 309 => Some (3, 
    Move (V_TEMP 81 (* v362 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 81 (* v362 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 81 (* v362 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 81 (* v362 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 81 (* v362 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 82 (* v364 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 82 (* v364 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 82 (* v364 *))) (Word 2 32)) (Var (V_TEMP 82 (* v364 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 82 (* v364 *))) (Word 1 32)) (Var (V_TEMP 82 (* v364 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001a8: jne 0x3d *)
| 312 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001aa: xorl %ecx, %ebp *)
| 314 => Some (2, 
    Move R_EBP (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 83 (* v353 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 83 (* v353 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 83 (* v353 *))) (Word 2 32)) (Var (V_TEMP 83 (* v353 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 83 (* v353 *))) (Word 1 32)) (Var (V_TEMP 83 (* v353 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00001ac: addl %ecx, %edi *)
| 316 => Some (2, 
    Move (V_TEMP 84 (* v354 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move (V_TEMP 85 (* v355 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EDI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 85 (* v355 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 84 (* v354 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 84 (* v354 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 85 (* v355 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 84 (* v354 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 84 (* v354 *)))) (Var (V_TEMP 85 (* v355 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 86 (* v356 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 86 (* v356 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 86 (* v356 *))) (Word 2 32)) (Var (V_TEMP 86 (* v356 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 86 (* v356 *))) (Word 1 32)) (Var (V_TEMP 86 (* v356 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0xc00001ae: leal 0x4(%eax), %eax *)
| 318 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) (Word 4 32)))
  )

(* 0xc00001b1: jae 0x4f *)
| 321 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001b3: movl %ecx, %ebx *)
| 323 => Some (2,
    Move R_EBX (Var R_ECX)
  )

(* 0xc00001b5: orl $0xfefefeff, %ebp *)
| 325 => Some (6, 
    Move R_EBP (BinOp OP_OR (Cast CAST_LOW 32 (Var R_EBP)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 87 (* v389 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 87 (* v389 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 87 (* v389 *))) (Word 2 32)) (Var (V_TEMP 87 (* v389 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 87 (* v389 *))) (Word 1 32)) (Var (V_TEMP 87 (* v389 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00001bb: addl $0x1, %ebp *)
| 331 => Some (3, 
    Move (V_TEMP 88 (* v390 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 88 (* v390 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 88 (* v390 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 88 (* v390 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 88 (* v390 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 89 (* v392 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 89 (* v392 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 89 (* v392 *))) (Word 2 32)) (Var (V_TEMP 89 (* v392 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 89 (* v392 *))) (Word 1 32)) (Var (V_TEMP 89 (* v392 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00001be: jne 0x42 *)
| 334 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 402 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001c0: movl $0xfefefeff, %esi *)
| 336 => Some (5,
    Move R_ESI (Word 4278124287 32)
  )

(* 0xc00001c5: xorl %edx, %ebx *)
| 341 => Some (2, 
    Move R_EBX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 90 (* v335 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 90 (* v335 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 90 (* v335 *))) (Word 2 32)) (Var (V_TEMP 90 (* v335 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 90 (* v335 *))) (Word 1 32)) (Var (V_TEMP 90 (* v335 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0xc00001c7: movl (%eax), %ecx *)
| 343 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0xc00001c9: addl %ebx, %esi *)
| 345 => Some (2, 
    Move (V_TEMP 91 (* v336 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move (V_TEMP 92 (* v337 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 92 (* v337 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 91 (* v336 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 91 (* v336 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 92 (* v337 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 91 (* v336 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 91 (* v336 *)))) (Var (V_TEMP 92 (* v337 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 93 (* v338 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 93 (* v338 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 93 (* v338 *))) (Word 2 32)) (Var (V_TEMP 93 (* v338 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 93 (* v338 *))) (Word 1 32)) (Var (V_TEMP 93 (* v338 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001cb: movl $0xfefefeff, %edi *)
| 347 => Some (5,
    Move R_EDI (Word 4278124287 32)
  )

(* 0xc00001d0: jae 0x15 *)
| 352 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 375 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001d2: movl %edi, %ebp *)
| 354 => Some (2,
    Move R_EBP (Var R_EDI)
  )

(* 0xc00001d4: xorl %ebx, %esi *)
| 356 => Some (2, 
    Move R_ESI (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 94 (* v393 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 94 (* v393 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 94 (* v393 *))) (Word 2 32)) (Var (V_TEMP 94 (* v393 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 94 (* v393 *))) (Word 1 32)) (Var (V_TEMP 94 (* v393 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001d6: addl %ecx, %ebp *)
| 358 => Some (2, 
    Move (V_TEMP 95 (* v394 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move (V_TEMP 96 (* v395 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_EBP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 96 (* v395 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 95 (* v394 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 95 (* v394 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 96 (* v395 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 95 (* v394 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBP)) (Var (V_TEMP 95 (* v394 *)))) (Var (V_TEMP 96 (* v395 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 97 (* v396 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBP))) (Let (V_TEMP 97 (* v396 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 97 (* v396 *))) (Word 2 32)) (Var (V_TEMP 97 (* v396 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 97 (* v396 *))) (Word 1 32)) (Var (V_TEMP 97 (* v396 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBP)))
  )

(* 0xc00001d8: orl $0xfefefeff, %esi *)
| 360 => Some (6, 
    Move R_ESI (BinOp OP_OR (Cast CAST_LOW 32 (Var R_ESI)) (Word 4278124287 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 98 (* v397 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 98 (* v397 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 98 (* v397 *))) (Word 2 32)) (Var (V_TEMP 98 (* v397 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 98 (* v397 *))) (Word 1 32)) (Var (V_TEMP 98 (* v397 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001de: addl $0x1, %esi *)
| 366 => Some (3, 
    Move (V_TEMP 99 (* v398 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESI)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 99 (* v398 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 99 (* v398 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 99 (* v398 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 99 (* v398 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 100 (* v400 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 100 (* v400 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 100 (* v400 *))) (Word 2 32)) (Var (V_TEMP 100 (* v400 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 100 (* v400 *))) (Word 1 32)) (Var (V_TEMP 100 (* v400 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0xc00001e1: je -0x108 *)
| 369 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 111 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001e7: subl $0x4, %eax *)
| 375 => Some (3, 
    Move (V_TEMP 101 (* v427 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 101 (* v427 *))) (Word 4 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 101 (* v427 *))) (Word 4 32)) (BinOp OP_XOR (Var (V_TEMP 101 (* v427 *))) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 101 (* v427 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 102 (* v429 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 102 (* v429 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 102 (* v429 *))) (Word 2 32)) (Var (V_TEMP 102 (* v429 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 102 (* v429 *))) (Word 1 32)) (Var (V_TEMP 102 (* v429 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00001ea: testb %bl, %bl *)
| 378 => Some (2, 
    Move (V_TEMP 103 (* v430 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 104 (* v431 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 103 (* v430 *))) (Word 4 8)) (Var (V_TEMP 103 (* v430 *)))) (Let (V_TEMP 104 (* v431 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 104 (* v431 *))) (Word 2 8)) (Var (V_TEMP 104 (* v431 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 104 (* v431 *))) (Word 1 8)) (Var (V_TEMP 104 (* v431 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 103 (* v430 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 103 (* v430 *))))
  )

(* 0xc00001ec: je 0xf *)
| 380 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001ee: incl %eax *)
| 382 => Some (1, 
    Move (V_TEMP 105 (* v312 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 105 (* v312 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 105 (* v312 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 105 (* v312 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 106 (* v313 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 106 (* v313 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 106 (* v313 *))) (Word 2 32)) (Var (V_TEMP 106 (* v313 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 106 (* v313 *))) (Word 1 32)) (Var (V_TEMP 106 (* v313 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00001ef: testb %bh, %bh *)
| 383 => Some (2, 
    Move (V_TEMP 107 (* v314 *)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EBX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 108 (* v315 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 107 (* v314 *))) (Word 4 8)) (Var (V_TEMP 107 (* v314 *)))) (Let (V_TEMP 108 (* v315 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 108 (* v315 *))) (Word 2 8)) (Var (V_TEMP 108 (* v315 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 108 (* v315 *))) (Word 1 8)) (Var (V_TEMP 108 (* v315 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 107 (* v314 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 107 (* v314 *))))
  )

(* 0xc00001f1: je 0xa *)
| 385 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001f3: shrl $0x10, %ebx *)
| 387 => Some (3, 
    Move (V_TEMP 109 (* tmp440 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_EBX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 16 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_LSHIFT (Var (V_TEMP 109 (* tmp440 *))) (BinOp OP_MINUS (Word 32 32) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32)))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 110 (* v441 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 110 (* v441 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 110 (* v441 *))) (Word 2 32)) (Var (V_TEMP 110 (* v441 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 110 (* v441 *))) (Word 1 32)) (Var (V_TEMP 110 (* v441 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Unknown 1)
  )

(* 0xc00001f6: incl %eax *)
| 390 => Some (1, 
    Move (V_TEMP 111 (* v442 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 111 (* v442 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 111 (* v442 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 111 (* v442 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 112 (* v443 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 112 (* v443 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 112 (* v443 *))) (Word 2 32)) (Var (V_TEMP 112 (* v443 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 112 (* v443 *))) (Word 1 32)) (Var (V_TEMP 112 (* v443 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00001f7: cmpb $0x0, %bl *)
| 391 => Some (3, 
    Move (V_TEMP 113 (* v444 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX))) (Var (V_TEMP 113 (* v444 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 113 (* v444 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EBX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 114 (* v445 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 113 (* v444 *))) (Word 4 8)) (Var (V_TEMP 113 (* v444 *)))) (Let (V_TEMP 114 (* v445 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 114 (* v445 *))) (Word 2 8)) (Var (V_TEMP 114 (* v445 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 114 (* v445 *))) (Word 1 8)) (Var (V_TEMP 114 (* v445 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 113 (* v444 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 113 (* v444 *))))
  )

(* 0xc00001fa: je 0x1 *)
| 394 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00001fc: incl %eax *)
| 396 => Some (1, 
    Move (V_TEMP 115 (* v347 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 115 (* v347 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 115 (* v347 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 115 (* v347 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 116 (* v348 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 116 (* v348 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 116 (* v348 *))) (Word 2 32)) (Var (V_TEMP 116 (* v348 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 116 (* v348 *))) (Word 1 32)) (Var (V_TEMP 116 (* v348 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00001fd: popl %ebp *)
| 397 => Some (1, 
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00001fe: popl %ebx *)
| 398 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc00001ff: popl %esi *)
| 399 => Some (1, 
    Move R_ESI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000200: popl %edi *)
| 400 => Some (1, 
    Move R_EDI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0xc0000201: retl *)
| 401 => Some (1, 
    Move (V_TEMP 117 (* v412 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 117 (* v412 *)))
  )

(* 0xc0000202: subl $0x4, %eax *)
| 402 => Some (3, 
    Move (V_TEMP 118 (* v403 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 118 (* v403 *))) (Word 4 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 118 (* v403 *))) (Word 4 32)) (BinOp OP_XOR (Var (V_TEMP 118 (* v403 *))) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 118 (* v403 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 119 (* v405 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 119 (* v405 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 119 (* v405 *))) (Word 2 32)) (Var (V_TEMP 119 (* v405 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 119 (* v405 *))) (Word 1 32)) (Var (V_TEMP 119 (* v405 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc0000205: cmpb %dl, %cl *)
| 405 => Some (2, 
    Move (V_TEMP 120 (* v406 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 120 (* v406 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 120 (* v406 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 121 (* v407 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 120 (* v406 *))) (Word 4 8)) (Var (V_TEMP 120 (* v406 *)))) (Let (V_TEMP 121 (* v407 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 121 (* v407 *))) (Word 2 8)) (Var (V_TEMP 121 (* v407 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 121 (* v407 *))) (Word 1 8)) (Var (V_TEMP 121 (* v407 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 120 (* v406 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 120 (* v406 *))))
  )

(* 0xc0000207: je -0xc *)
| 407 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000209: cmpb $0x0, %cl *)
| 409 => Some (3, 
    Move (V_TEMP 122 (* v420 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 122 (* v420 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 122 (* v420 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 123 (* v421 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 122 (* v420 *))) (Word 4 8)) (Var (V_TEMP 122 (* v420 *)))) (Let (V_TEMP 123 (* v421 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 123 (* v421 *))) (Word 2 8)) (Var (V_TEMP 123 (* v421 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 123 (* v421 *))) (Word 1 8)) (Var (V_TEMP 123 (* v421 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 122 (* v420 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 122 (* v420 *))))
  )

(* 0xc000020c: je 0x1c *)
| 412 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000020e: incl %eax *)
| 414 => Some (1, 
    Move (V_TEMP 124 (* v408 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 124 (* v408 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 124 (* v408 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 124 (* v408 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 125 (* v409 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 125 (* v409 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 125 (* v409 *))) (Word 2 32)) (Var (V_TEMP 125 (* v409 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 125 (* v409 *))) (Word 1 32)) (Var (V_TEMP 125 (* v409 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc000020f: cmpb %dl, %ch *)
| 415 => Some (2, 
    Move (V_TEMP 126 (* v410 *)) (BinOp OP_MINUS (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Var (V_TEMP 126 (* v410 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 126 (* v410 *))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX))))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 127 (* v411 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 126 (* v410 *))) (Word 4 8)) (Var (V_TEMP 126 (* v410 *)))) (Let (V_TEMP 127 (* v411 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 127 (* v411 *))) (Word 2 8)) (Var (V_TEMP 127 (* v411 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 127 (* v411 *))) (Word 1 8)) (Var (V_TEMP 127 (* v411 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 126 (* v410 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 126 (* v410 *))))
  )

(* 0xc0000211: je -0x16 *)
| 417 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000213: cmpb $0x0, %ch *)
| 419 => Some (3, 
    Move (V_TEMP 128 (* v401 *)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Var (V_TEMP 128 (* v401 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 128 (* v401 *))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX))))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 129 (* v402 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 128 (* v401 *))) (Word 4 8)) (Var (V_TEMP 128 (* v401 *)))) (Let (V_TEMP 129 (* v402 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 129 (* v402 *))) (Word 2 8)) (Var (V_TEMP 129 (* v402 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 129 (* v402 *))) (Word 1 8)) (Var (V_TEMP 129 (* v402 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 128 (* v401 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 128 (* v401 *))))
  )

(* 0xc0000216: je 0x12 *)
| 422 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000218: shrl $0x10, %ecx *)
| 424 => Some (3, 
    Move (V_TEMP 130 (* tmp379 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 16 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_LSHIFT (Var (V_TEMP 130 (* tmp379 *))) (BinOp OP_MINUS (Word 32 32) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32)))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 131 (* v380 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 131 (* v380 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 131 (* v380 *))) (Word 2 32)) (Var (V_TEMP 131 (* v380 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 131 (* v380 *))) (Word 1 32)) (Var (V_TEMP 131 (* v380 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Unknown 1)
  )

(* 0xc000021b: incl %eax *)
| 427 => Some (1, 
    Move (V_TEMP 132 (* v381 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 132 (* v381 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 132 (* v381 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 132 (* v381 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 133 (* v382 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 133 (* v382 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 133 (* v382 *))) (Word 2 32)) (Var (V_TEMP 133 (* v382 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 133 (* v382 *))) (Word 1 32)) (Var (V_TEMP 133 (* v382 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc000021c: cmpb %dl, %cl *)
| 428 => Some (2, 
    Move (V_TEMP 134 (* v383 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 134 (* v383 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 134 (* v383 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 135 (* v384 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 134 (* v383 *))) (Word 4 8)) (Var (V_TEMP 134 (* v383 *)))) (Let (V_TEMP 135 (* v384 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 135 (* v384 *))) (Word 2 8)) (Var (V_TEMP 135 (* v384 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 135 (* v384 *))) (Word 1 8)) (Var (V_TEMP 135 (* v384 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 134 (* v383 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 134 (* v383 *))))
  )

(* 0xc000021e: je -0x23 *)
| 430 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000220: cmpb $0x0, %cl *)
| 432 => Some (3, 
    Move (V_TEMP 136 (* v325 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 136 (* v325 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 136 (* v325 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 137 (* v326 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 136 (* v325 *))) (Word 4 8)) (Var (V_TEMP 136 (* v325 *)))) (Let (V_TEMP 137 (* v326 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 137 (* v326 *))) (Word 2 8)) (Var (V_TEMP 137 (* v326 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 137 (* v326 *))) (Word 1 8)) (Var (V_TEMP 137 (* v326 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 136 (* v325 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 136 (* v325 *))))
  )

(* 0xc0000223: je 0x5 *)
| 435 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 442 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000225: incl %eax *)
| 437 => Some (1, 
    Move (V_TEMP 138 (* v319 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 138 (* v319 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 138 (* v319 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 138 (* v319 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 139 (* v320 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 139 (* v320 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 139 (* v320 *))) (Word 2 32)) (Var (V_TEMP 139 (* v320 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 139 (* v320 *))) (Word 1 32)) (Var (V_TEMP 139 (* v320 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc0000226: cmpb %dl, %ch *)
| 438 => Some (2, 
    Move (V_TEMP 140 (* v321 *)) (BinOp OP_MINUS (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))) (BinOp OP_XOR (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Var (V_TEMP 140 (* v321 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 140 (* v321 *))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX))))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EDX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 141 (* v322 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 140 (* v321 *))) (Word 4 8)) (Var (V_TEMP 140 (* v321 *)))) (Let (V_TEMP 141 (* v322 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 141 (* v322 *))) (Word 2 8)) (Var (V_TEMP 141 (* v322 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 141 (* v322 *))) (Word 1 8)) (Var (V_TEMP 141 (* v322 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 140 (* v321 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 140 (* v321 *))))
  )

(* 0xc0000228: je -0x2d *)
| 440 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 397 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000022a: xorl %eax, %eax *)
| 442 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc000022c: jmp -0x31 *)
| 444 => Some (2,
    Jmp (Word 397 32)
  )

| _ => None
end.
