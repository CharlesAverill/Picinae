Require Import Picinae_i386.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition strtok_i386 loc : program := fun _ a => match a with

(* 0xc0000040: movl %edi, %edx *)
| 0 => Some (2,
    Move R_EDX (Var R_EDI)
  )

(* 0xc0000042: subl $0x100, %esp *)
| 2 => Some (6, 
    Move (V_TEMP 0 (* v128 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 256 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 0 (* v128 *))) (Word 256 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 0 (* v128 *))) (Word 256 32)) (BinOp OP_XOR (Var (V_TEMP 0 (* v128 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 0 (* v128 *)))) (Word 256 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 1 (* v130 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 1 (* v130 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v130 *))) (Word 2 32)) (Var (V_TEMP 1 (* v130 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v130 *))) (Word 1 32)) (Var (V_TEMP 1 (* v130 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0xc0000048: movl $0x40, %ecx *)
| 8 => Some (5,
    Move R_ECX (Word 64 32)
  )

(* 0xc000004d: movl %esp, %edi *)
| 13 => Some (2,
    Move R_EDI (Var R_ESP)
  )

(* 0xc000004f: xorl %eax, %eax *)
| 15 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000051: cld *)
| 17 => Some (1,
    Move R_DF (Word 0 1)
  )

(* 0xc0000052: stosl %eax, %es:(%edi) *)
| 18 => Some (2, 
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 20 32)
    ) (* else *) (
      Nop
    ) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDI) (Cast CAST_LOW 32 (Var R_EAX)) LittleE 4) $;
    Move R_EDI (BinOp OP_PLUS (Var R_EDI) (BinOp OP_TIMES (Ite (BinOp OP_EQ (Var R_DF) (Word 0 1)) (Word 1 32) (Word 4294967295 32)) (Word 4 32))) $;
    Move R_ECX (BinOp OP_MINUS (Var R_ECX) (Word 1 32)) $;
    If (BinOp OP_EQ (Var R_ECX) (Word 0 32)) (
      Jmp (Word 20 32)
    ) (* else *) (
      Nop
    ) $;
    Jmp (Word 18 32)
  )

(* 0xc0000054: movl %edx, %edi *)
| 20 => Some (2,
    Move R_EDI (Var R_EDX)
  )

(* 0xc0000056: movl 0x104(%esp), %edx *)
| 22 => Some (7,
    Move R_EDX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 260 32)) LittleE 4)
  )

(* 0xc000005d: movl 0x0, %eax *)
| 29 => Some (5,
    Move R_EAX (Load (Var V_MEM32) (Word loc 32) LittleE 4)
  )

(* 0xc0000062: cmpl $0x0, %edx *)
| 34 => Some (3, 
    Move (V_TEMP 2 (* v170 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDX)) (Word 0 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Word 0 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 2 (* v170 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (Var (V_TEMP 2 (* v170 *))) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* v171 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v170 *))) (Word 4 32)) (Var (V_TEMP 2 (* v170 *)))) (Let (V_TEMP 3 (* v171 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v171 *))) (Word 2 32)) (Var (V_TEMP 3 (* v171 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v171 *))) (Word 1 32)) (Var (V_TEMP 3 (* v171 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v170 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 2 (* v170 *))))
  )

(* 0xc0000065: cmovel %eax, %edx *)
| 37 => Some (3,
    Move R_EDX (Ite (Var R_ZF) (Cast CAST_LOW 32 (Var R_EAX)) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc0000068: testl %edx, %edx *)
| 40 => Some (2, 
    Move (V_TEMP 4 (* v172 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 5 (* v173 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v172 *))) (Word 4 32)) (Var (V_TEMP 4 (* v172 *)))) (Let (V_TEMP 5 (* v173 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v173 *))) (Word 2 32)) (Var (V_TEMP 5 (* v173 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v173 *))) (Word 1 32)) (Var (V_TEMP 5 (* v173 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v172 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 4 (* v172 *))))
  )

(* 0xc000006a: je 0xa1 *)
| 42 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 209 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000070: movl 0x108(%esp), %eax *)
| 48 => Some (7,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 264 32)) LittleE 4)
  )

(* 0xc0000077: movb (%eax), %cl *)
| 55 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (Var R_EAX) LittleE 1))
  )

(* 0xc0000079: testb %cl, %cl *)
| 57 => Some (2, 
    Move (V_TEMP 6 (* v133 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v134 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v133 *))) (Word 4 8)) (Var (V_TEMP 6 (* v133 *)))) (Let (V_TEMP 7 (* v134 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v134 *))) (Word 2 8)) (Var (V_TEMP 7 (* v134 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v134 *))) (Word 1 8)) (Var (V_TEMP 7 (* v134 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v133 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 6 (* v133 *))))
  )

(* 0xc000007b: je 0x27 *)
| 59 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 100 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007d: movb %cl, (%esp,%ecx) *)
| 61 => Some (3,
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Var R_ECX)) (Cast CAST_LOW 8 (Var R_ECX)) LittleE 1)
  )

(* 0xc0000080: movb 0x1(%eax), %cl *)
| 64 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 1 32)) LittleE 1))
  )

(* 0xc0000083: testb $-0x1, %cl *)
| 67 => Some (3, 
    Move (V_TEMP 8 (* v162 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 9 (* v163 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v162 *))) (Word 4 8)) (Var (V_TEMP 8 (* v162 *)))) (Let (V_TEMP 9 (* v163 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v163 *))) (Word 2 8)) (Var (V_TEMP 9 (* v163 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v163 *))) (Word 1 8)) (Var (V_TEMP 9 (* v163 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 8 (* v162 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 8 (* v162 *))))
  )

(* 0xc0000086: je 0x1c *)
| 70 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 100 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000088: movb %cl, (%esp,%ecx) *)
| 72 => Some (3,
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Var R_ECX)) (Cast CAST_LOW 8 (Var R_ECX)) LittleE 1)
  )

(* 0xc000008b: movb 0x2(%eax), %cl *)
| 75 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 2 32)) LittleE 1))
  )

(* 0xc000008e: testb $-0x1, %cl *)
| 78 => Some (3, 
    Move (V_TEMP 10 (* v120 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 11 (* v121 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* v120 *))) (Word 4 8)) (Var (V_TEMP 10 (* v120 *)))) (Let (V_TEMP 11 (* v121 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v121 *))) (Word 2 8)) (Var (V_TEMP 11 (* v121 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v121 *))) (Word 1 8)) (Var (V_TEMP 11 (* v121 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v120 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 10 (* v120 *))))
  )

(* 0xc0000091: je 0x11 *)
| 81 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 100 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000093: movb %cl, (%esp,%ecx) *)
| 83 => Some (3,
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Var R_ECX)) (Cast CAST_LOW 8 (Var R_ECX)) LittleE 1)
  )

(* 0xc0000096: movb 0x3(%eax), %cl *)
| 86 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 3 32)) LittleE 1))
  )

(* 0xc0000099: addl $0x4, %eax *)
| 89 => Some (3, 
    Move (V_TEMP 12 (* v148 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 12 (* v148 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v148 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* v148 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 12 (* v148 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 13 (* v150 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 13 (* v150 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v150 *))) (Word 2 32)) (Var (V_TEMP 13 (* v150 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v150 *))) (Word 1 32)) (Var (V_TEMP 13 (* v150 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc000009c: movb %cl, (%esp,%ecx) *)
| 92 => Some (3,
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Var R_ECX)) (Cast CAST_LOW 8 (Var R_ECX)) LittleE 1)
  )

(* 0xc000009f: testb $-0x1, %cl *)
| 95 => Some (3, 
    Move (V_TEMP 14 (* v151 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 15 (* v152 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* v151 *))) (Word 4 8)) (Var (V_TEMP 14 (* v151 *)))) (Let (V_TEMP 15 (* v152 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v152 *))) (Word 2 8)) (Var (V_TEMP 15 (* v152 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v152 *))) (Word 1 8)) (Var (V_TEMP 15 (* v152 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 14 (* v151 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 14 (* v151 *))))
  )

(* 0xc00000a2: jne -0x2d *)
| 98 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 55 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a4: leal -0x4(%edx), %eax *)
| 100 => Some (3,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) (Word 4294967292 32)))
  )

(* 0xc00000a7: addl $0x4, %eax *)
| 103 => Some (3, 
    Move (V_TEMP 16 (* v135 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 16 (* v135 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v135 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v135 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 16 (* v135 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 17 (* v137 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 17 (* v137 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v137 *))) (Word 2 32)) (Var (V_TEMP 17 (* v137 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v137 *))) (Word 1 32)) (Var (V_TEMP 17 (* v137 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000aa: movb (%eax), %cl *)
| 106 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (Var R_EAX) LittleE 1))
  )

(* 0xc00000ac: testb (%esp,%ecx), %cl *)
| 108 => Some (3, 
    Move (V_TEMP 18 (* v138 *)) (BinOp OP_AND (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 19 (* v139 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v138 *))) (Word 4 8)) (Var (V_TEMP 18 (* v138 *)))) (Let (V_TEMP 19 (* v139 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v139 *))) (Word 2 8)) (Var (V_TEMP 19 (* v139 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v139 *))) (Word 1 8)) (Var (V_TEMP 19 (* v139 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* v138 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 18 (* v138 *))))
  )

(* 0xc00000af: je 0x1b *)
| 111 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 140 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b1: movb 0x1(%eax), %cl *)
| 113 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 1 32)) LittleE 1))
  )

(* 0xc00000b4: testb (%esp,%ecx), %cl *)
| 116 => Some (3, 
    Move (V_TEMP 20 (* v122 *)) (BinOp OP_AND (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 21 (* v123 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* v122 *))) (Word 4 8)) (Var (V_TEMP 20 (* v122 *)))) (Let (V_TEMP 21 (* v123 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 21 (* v123 *))) (Word 2 8)) (Var (V_TEMP 21 (* v123 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 21 (* v123 *))) (Word 1 8)) (Var (V_TEMP 21 (* v123 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 20 (* v122 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 20 (* v122 *))))
  )

(* 0xc00000b7: je 0x12 *)
| 119 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 139 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b9: movb 0x2(%eax), %cl *)
| 121 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 2 32)) LittleE 1))
  )

(* 0xc00000bc: testb (%esp,%ecx), %cl *)
| 124 => Some (3, 
    Move (V_TEMP 22 (* v166 *)) (BinOp OP_AND (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 23 (* v167 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 22 (* v166 *))) (Word 4 8)) (Var (V_TEMP 22 (* v166 *)))) (Let (V_TEMP 23 (* v167 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 23 (* v167 *))) (Word 2 8)) (Var (V_TEMP 23 (* v167 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 23 (* v167 *))) (Word 1 8)) (Var (V_TEMP 23 (* v167 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 22 (* v166 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 22 (* v166 *))))
  )

(* 0xc00000bf: je 0x9 *)
| 127 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 138 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000c1: movb 0x3(%eax), %cl *)
| 129 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EAX) (Word 3 32)) LittleE 1))
  )

(* 0xc00000c4: testb (%esp,%ecx), %cl *)
| 132 => Some (3, 
    Move (V_TEMP 24 (* v142 *)) (BinOp OP_AND (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 25 (* v143 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v142 *))) (Word 4 8)) (Var (V_TEMP 24 (* v142 *)))) (Let (V_TEMP 25 (* v143 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* v143 *))) (Word 2 8)) (Var (V_TEMP 25 (* v143 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* v143 *))) (Word 1 8)) (Var (V_TEMP 25 (* v143 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* v142 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 24 (* v142 *))))
  )

(* 0xc00000c7: jne -0x22 *)
| 135 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 103 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000c9: incl %eax *)
| 137 => Some (1, 
    Move (V_TEMP 26 (* v124 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* v124 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* v124 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 26 (* v124 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 27 (* v125 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 27 (* v125 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 27 (* v125 *))) (Word 2 32)) (Var (V_TEMP 27 (* v125 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 27 (* v125 *))) (Word 1 32)) (Var (V_TEMP 27 (* v125 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000ca: incl %eax *)
| 138 => Some (1, 
    Move (V_TEMP 28 (* v164 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 28 (* v164 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 28 (* v164 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 28 (* v164 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 29 (* v165 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 29 (* v165 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 29 (* v165 *))) (Word 2 32)) (Var (V_TEMP 29 (* v165 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 29 (* v165 *))) (Word 1 32)) (Var (V_TEMP 29 (* v165 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000cb: incl %eax *)
| 139 => Some (1, 
    Move (V_TEMP 30 (* v140 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v140 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v140 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 30 (* v140 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 31 (* v141 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 31 (* v141 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v141 *))) (Word 2 32)) (Var (V_TEMP 31 (* v141 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v141 *))) (Word 1 32)) (Var (V_TEMP 31 (* v141 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000cc: leal -0x4(%eax), %edx *)
| 140 => Some (3,
    Move R_EDX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) (Word 4294967292 32)))
  )

(* 0xc00000cf: addl $0x4, %edx *)
| 143 => Some (3, 
    Move (V_TEMP 32 (* v153 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 32 (* v153 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 32 (* v153 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 32 (* v153 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 32 (* v153 *)))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 33 (* v155 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 33 (* v155 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v155 *))) (Word 2 32)) (Var (V_TEMP 33 (* v155 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v155 *))) (Word 1 32)) (Var (V_TEMP 33 (* v155 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc00000d2: movb (%edx), %cl *)
| 146 => Some (2,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (Var R_EDX) LittleE 1))
  )

(* 0xc00000d4: cmpb %cl, (%esp,%ecx) *)
| 148 => Some (3, 
    Move (V_TEMP 34 (* v156 *)) (BinOp OP_MINUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Var (V_TEMP 34 (* v156 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 34 (* v156 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 35 (* v157 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 34 (* v156 *))) (Word 4 8)) (Var (V_TEMP 34 (* v156 *)))) (Let (V_TEMP 35 (* v157 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v157 *))) (Word 2 8)) (Var (V_TEMP 35 (* v157 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v157 *))) (Word 1 8)) (Var (V_TEMP 35 (* v157 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 34 (* v156 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 34 (* v156 *))))
  )

(* 0xc00000d7: je 0x1b *)
| 151 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 180 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000d9: movb 0x1(%edx), %cl *)
| 153 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EDX) (Word 1 32)) LittleE 1))
  )

(* 0xc00000dc: cmpb %cl, (%esp,%ecx) *)
| 156 => Some (3, 
    Move (V_TEMP 36 (* v144 *)) (BinOp OP_MINUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Var (V_TEMP 36 (* v144 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 36 (* v144 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 37 (* v145 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 36 (* v144 *))) (Word 4 8)) (Var (V_TEMP 36 (* v144 *)))) (Let (V_TEMP 37 (* v145 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 37 (* v145 *))) (Word 2 8)) (Var (V_TEMP 37 (* v145 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 37 (* v145 *))) (Word 1 8)) (Var (V_TEMP 37 (* v145 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 36 (* v144 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 36 (* v144 *))))
  )

(* 0xc00000df: je 0x12 *)
| 159 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 179 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000e1: movb 0x2(%edx), %cl *)
| 161 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EDX) (Word 2 32)) LittleE 1))
  )

(* 0xc00000e4: cmpb %cl, (%esp,%ecx) *)
| 164 => Some (3, 
    Move (V_TEMP 38 (* v126 *)) (BinOp OP_MINUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Var (V_TEMP 38 (* v126 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 38 (* v126 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 39 (* v127 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 38 (* v126 *))) (Word 4 8)) (Var (V_TEMP 38 (* v126 *)))) (Let (V_TEMP 39 (* v127 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v127 *))) (Word 2 8)) (Var (V_TEMP 39 (* v127 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v127 *))) (Word 1 8)) (Var (V_TEMP 39 (* v127 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 38 (* v126 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 38 (* v126 *))))
  )

(* 0xc00000e7: je 0x9 *)
| 167 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 178 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000e9: movb 0x3(%edx), %cl *)
| 169 => Some (3,
    Move R_ECX (Concat (Cast CAST_HIGH 24 (Var R_ECX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EDX) (Word 3 32)) LittleE 1))
  )

(* 0xc00000ec: cmpb %cl, (%esp,%ecx) *)
| 172 => Some (3, 
    Move (V_TEMP 40 (* v168 *)) (BinOp OP_MINUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1) (Var (V_TEMP 40 (* v168 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 40 (* v168 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Cast CAST_LOW 32 (Var R_ECX))) LittleE 1)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 41 (* v169 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 40 (* v168 *))) (Word 4 8)) (Var (V_TEMP 40 (* v168 *)))) (Let (V_TEMP 41 (* v169 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 41 (* v169 *))) (Word 2 8)) (Var (V_TEMP 41 (* v169 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 41 (* v169 *))) (Word 1 8)) (Var (V_TEMP 41 (* v169 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 40 (* v168 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 40 (* v168 *))))
  )

(* 0xc00000ef: jne -0x22 *)
| 175 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 143 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000f1: incl %edx *)
| 177 => Some (1, 
    Move (V_TEMP 42 (* v146 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* v146 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* v146 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 42 (* v146 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 43 (* v147 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 43 (* v147 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 43 (* v147 *))) (Word 2 32)) (Var (V_TEMP 43 (* v147 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 43 (* v147 *))) (Word 1 32)) (Var (V_TEMP 43 (* v147 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc00000f2: incl %edx *)
| 178 => Some (1, 
    Move (V_TEMP 44 (* v174 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 44 (* v174 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 44 (* v174 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 44 (* v174 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 45 (* v175 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 45 (* v175 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 45 (* v175 *))) (Word 2 32)) (Var (V_TEMP 45 (* v175 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 45 (* v175 *))) (Word 1 32)) (Var (V_TEMP 45 (* v175 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc00000f3: incl %edx *)
| 179 => Some (1, 
    Move (V_TEMP 46 (* v160 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 46 (* v160 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 46 (* v160 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 46 (* v160 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 47 (* v161 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 47 (* v161 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 47 (* v161 *))) (Word 2 32)) (Var (V_TEMP 47 (* v161 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 47 (* v161 *))) (Word 1 32)) (Var (V_TEMP 47 (* v161 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc00000f4: cmpl %eax, %edx *)
| 180 => Some (2, 
    Move (V_TEMP 48 (* v131 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_EAX))) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 48 (* v131 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 48 (* v131 *))) (Cast CAST_LOW 32 (Var R_EDX))) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 49 (* v132 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 48 (* v131 *))) (Word 4 32)) (Var (V_TEMP 48 (* v131 *)))) (Let (V_TEMP 49 (* v132 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 49 (* v132 *))) (Word 2 32)) (Var (V_TEMP 49 (* v132 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 49 (* v132 *))) (Word 1 32)) (Var (V_TEMP 49 (* v132 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 48 (* v131 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 48 (* v131 *))))
  )

(* 0xc00000f6: je 0x19 *)
| 182 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 209 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000f8: movb $0x0, (%edx) *)
| 184 => Some (3,
    Move V_MEM32 (Store (Var V_MEM32) (Var R_EDX) (Word 0 8) LittleE 1)
  )

(* 0xc00000fb: cmpb $0x0, %cl *)
| 187 => Some (3, 
    Move (V_TEMP 50 (* v158 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 50 (* v158 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (Var (V_TEMP 50 (* v158 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 51 (* v159 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 50 (* v158 *))) (Word 4 8)) (Var (V_TEMP 50 (* v158 *)))) (Let (V_TEMP 51 (* v159 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 51 (* v159 *))) (Word 2 8)) (Var (V_TEMP 51 (* v159 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 51 (* v159 *))) (Word 1 8)) (Var (V_TEMP 51 (* v159 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 50 (* v158 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 50 (* v158 *))))
  )

(* 0xc00000fe: leal 0x1(%edx), %ecx *)
| 190 => Some (3,
    Move R_ECX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) (Word 1 32)))
  )

(* 0xc0000101: cmovnel %ecx, %edx *)
| 193 => Some (3,
    Move R_EDX (Ite (UnOp OP_NOT (Var R_ZF)) (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc0000104: movl %edx, 0x0 *)
| 196 => Some (6,
    Move V_MEM32 (Store (Var V_MEM32) (Word loc 32) (Var R_EDX) LittleE 4)
  )

(* 0xc000010a: addl $0x100, %esp *)
| 202 => Some (6, 
    Move (V_TEMP 52 (* v176 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 256 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 52 (* v176 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* v176 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* v176 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 52 (* v176 *)))) (Word 256 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 53 (* v178 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 53 (* v178 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 53 (* v178 *))) (Word 2 32)) (Var (V_TEMP 53 (* v178 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 53 (* v178 *))) (Word 1 32)) (Var (V_TEMP 53 (* v178 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0xc0000110: retl *)
| 208 => Some (1, 
    Move (V_TEMP 54 (* v179 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 54 (* v179 *)))
  )

(* 0xc0000111: xorl %eax, %eax *)
| 209 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000113: movl %edx, 0x0 *)
| 211 => Some (6,
    Move V_MEM32 (Store (Var V_MEM32) (Word loc 32) (Var R_EDX) LittleE 4)
  )

(* 0xc0000119: jmp -0x11 *)
| 217 => Some (2,
    Jmp (Word 202 32)
  )

| _ => None
end.
