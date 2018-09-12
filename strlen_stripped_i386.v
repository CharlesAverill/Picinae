Require Import Picinae_i386.
Import PArch_i386.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition strlen_i386 : program := fun a => match a with

(* 0x74820: movl 0x4(%esp), %eax *)
| 0 => Some (4,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) LittleE 4)
  )

(* 0x74824: movl $0x3, %edx *)
| 4 => Some (5,
    Move R_EDX (Word 3 32)
  )

(* 0x74829: andl %eax, %edx *)
| 9 => Some (2,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59293) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59293) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59293)) (Word 2 32)) (Var (V_TEMP 59293))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59293)) (Word 1 32)) (Var (V_TEMP 59293))))))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x7482b: je 0x24 *)
| 11 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 49 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7482d: jp 0x17 *)
| 13 => Some (2,
    If (Var R_PF) (
      Jmp (Word 38 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7482f: cmpb %dh, (%eax) *)
| 15 => Some (2,
    Move (V_TEMP 59294) (BinOp OP_MINUS (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59294)))
  )

(* 0x74831: je 0x9f *)
| 17 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74837: incl %eax *)
| 23 => Some (1,
    Move (V_TEMP 59296) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x74838: cmpb %dh, (%eax) *)
| 24 => Some (2,
    Move (V_TEMP 59298) (BinOp OP_MINUS (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59298)))
  )

(* 0x7483a: je 0x96 *)
| 26 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74840: incl %eax *)
| 32 => Some (1,
    Move (V_TEMP 59300) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x74841: xorl $0x2, %edx *)
| 33 => Some (3,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74844: je 0xb *)
| 36 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 49 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74846: cmpb %dh, (%eax) *)
| 38 => Some (2,
    Move (V_TEMP 59303) (BinOp OP_MINUS (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59303)))
  )

(* 0x74848: je 0x88 *)
| 40 => Some (6,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7484e: incl %eax *)
| 46 => Some (1,
    Move (V_TEMP 59305) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x7484f: xorl %edx, %edx *)
| 47 => Some (2,
    Move R_EDX (Word 0 32)
  )

(* 0x74851: movl (%eax), %ecx *)
| 49 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0x74853: addl $0x4, %eax *)
| 51 => Some (3,
    Move (V_TEMP 59307) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 59308) (Word 4 32) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59308)))
  )

(* 0x74856: subl %ecx, %edx *)
| 54 => Some (2,
    Move (V_TEMP 59310) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74858: addl $0xfefefeff, %ecx *)
| 56 => Some (6,
    Move (V_TEMP 59312) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59313) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59313))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59312)))
  )

(* 0x7485e: decl %edx *)
| 62 => Some (1,
    Move (V_TEMP 59315) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32))
  )

(* 0x7485f: jae 0x58 *)
| 63 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74861: xorl %ecx, %edx *)
| 65 => Some (2,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74863: andl $0x1010100, %edx *)
| 67 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74869: jne 0x4e *)
| 73 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7486b: movl (%eax), %ecx *)
| 75 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0x7486d: addl $0x4, %eax *)
| 77 => Some (3,
    Move (V_TEMP 59319) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 59320) (Word 4 32) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59320)))
  )

(* 0x74870: subl %ecx, %edx *)
| 80 => Some (2,
    Move (V_TEMP 59322) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74872: addl $0xfefefeff, %ecx *)
| 82 => Some (6,
    Move (V_TEMP 59324) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59325) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59325))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59324)))
  )

(* 0x74878: decl %edx *)
| 88 => Some (1,
    Move (V_TEMP 59327) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32))
  )

(* 0x74879: jae 0x3e *)
| 89 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7487b: xorl %ecx, %edx *)
| 91 => Some (2,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x7487d: andl $0x1010100, %edx *)
| 93 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74883: jne 0x34 *)
| 99 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74885: movl (%eax), %ecx *)
| 101 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0x74887: addl $0x4, %eax *)
| 103 => Some (3,
    Move (V_TEMP 59331) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 59332) (Word 4 32) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59332)))
  )

(* 0x7488a: subl %ecx, %edx *)
| 106 => Some (2,
    Move (V_TEMP 59334) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x7488c: addl $0xfefefeff, %ecx *)
| 108 => Some (6,
    Move (V_TEMP 59336) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59337) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59337))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59336)))
  )

(* 0x74892: decl %edx *)
| 114 => Some (1,
    Move (V_TEMP 59339) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32))
  )

(* 0x74893: jae 0x24 *)
| 115 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x74895: xorl %ecx, %edx *)
| 117 => Some (2,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74897: andl $0x1010100, %edx *)
| 119 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x7489d: jne 0x1a *)
| 125 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x7489f: movl (%eax), %ecx *)
| 127 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0x748a1: addl $0x4, %eax *)
| 129 => Some (3,
    Move (V_TEMP 59343) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 59344) (Word 4 32) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59344)))
  )

(* 0x748a4: subl %ecx, %edx *)
| 132 => Some (2,
    Move (V_TEMP 59346) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x748a6: addl $0xfefefeff, %ecx *)
| 134 => Some (6,
    Move (V_TEMP 59348) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59349) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59349))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59348)))
  )

(* 0x748ac: decl %edx *)
| 140 => Some (1,
    Move (V_TEMP 59351) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32))
  )

(* 0x748ad: jae 0xa *)
| 141 => Some (2,
    If (UnOp OP_NOT (Var R_CF)) (
      Jmp (Word 153 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x748af: xorl %ecx, %edx *)
| 143 => Some (2,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x748b1: andl $0x1010100, %edx *)
| 145 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x748b7: je -0x68 *)
| 151 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 49 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x748b9: subl $0x4, %eax *)
| 153 => Some (3,
    Move (V_TEMP 59355) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32))
  )

(* 0x748bc: subl $0xfefefeff, %ecx *)
| 156 => Some (6,
    Move (V_TEMP 59357) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 4278124287 32))
  )

(* 0x748c2: cmpb $0x0, %cl *)
| 162 => Some (3,
    Move (V_TEMP 59359) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59359)))
  )

(* 0x748c5: je 0xf *)
| 165 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x748c7: incl %eax *)
| 167 => Some (1,
    Move (V_TEMP 59361) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x748c8: testb %ch, %ch *)
| 168 => Some (2,
    Move (V_TEMP 59363) (BinOp OP_AND (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59363)))
  )

(* 0x748ca: je 0xa *)
| 170 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x748cc: shrl $0x10, %ecx *)
| 172 => Some (3,
    Move (V_TEMP 59365) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59366) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))) $;
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))
  )

(* 0x748cf: incl %eax *)
| 175 => Some (1,
    Move (V_TEMP 59368) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x748d0: cmpb $0x0, %cl *)
| 176 => Some (3,
    Move (V_TEMP 59370) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 59370)))
  )

(* 0x748d3: je 0x1 *)
| 179 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 182 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x748d5: incl %eax *)
| 181 => Some (1,
    Move (V_TEMP 59372) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32))
  )

(* 0x748d6: subl 0x4(%esp), %eax *)
| 182 => Some (4,
    Move (V_TEMP 59374) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) LittleE 4))
  )

(* 0x748da: retl *)
| 186 => Some (1,
    Move (V_TEMP 59376) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 59376))
  )

| _ => None
end.
