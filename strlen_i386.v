Require Import Picinae_i386.
Require Import NArith.
Open Scope N.

Definition strlen_i386 : program := fun _ a => match a with

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
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59293) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59293) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59293)) (Word 2 32)) (Var (V_TEMP 59293))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59293)) (Word 1 32)) (Var (V_TEMP 59293))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Var (V_TEMP 59294))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59294)) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59295) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59294)) (Word 4 8)) (Var (V_TEMP 59294))) (Let (V_TEMP 59295) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59295)) (Word 2 8)) (Var (V_TEMP 59295))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59295)) (Word 1 8)) (Var (V_TEMP 59295))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59294))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59296))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59296))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59296))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59297) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59297) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59297)) (Word 2 32)) (Var (V_TEMP 59297))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59297)) (Word 1 32)) (Var (V_TEMP 59297))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x74838: cmpb %dh, (%eax) *)
| 24 => Some (2,
    Move (V_TEMP 59298) (BinOp OP_MINUS (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Var (V_TEMP 59298))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59298)) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59299) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59298)) (Word 4 8)) (Var (V_TEMP 59298))) (Let (V_TEMP 59299) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59299)) (Word 2 8)) (Var (V_TEMP 59299))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59299)) (Word 1 8)) (Var (V_TEMP 59299))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59298))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59300))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59300))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59300))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59301) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59301) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59301)) (Word 2 32)) (Var (V_TEMP 59301))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59301)) (Word 1 32)) (Var (V_TEMP 59301))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x74841: xorl $0x2, %edx *)
| 33 => Some (3,
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Word 2 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59302) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59302) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59302)) (Word 2 32)) (Var (V_TEMP 59302))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59302)) (Word 1 32)) (Var (V_TEMP 59302))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))) (BinOp OP_XOR (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1) (Var (V_TEMP 59303))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59303)) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EAX))) LittleE 1)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_EDX))))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59304) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59303)) (Word 4 8)) (Var (V_TEMP 59303))) (Let (V_TEMP 59304) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59304)) (Word 2 8)) (Var (V_TEMP 59304))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59304)) (Word 1 8)) (Var (V_TEMP 59304))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59303))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59305))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59305))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59305))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59306) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59306) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59306)) (Word 2 32)) (Var (V_TEMP 59306))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59306)) (Word 1 32)) (Var (V_TEMP 59306))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x7484f: xorl %edx, %edx *)
| 47 => Some (2,
    Move R_EDX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0x74851: movl (%eax), %ecx *)
| 49 => Some (2,
    Move R_ECX (Load (Var V_MEM32) (Var R_EAX) LittleE 4)
  )

(* 0x74853: addl $0x4, %eax *)
| 51 => Some (3,
    Move (V_TEMP 59307) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 59308) (Word 4 32) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59308))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59307))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59307))) (Cast CAST_HIGH 1 (Var (V_TEMP 59308)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59307))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59307))) (Var (V_TEMP 59308))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59309) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59309) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59309)) (Word 2 32)) (Var (V_TEMP 59309))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59309)) (Word 1 32)) (Var (V_TEMP 59309))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x74856: subl %ecx, %edx *)
| 54 => Some (2,
    Move (V_TEMP 59310) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59310)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59310)) (Cast CAST_LOW 32 (Var R_ECX))) (BinOp OP_XOR (Var (V_TEMP 59310)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59310))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59311) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59311) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59311)) (Word 2 32)) (Var (V_TEMP 59311))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59311)) (Word 1 32)) (Var (V_TEMP 59311))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74858: addl $0xfefefeff, %ecx *)
| 56 => Some (6,
    Move (V_TEMP 59312) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59313) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59313))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59312))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59312))) (Cast CAST_HIGH 1 (Var (V_TEMP 59313)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59312))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59312))) (Var (V_TEMP 59313))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59314) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59314) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59314)) (Word 2 32)) (Var (V_TEMP 59314))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59314)) (Word 1 32)) (Var (V_TEMP 59314))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x7485e: decl %edx *)
| 62 => Some (1,
    Move (V_TEMP 59315) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59315)) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 59315)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59315))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59316) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59316) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59316)) (Word 2 32)) (Var (V_TEMP 59316))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59316)) (Word 1 32)) (Var (V_TEMP 59316))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
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
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59317) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59317) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59317)) (Word 2 32)) (Var (V_TEMP 59317))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59317)) (Word 1 32)) (Var (V_TEMP 59317))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74863: andl $0x1010100, %edx *)
| 67 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59318) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59318) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59318)) (Word 2 32)) (Var (V_TEMP 59318))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59318)) (Word 1 32)) (Var (V_TEMP 59318))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59320))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59319))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59319))) (Cast CAST_HIGH 1 (Var (V_TEMP 59320)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59319))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59319))) (Var (V_TEMP 59320))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59321) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59321) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59321)) (Word 2 32)) (Var (V_TEMP 59321))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59321)) (Word 1 32)) (Var (V_TEMP 59321))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x74870: subl %ecx, %edx *)
| 80 => Some (2,
    Move (V_TEMP 59322) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59322)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59322)) (Cast CAST_LOW 32 (Var R_ECX))) (BinOp OP_XOR (Var (V_TEMP 59322)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59322))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59323) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59323) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59323)) (Word 2 32)) (Var (V_TEMP 59323))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59323)) (Word 1 32)) (Var (V_TEMP 59323))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74872: addl $0xfefefeff, %ecx *)
| 82 => Some (6,
    Move (V_TEMP 59324) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59325) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59325))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59324))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59324))) (Cast CAST_HIGH 1 (Var (V_TEMP 59325)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59324))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59324))) (Var (V_TEMP 59325))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59326) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59326) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59326)) (Word 2 32)) (Var (V_TEMP 59326))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59326)) (Word 1 32)) (Var (V_TEMP 59326))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74878: decl %edx *)
| 88 => Some (1,
    Move (V_TEMP 59327) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59327)) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 59327)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59327))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59328) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59328) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59328)) (Word 2 32)) (Var (V_TEMP 59328))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59328)) (Word 1 32)) (Var (V_TEMP 59328))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
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
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59329) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59329) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59329)) (Word 2 32)) (Var (V_TEMP 59329))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59329)) (Word 1 32)) (Var (V_TEMP 59329))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x7487d: andl $0x1010100, %edx *)
| 93 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59330) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59330) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59330)) (Word 2 32)) (Var (V_TEMP 59330))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59330)) (Word 1 32)) (Var (V_TEMP 59330))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59332))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59331))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59331))) (Cast CAST_HIGH 1 (Var (V_TEMP 59332)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59331))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59331))) (Var (V_TEMP 59332))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59333) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59333) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59333)) (Word 2 32)) (Var (V_TEMP 59333))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59333)) (Word 1 32)) (Var (V_TEMP 59333))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x7488a: subl %ecx, %edx *)
| 106 => Some (2,
    Move (V_TEMP 59334) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59334)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59334)) (Cast CAST_LOW 32 (Var R_ECX))) (BinOp OP_XOR (Var (V_TEMP 59334)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59334))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59335) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59335) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59335)) (Word 2 32)) (Var (V_TEMP 59335))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59335)) (Word 1 32)) (Var (V_TEMP 59335))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x7488c: addl $0xfefefeff, %ecx *)
| 108 => Some (6,
    Move (V_TEMP 59336) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59337) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59337))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59336))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59336))) (Cast CAST_HIGH 1 (Var (V_TEMP 59337)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59336))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59336))) (Var (V_TEMP 59337))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59338) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59338) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59338)) (Word 2 32)) (Var (V_TEMP 59338))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59338)) (Word 1 32)) (Var (V_TEMP 59338))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x74892: decl %edx *)
| 114 => Some (1,
    Move (V_TEMP 59339) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59339)) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 59339)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59339))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59340) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59340) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59340)) (Word 2 32)) (Var (V_TEMP 59340))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59340)) (Word 1 32)) (Var (V_TEMP 59340))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
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
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59341) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59341) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59341)) (Word 2 32)) (Var (V_TEMP 59341))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59341)) (Word 1 32)) (Var (V_TEMP 59341))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x74897: andl $0x1010100, %edx *)
| 119 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59342) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59342) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59342)) (Word 2 32)) (Var (V_TEMP 59342))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59342)) (Word 1 32)) (Var (V_TEMP 59342))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59344))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59343))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59343))) (Cast CAST_HIGH 1 (Var (V_TEMP 59344)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59343))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59343))) (Var (V_TEMP 59344))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59345) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59345) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59345)) (Word 2 32)) (Var (V_TEMP 59345))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59345)) (Word 1 32)) (Var (V_TEMP 59345))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748a4: subl %ecx, %edx *)
| 132 => Some (2,
    Move (V_TEMP 59346) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59346)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59346)) (Cast CAST_LOW 32 (Var R_ECX))) (BinOp OP_XOR (Var (V_TEMP 59346)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59346))) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59347) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59347) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59347)) (Word 2 32)) (Var (V_TEMP 59347))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59347)) (Word 1 32)) (Var (V_TEMP 59347))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x748a6: addl $0xfefefeff, %ecx *)
| 134 => Some (6,
    Move (V_TEMP 59348) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move (V_TEMP 59349) (Word 4278124287 32) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59349))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59348))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59348))) (Cast CAST_HIGH 1 (Var (V_TEMP 59349)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59348))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59348))) (Var (V_TEMP 59349))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59350) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59350) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59350)) (Word 2 32)) (Var (V_TEMP 59350))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59350)) (Word 1 32)) (Var (V_TEMP 59350))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x748ac: decl %edx *)
| 140 => Some (1,
    Move (V_TEMP 59351) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59351)) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 59351)) (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 59351))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59352) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59352) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59352)) (Word 2 32)) (Var (V_TEMP 59352))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59352)) (Word 1 32)) (Var (V_TEMP 59352))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
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
    Move R_EDX (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59353) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59353) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59353)) (Word 2 32)) (Var (V_TEMP 59353))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59353)) (Word 1 32)) (Var (V_TEMP 59353))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0x748b1: andl $0x1010100, %edx *)
| 145 => Some (6,
    Move R_EDX (BinOp OP_AND (Cast CAST_LOW 32 (Var R_EDX)) (Word 16843008 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59354) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 59354) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59354)) (Word 2 32)) (Var (V_TEMP 59354))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59354)) (Word 1 32)) (Var (V_TEMP 59354))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
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
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59355)) (Word 4 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59355)) (Word 4 32)) (BinOp OP_XOR (Var (V_TEMP 59355)) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59355))) (Word 4 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59356) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59356) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59356)) (Word 2 32)) (Var (V_TEMP 59356))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59356)) (Word 1 32)) (Var (V_TEMP 59356))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748bc: subl $0xfefefeff, %ecx *)
| 156 => Some (6,
    Move (V_TEMP 59357) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 4278124287 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59357)) (Word 4278124287 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59357)) (Word 4278124287 32)) (BinOp OP_XOR (Var (V_TEMP 59357)) (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 59357))) (Word 4278124287 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59358) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59358) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59358)) (Word 2 32)) (Var (V_TEMP 59358))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59358)) (Word 1 32)) (Var (V_TEMP 59358))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0x748c2: cmpb $0x0, %cl *)
| 162 => Some (3,
    Move (V_TEMP 59359) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 59359))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59359)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Word 0 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59360) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59359)) (Word 4 8)) (Var (V_TEMP 59359))) (Let (V_TEMP 59360) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59360)) (Word 2 8)) (Var (V_TEMP 59360))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59360)) (Word 1 8)) (Var (V_TEMP 59360))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59359))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59361))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59361))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59361))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59362) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59362) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59362)) (Word 2 32)) (Var (V_TEMP 59362))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59362)) (Word 1 32)) (Var (V_TEMP 59362))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748c8: testb %ch, %ch *)
| 168 => Some (2,
    Move (V_TEMP 59363) (BinOp OP_AND (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX)))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59364) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59363)) (Word 4 8)) (Var (V_TEMP 59363))) (Let (V_TEMP 59364) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59364)) (Word 2 8)) (Var (V_TEMP 59364))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59364)) (Word 1 8)) (Var (V_TEMP 59364))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59363))) $;
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
    Move R_ECX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (BinOp OP_AND (Word 16 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32)))) $;
    Move R_CF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_CF) (Cast CAST_HIGH 1 (BinOp OP_LSHIFT (Var (V_TEMP 59365)) (BinOp OP_MINUS (Word 32 32) (Var (V_TEMP 59366)))))) $;
    Move R_OF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_OF) (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 1 32)) (Cast CAST_HIGH 1 (Var (V_TEMP 59365))) (Unknown 1))) $;
    Move R_SF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_SF) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_ZF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_ZF) (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))) $;
    Move R_PF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_PF) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59367) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 59367) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59367)) (Word 2 32)) (Var (V_TEMP 59367))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59367)) (Word 1 32)) (Var (V_TEMP 59367)))))))) $;
    Move R_AF (Ite (BinOp OP_EQ (Var (V_TEMP 59366)) (Word 0 32)) (Var R_AF) (Unknown 1))
  )

(* 0x748cf: incl %eax *)
| 175 => Some (1,
    Move (V_TEMP 59368) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59368))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59368))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59368))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59369) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59369) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59369)) (Word 2 32)) (Var (V_TEMP 59369))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59369)) (Word 1 32)) (Var (V_TEMP 59369))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748d0: cmpb $0x0, %cl *)
| 176 => Some (3,
    Move (V_TEMP 59370) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Word 0 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX))) (Var (V_TEMP 59370))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59370)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_ECX)))) (Word 0 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59371) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59370)) (Word 4 8)) (Var (V_TEMP 59370))) (Let (V_TEMP 59371) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59371)) (Word 2 8)) (Var (V_TEMP 59371))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59371)) (Word 1 8)) (Var (V_TEMP 59371))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59370))) $;
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
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 59372))) (Cast CAST_HIGH 1 (Word 1 32))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 59372))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59372))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59373) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59373) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59373)) (Word 2 32)) (Var (V_TEMP 59373))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59373)) (Word 1 32)) (Var (V_TEMP 59373))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748d6: subl 0x4(%esp), %eax *)
| 182 => Some (4,
    Move (V_TEMP 59374) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) LittleE 4)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59374)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) LittleE 4)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59374)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) LittleE 4)) (BinOp OP_XOR (Var (V_TEMP 59374)) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 59374))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) LittleE 4)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 59375) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 59375) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59375)) (Word 2 32)) (Var (V_TEMP 59375))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59375)) (Word 1 32)) (Var (V_TEMP 59375))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x748da: retl *)
| 186 => Some (1,
    Move (V_TEMP 59376) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 59376))
  )

| _ => None
end.
