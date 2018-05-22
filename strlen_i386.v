Require Import Bap_i386.
Import BAPx86.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition strlen_i386 : program := fun a => match a with

(* 0x74820: movl 0x4(%esp), %eax *)
| 0 => Some (4,
    Move (Va (R_EAX) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Var (Va (R_ESP) (NumT 32))) (Word (4, 32))) LittleE 32)
  )

(* 0x74824: movl $0x3, %edx *)
| 4 => Some (5,
    Move (Va (R_EDX) (NumT 32)) (Word (3, 32))
  )

(* 0x74829: andl %eax, %edx *)
| 9 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_AND (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59293) (* v468675 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59293) (* v468675 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59293) (* v468675 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59293) (* v468675 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59293) (* v468675 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59293) (* v468675 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x7482b: je 0x24 *)
| 11 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (49, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7482d: jp 0x17 *)
| 13 => Some (2,
    If (Var (Va (R_PF) (NumT 1))) (
      Jmp (Word (38, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7482f: cmpb %dh, (%eax) *)
| 15 => Some (2,
    Move (Va (V_TEMP (59294) (* v404347 *)) (NumT 8)) (BinOp OP_MINUS (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 8)) (BinOp OP_AND (Word (16, 8)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8))) (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59295) (* v404348 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8)))) (Let (Va (V_TEMP (59295) (* v404348 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59295) (* v404348 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59295) (* v404348 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59295) (* v404348 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59295) (* v404348 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59294) (* v404347 *)) (NumT 8))))
  )

(* 0x74831: je 0x9f *)
| 17 => Some (6,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74837: incl %eax *)
| 23 => Some (1,
    Move (Va (V_TEMP (59296) (* v413198 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59296) (* v413198 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59296) (* v413198 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59296) (* v413198 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59297) (* v413199 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59297) (* v413199 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59297) (* v413199 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59297) (* v413199 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59297) (* v413199 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59297) (* v413199 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x74838: cmpb %dh, (%eax) *)
| 24 => Some (2,
    Move (Va (V_TEMP (59298) (* v413200 *)) (NumT 8)) (BinOp OP_MINUS (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 8)) (BinOp OP_AND (Word (16, 8)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8))) (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59299) (* v413201 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8)))) (Let (Va (V_TEMP (59299) (* v413201 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59299) (* v413201 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59299) (* v413201 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59299) (* v413201 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59299) (* v413201 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59298) (* v413200 *)) (NumT 8))))
  )

(* 0x7483a: je 0x96 *)
| 26 => Some (6,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74840: incl %eax *)
| 32 => Some (1,
    Move (Va (V_TEMP (59300) (* v418551 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59300) (* v418551 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59300) (* v418551 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59300) (* v418551 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59301) (* v418552 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59301) (* v418552 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59301) (* v418552 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59301) (* v418552 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59301) (* v418552 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59301) (* v418552 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x74841: xorl $0x2, %edx *)
| 33 => Some (3,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (2, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59302) (* v418553 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59302) (* v418553 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59302) (* v418553 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59302) (* v418553 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59302) (* v418553 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59302) (* v418553 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74844: je 0xb *)
| 36 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (49, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74846: cmpb %dh, (%eax) *)
| 38 => Some (2,
    Move (Va (V_TEMP (59303) (* v502620 *)) (NumT 8)) (BinOp OP_MINUS (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) (BinOp OP_XOR (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8) (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 8)) (BinOp OP_AND (Word (16, 8)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8))) (Load (Var (Va (V_MEM32) (MemT 32))) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) LittleE 8)) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59304) (* v502621 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8)))) (Let (Va (V_TEMP (59304) (* v502621 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59304) (* v502621 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59304) (* v502621 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59304) (* v502621 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59304) (* v502621 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59303) (* v502620 *)) (NumT 8))))
  )

(* 0x74848: je 0x88 *)
| 40 => Some (6,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7484e: incl %eax *)
| 46 => Some (1,
    Move (Va (V_TEMP (59305) (* v492082 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59305) (* v492082 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59305) (* v492082 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59305) (* v492082 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59306) (* v492083 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59306) (* v492083 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59306) (* v492083 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59306) (* v492083 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59306) (* v492083 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59306) (* v492083 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x7484f: xorl %edx, %edx *)
| 47 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (Word (0, 32)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word (1, 1)) $;
    Move (Va (R_PF) (NumT 1)) (Word (1, 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_SF) (NumT 1)) (Word (0, 1))
  )

(* 0x74851: movl (%eax), %ecx *)
| 49 => Some (2,
    Move (Va (R_ECX) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_EAX) (NumT 32))) LittleE 32)
  )

(* 0x74853: addl $0x4, %eax *)
| 51 => Some (3,
    Move (Va (V_TEMP (59307) (* v582794 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (V_TEMP (59308) (* v582795 *)) (NumT 32)) (Word (4, 32)) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59308) (* v582795 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59307) (* v582794 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59307) (* v582794 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59308) (* v582795 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59307) (* v582794 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59307) (* v582794 *)) (NumT 32)))) (Var (Va (V_TEMP (59308) (* v582795 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59309) (* v582796 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59309) (* v582796 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59309) (* v582796 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59309) (* v582796 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59309) (* v582796 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59309) (* v582796 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x74856: subl %ecx, %edx *)
| 54 => Some (2,
    Move (Va (V_TEMP (59310) (* v582797 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59310) (* v582797 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59310) (* v582797 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (BinOp OP_XOR (Var (Va (V_TEMP (59310) (* v582797 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59310) (* v582797 *)) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59311) (* v582798 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59311) (* v582798 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59311) (* v582798 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59311) (* v582798 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59311) (* v582798 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59311) (* v582798 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74858: addl $0xfefefeff, %ecx *)
| 56 => Some (6,
    Move (Va (V_TEMP (59312) (* v582799 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (V_TEMP (59313) (* v582800 *)) (NumT 32)) (Word (4278124287, 32)) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59313) (* v582800 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59312) (* v582799 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59312) (* v582799 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59313) (* v582800 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59312) (* v582799 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59312) (* v582799 *)) (NumT 32)))) (Var (Va (V_TEMP (59313) (* v582800 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59314) (* v582801 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59314) (* v582801 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59314) (* v582801 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59314) (* v582801 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59314) (* v582801 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59314) (* v582801 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))
  )

(* 0x7485e: decl %edx *)
| 62 => Some (1,
    Move (Va (V_TEMP (59315) (* v582802 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59315) (* v582802 *)) (NumT 32))) (Word (1, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59315) (* v582802 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59315) (* v582802 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59316) (* v582803 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59316) (* v582803 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59316) (* v582803 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59316) (* v582803 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59316) (* v582803 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59316) (* v582803 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x7485f: jae 0x58 *)
| 63 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_CF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74861: xorl %ecx, %edx *)
| 65 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59317) (* v506130 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59317) (* v506130 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59317) (* v506130 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59317) (* v506130 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59317) (* v506130 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59317) (* v506130 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74863: andl $0x1010100, %edx *)
| 67 => Some (6,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_AND (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (16843008, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59318) (* v506131 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59318) (* v506131 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59318) (* v506131 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59318) (* v506131 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59318) (* v506131 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59318) (* v506131 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74869: jne 0x4e *)
| 73 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7486b: movl (%eax), %ecx *)
| 75 => Some (2,
    Move (Va (R_ECX) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_EAX) (NumT 32))) LittleE 32)
  )

(* 0x7486d: addl $0x4, %eax *)
| 77 => Some (3,
    Move (Va (V_TEMP (59319) (* v411206 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (V_TEMP (59320) (* v411207 *)) (NumT 32)) (Word (4, 32)) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59320) (* v411207 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59319) (* v411206 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59319) (* v411206 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59320) (* v411207 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59319) (* v411206 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59319) (* v411206 *)) (NumT 32)))) (Var (Va (V_TEMP (59320) (* v411207 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59321) (* v411208 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59321) (* v411208 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59321) (* v411208 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59321) (* v411208 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59321) (* v411208 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59321) (* v411208 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x74870: subl %ecx, %edx *)
| 80 => Some (2,
    Move (Va (V_TEMP (59322) (* v411209 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59322) (* v411209 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59322) (* v411209 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (BinOp OP_XOR (Var (Va (V_TEMP (59322) (* v411209 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59322) (* v411209 *)) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59323) (* v411210 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59323) (* v411210 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59323) (* v411210 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59323) (* v411210 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59323) (* v411210 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59323) (* v411210 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74872: addl $0xfefefeff, %ecx *)
| 82 => Some (6,
    Move (Va (V_TEMP (59324) (* v411211 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (V_TEMP (59325) (* v411212 *)) (NumT 32)) (Word (4278124287, 32)) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59325) (* v411212 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59324) (* v411211 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59324) (* v411211 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59325) (* v411212 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59324) (* v411211 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59324) (* v411211 *)) (NumT 32)))) (Var (Va (V_TEMP (59325) (* v411212 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59326) (* v411213 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59326) (* v411213 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59326) (* v411213 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59326) (* v411213 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59326) (* v411213 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59326) (* v411213 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))
  )

(* 0x74878: decl %edx *)
| 88 => Some (1,
    Move (Va (V_TEMP (59327) (* v411214 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59327) (* v411214 *)) (NumT 32))) (Word (1, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59327) (* v411214 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59327) (* v411214 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59328) (* v411215 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59328) (* v411215 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59328) (* v411215 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59328) (* v411215 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59328) (* v411215 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59328) (* v411215 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74879: jae 0x3e *)
| 89 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_CF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7487b: xorl %ecx, %edx *)
| 91 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59329) (* v448738 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59329) (* v448738 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59329) (* v448738 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59329) (* v448738 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59329) (* v448738 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59329) (* v448738 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x7487d: andl $0x1010100, %edx *)
| 93 => Some (6,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_AND (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (16843008, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59330) (* v448739 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59330) (* v448739 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59330) (* v448739 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59330) (* v448739 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59330) (* v448739 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59330) (* v448739 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74883: jne 0x34 *)
| 99 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74885: movl (%eax), %ecx *)
| 101 => Some (2,
    Move (Va (R_ECX) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_EAX) (NumT 32))) LittleE 32)
  )

(* 0x74887: addl $0x4, %eax *)
| 103 => Some (3,
    Move (Va (V_TEMP (59331) (* v522674 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (V_TEMP (59332) (* v522675 *)) (NumT 32)) (Word (4, 32)) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59332) (* v522675 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59331) (* v522674 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59331) (* v522674 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59332) (* v522675 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59331) (* v522674 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59331) (* v522674 *)) (NumT 32)))) (Var (Va (V_TEMP (59332) (* v522675 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59333) (* v522676 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59333) (* v522676 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59333) (* v522676 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59333) (* v522676 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59333) (* v522676 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59333) (* v522676 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x7488a: subl %ecx, %edx *)
| 106 => Some (2,
    Move (Va (V_TEMP (59334) (* v522677 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59334) (* v522677 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59334) (* v522677 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (BinOp OP_XOR (Var (Va (V_TEMP (59334) (* v522677 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59334) (* v522677 *)) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59335) (* v522678 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59335) (* v522678 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59335) (* v522678 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59335) (* v522678 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59335) (* v522678 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59335) (* v522678 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x7488c: addl $0xfefefeff, %ecx *)
| 108 => Some (6,
    Move (Va (V_TEMP (59336) (* v522679 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (V_TEMP (59337) (* v522680 *)) (NumT 32)) (Word (4278124287, 32)) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59337) (* v522680 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59336) (* v522679 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59336) (* v522679 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59337) (* v522680 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59336) (* v522679 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59336) (* v522679 *)) (NumT 32)))) (Var (Va (V_TEMP (59337) (* v522680 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59338) (* v522681 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59338) (* v522681 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59338) (* v522681 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59338) (* v522681 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59338) (* v522681 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59338) (* v522681 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))
  )

(* 0x74892: decl %edx *)
| 114 => Some (1,
    Move (Va (V_TEMP (59339) (* v522682 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59339) (* v522682 *)) (NumT 32))) (Word (1, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59339) (* v522682 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59339) (* v522682 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59340) (* v522683 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59340) (* v522683 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59340) (* v522683 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59340) (* v522683 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59340) (* v522683 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59340) (* v522683 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74893: jae 0x24 *)
| 115 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_CF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x74895: xorl %ecx, %edx *)
| 117 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59341) (* v404747 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59341) (* v404747 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59341) (* v404747 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59341) (* v404747 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59341) (* v404747 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59341) (* v404747 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x74897: andl $0x1010100, %edx *)
| 119 => Some (6,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_AND (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (16843008, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59342) (* v404748 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59342) (* v404748 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59342) (* v404748 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59342) (* v404748 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59342) (* v404748 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59342) (* v404748 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x7489d: jne 0x1a *)
| 125 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x7489f: movl (%eax), %ecx *)
| 127 => Some (2,
    Move (Va (R_ECX) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_EAX) (NumT 32))) LittleE 32)
  )

(* 0x748a1: addl $0x4, %eax *)
| 129 => Some (3,
    Move (Va (V_TEMP (59343) (* v448080 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (V_TEMP (59344) (* v448081 *)) (NumT 32)) (Word (4, 32)) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59344) (* v448081 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59343) (* v448080 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59343) (* v448080 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59344) (* v448081 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59343) (* v448080 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59343) (* v448080 *)) (NumT 32)))) (Var (Va (V_TEMP (59344) (* v448081 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59345) (* v448082 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59345) (* v448082 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59345) (* v448082 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59345) (* v448082 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59345) (* v448082 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59345) (* v448082 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748a4: subl %ecx, %edx *)
| 132 => Some (2,
    Move (Va (V_TEMP (59346) (* v448083 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59346) (* v448083 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59346) (* v448083 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (BinOp OP_XOR (Var (Va (V_TEMP (59346) (* v448083 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59346) (* v448083 *)) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59347) (* v448084 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59347) (* v448084 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59347) (* v448084 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59347) (* v448084 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59347) (* v448084 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59347) (* v448084 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x748a6: addl $0xfefefeff, %ecx *)
| 134 => Some (6,
    Move (Va (V_TEMP (59348) (* v448085 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (V_TEMP (59349) (* v448086 *)) (NumT 32)) (Word (4278124287, 32)) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59349) (* v448086 *)) (NumT 32)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59348) (* v448085 *)) (NumT 32)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59348) (* v448085 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59349) (* v448086 *)) (NumT 32))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59348) (* v448085 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59348) (* v448085 *)) (NumT 32)))) (Var (Va (V_TEMP (59349) (* v448086 *)) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59350) (* v448087 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59350) (* v448087 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59350) (* v448087 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59350) (* v448087 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59350) (* v448087 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59350) (* v448087 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))
  )

(* 0x748ac: decl %edx *)
| 140 => Some (1,
    Move (Va (V_TEMP (59351) (* v448088 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) $;
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59351) (* v448088 *)) (NumT 32))) (Word (1, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59351) (* v448088 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Var (Va (V_TEMP (59351) (* v448088 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59352) (* v448089 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59352) (* v448089 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59352) (* v448089 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59352) (* v448089 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59352) (* v448089 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59352) (* v448089 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x748ad: jae 0xa *)
| 141 => Some (2,
    If (UnOp OP_NOT (Var (Va (R_CF) (NumT 1)))) (
      Jmp (Word (153, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x748af: xorl %ecx, %edx *)
| 143 => Some (2,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59353) (* v445393 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59353) (* v445393 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59353) (* v445393 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59353) (* v445393 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59353) (* v445393 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59353) (* v445393 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x748b1: andl $0x1010100, %edx *)
| 145 => Some (6,
    Move (Va (R_EDX) (NumT 32)) (BinOp OP_AND (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (16843008, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59354) (* v445394 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) (Let (Va (V_TEMP (59354) (* v445394 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59354) (* v445394 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59354) (* v445394 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59354) (* v445394 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59354) (* v445394 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EDX) (NumT 32)))))
  )

(* 0x748b7: je -0x68 *)
| 151 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (49, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x748b9: subl $0x4, %eax *)
| 153 => Some (3,
    Move (Va (V_TEMP (59355) (* v545999 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59355) (* v545999 *)) (NumT 32))) (Word (4, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59355) (* v545999 *)) (NumT 32))) (Word (4, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59355) (* v545999 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59355) (* v545999 *)) (NumT 32)))) (Word (4, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59356) (* v546000 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59356) (* v546000 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59356) (* v546000 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59356) (* v546000 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59356) (* v546000 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59356) (* v546000 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748bc: subl $0xfefefeff, %ecx *)
| 156 => Some (6,
    Move (Va (V_TEMP (59357) (* v546001 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4278124287, 32))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59357) (* v546001 *)) (NumT 32))) (Word (4278124287, 32))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59357) (* v546001 *)) (NumT 32))) (Word (4278124287, 32))) (BinOp OP_XOR (Var (Va (V_TEMP (59357) (* v546001 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Var (Va (V_TEMP (59357) (* v546001 *)) (NumT 32)))) (Word (4278124287, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59358) (* v546002 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59358) (* v546002 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59358) (* v546002 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59358) (* v546002 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59358) (* v546002 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59358) (* v546002 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))
  )

(* 0x748c2: cmpb $0x0, %cl *)
| 162 => Some (3,
    Move (Va (V_TEMP (59359) (* v546003 *)) (NumT 8)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 8)) (BinOp OP_AND (Word (16, 8)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))) (Word (0, 8))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59360) (* v546004 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8)))) (Let (Va (V_TEMP (59360) (* v546004 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59360) (* v546004 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59360) (* v546004 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59360) (* v546004 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59360) (* v546004 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59359) (* v546003 *)) (NumT 8))))
  )

(* 0x748c5: je 0xf *)
| 165 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x748c7: incl %eax *)
| 167 => Some (1,
    Move (Va (V_TEMP (59361) (* v524363 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59361) (* v524363 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59361) (* v524363 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59361) (* v524363 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59362) (* v524364 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59362) (* v524364 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59362) (* v524364 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59362) (* v524364 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59362) (* v524364 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59362) (* v524364 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748c8: testb %ch, %ch *)
| 168 => Some (2,
    Move (Va (V_TEMP (59363) (* v524365 *)) (NumT 8)) (BinOp OP_AND (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))) (Cast CAST_HIGH 8 (Cast CAST_LOW 16 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59364) (* v524366 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59363) (* v524365 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59363) (* v524365 *)) (NumT 8)))) (Let (Va (V_TEMP (59364) (* v524366 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59364) (* v524366 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59364) (* v524366 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59364) (* v524366 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59364) (* v524366 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59363) (* v524365 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59363) (* v524365 *)) (NumT 8))))
  )

(* 0x748ca: je 0xa *)
| 170 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x748cc: shrl $0x10, %ecx *)
| 172 => Some (3,
    Move (Va (V_TEMP (59365) (* orig_dest401142 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) $;
    Move (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_MINUS (Word (32, 32)) (Word (1, 32)))) $;
    Move (Va (R_ECX) (NumT 32)) (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (BinOp OP_AND (Word (16, 32)) (BinOp OP_MINUS (Word (32, 32)) (Word (1, 32))))) $;
    Move (Va (R_CF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_CF) (NumT 1))) (Cast CAST_HIGH 1 (BinOp OP_LSHIFT (Var (Va (V_TEMP (59365) (* orig_dest401142 *)) (NumT 32))) (BinOp OP_MINUS (Word (32, 32)) (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))))))) $;
    Move (Va (R_OF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_OF) (NumT 1))) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (1, 32))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59365) (* orig_dest401142 *)) (NumT 32)))) (Unknown (NumT 1)))) $;
    Move (Va (R_SF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_SF) (NumT 1))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))) $;
    Move (Va (R_ZF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_ZF) (NumT 1))) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))) $;
    Move (Va (R_PF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_PF) (NumT 1))) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59367) (* v401144 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Let (Va (V_TEMP (59367) (* v401144 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59367) (* v401144 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59367) (* v401144 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59367) (* v401144 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59367) (* v401144 *)) (NumT 32))))))))) $;
    Move (Va (R_AF) (NumT 1)) (Ite (BinOp OP_EQ (Var (Va (V_TEMP (59366) (* orig_count401143 *)) (NumT 32))) (Word (0, 32))) (Var (Va (R_AF) (NumT 1))) (Unknown (NumT 1)))
  )

(* 0x748cf: incl %eax *)
| 175 => Some (1,
    Move (Va (V_TEMP (59368) (* v401145 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59368) (* v401145 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59368) (* v401145 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59368) (* v401145 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59369) (* v401146 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59369) (* v401146 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59369) (* v401146 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59369) (* v401146 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59369) (* v401146 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59369) (* v401146 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748d0: cmpb $0x0, %cl *)
| 176 => Some (3,
    Move (Va (V_TEMP (59370) (* v401147 *)) (NumT 8)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Word (0, 8))) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32))))) (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 8)) (BinOp OP_AND (Word (16, 8)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var (Va (R_ECX) (NumT 32)))))) (Word (0, 8))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59371) (* v401148 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8))) (Word (4, 8))) (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8)))) (Let (Va (V_TEMP (59371) (* v401148 *)) (NumT 8)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59371) (* v401148 *)) (NumT 8))) (Word (2, 8))) (Var (Va (V_TEMP (59371) (* v401148 *)) (NumT 8)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59371) (* v401148 *)) (NumT 8))) (Word (1, 8))) (Var (Va (V_TEMP (59371) (* v401148 *)) (NumT 8)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 8)) (Var (Va (V_TEMP (59370) (* v401147 *)) (NumT 8))))
  )

(* 0x748d3: je 0x1 *)
| 179 => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (182, 32))
    ) (* else *) (
      Nop
    )
  )

(* 0x748d5: incl %eax *)
| 181 => Some (1,
    Move (Va (V_TEMP (59372) (* v474630 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (1, 32))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59372) (* v474630 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Word (1, 32)))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59372) (* v474630 *)) (NumT 32)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59372) (* v474630 *)) (NumT 32)))) (Word (1, 32))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59373) (* v474631 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59373) (* v474631 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59373) (* v474631 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59373) (* v474631 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59373) (* v474631 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59373) (* v474631 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748d6: subl 0x4(%esp), %eax *)
| 182 => Some (4,
    Move (Va (V_TEMP (59374) (* v410213 *)) (NumT 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) $;
    Move (Va (R_EAX) (NumT 32)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ESP) (NumT 32)))) (Word (4, 32))) LittleE 32)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (59374) (* v410213 *)) (NumT 32))) (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ESP) (NumT 32)))) (Word (4, 32))) LittleE 32)) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (59374) (* v410213 *)) (NumT 32))) (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ESP) (NumT 32)))) (Word (4, 32))) LittleE 32)) (BinOp OP_XOR (Var (Va (V_TEMP (59374) (* v410213 *)) (NumT 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16, 32)) (BinOp OP_AND (Word (16, 32)) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Var (Va (V_TEMP (59374) (* v410213 *)) (NumT 32)))) (Load (Var (Va (V_MEM32) (MemT 32))) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var (Va (R_ESP) (NumT 32)))) (Word (4, 32))) LittleE 32)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59375) (* v410214 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))) (Word (4, 32))) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) (Let (Va (V_TEMP (59375) (* v410214 *)) (NumT 32)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59375) (* v410214 *)) (NumT 32))) (Word (2, 32))) (Var (Va (V_TEMP (59375) (* v410214 *)) (NumT 32)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59375) (* v410214 *)) (NumT 32))) (Word (1, 32))) (Var (Va (V_TEMP (59375) (* v410214 *)) (NumT 32)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32))))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0, 32)) (Cast CAST_LOW 32 (Var (Va (R_EAX) (NumT 32)))))
  )

(* 0x748da: retl *)
| 186 => Some (1,
    Move (Va (V_TEMP (59376) (* v410215 *)) (NumT 32)) (Load (Var (Va (V_MEM32) (MemT 32))) (Var (Va (R_ESP) (NumT 32))) LittleE 32) $;
    Move (Va (R_ESP) (NumT 32)) (BinOp OP_PLUS (Var (Va (R_ESP) (NumT 32))) (Word (4, 32))) $;
    Jmp (Var (Va (V_TEMP (59376) (* v410215 *)) (NumT 32)))
  )

| _ => None
end.
