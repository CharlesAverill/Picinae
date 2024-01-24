Require Import Picinae_i386.
Require Import NArith.
Open Scope N.
Open Scope i386_scope.

Definition strcmp_i386 : program := fun _ a => match a with

(* 0xc0000080: movl 0x4(%esp), %ecx *)
| 0 => Some (4,
    Move R_ECX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) LittleE 4)
  )

(* 0xc0000084: movl 0x8(%esp), %edx *)
| 4 => Some (4,
    Move R_EDX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 8 32)) LittleE 4)
  )

(* 0xc0000088: movb (%ecx), %al *)
| 8 => Some (2,
    Move R_EAX (Concat (Cast CAST_HIGH 24 (Var R_EAX)) (Load (Var V_MEM32) (Var R_ECX) LittleE 1))
  )

(* 0xc000008a: cmpb (%edx), %al *)
| 10 => Some (2, 
    Move (V_TEMP 0 (* v19 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX))) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) LittleE 1)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX))) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) LittleE 1)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX))) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) LittleE 1)) (BinOp OP_XOR (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX))) (Var (V_TEMP 0 (* v19 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 0 (* v19 *))) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX)))) (Load (Var V_MEM32) (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EDX))) LittleE 1)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 1 (* v20 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 0 (* v19 *))) (Word 4 8)) (Var (V_TEMP 0 (* v19 *)))) (Let (V_TEMP 1 (* v20 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v20 *))) (Word 2 8)) (Var (V_TEMP 1 (* v20 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 1 (* v20 *))) (Word 1 8)) (Var (V_TEMP 1 (* v20 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 0 (* v19 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 0 (* v19 *))))
  )

(* 0xc000008c: jne 0x9 *)
| 12 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 23 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000008e: incl %ecx *)
| 14 => Some (1, 
    Move (V_TEMP 2 (* v22 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ECX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ECX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v22 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v22 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ECX)) (Var (V_TEMP 2 (* v22 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* v23 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ECX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ECX))) (Let (V_TEMP 3 (* v23 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v23 *))) (Word 2 32)) (Var (V_TEMP 3 (* v23 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v23 *))) (Word 1 32)) (Var (V_TEMP 3 (* v23 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ECX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ECX)))
  )

(* 0xc000008f: incl %edx *)
| 15 => Some (1, 
    Move (V_TEMP 4 (* v24 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDX)) (Word 1 32)) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v24 *)))) (Word 0 1)) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v24 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDX)) (Var (V_TEMP 4 (* v24 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 5 (* v25 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 5 (* v25 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v25 *))) (Word 2 32)) (Var (V_TEMP 5 (* v25 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* v25 *))) (Word 1 32)) (Var (V_TEMP 5 (* v25 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX)))
  )

(* 0xc0000090: testb %al, %al *)
| 16 => Some (2, 
    Move (V_TEMP 6 (* v26 *)) (Cast CAST_LOW 8 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v27 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v26 *))) (Word 4 8)) (Var (V_TEMP 6 (* v26 *)))) (Let (V_TEMP 7 (* v27 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v27 *))) (Word 2 8)) (Var (V_TEMP 7 (* v27 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v27 *))) (Word 1 8)) (Var (V_TEMP 7 (* v27 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v26 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 6 (* v26 *))))
  )

(* 0xc0000092: jne -0xc *)
| 18 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 8 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000094: xorl %eax, %eax *)
| 20 => Some (2, 
    Move R_EAX (Word 0 32) $;
    Move R_AF (Unknown 1) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0xc0000096: retl *)
| 22 => Some (1, 
    Move (V_TEMP 8 (* v21 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 8 (* v21 *)))
  )

(* 0xc0000097: movl $0x1, %eax *)
| 23 => Some (5,
    Move R_EAX (Word 1 32)
  )

(* 0xc000009c: movl $0xffffffff, %ecx *)
| 28 => Some (5,
    Move R_ECX (Word 4294967295 32)
  )

(* 0xc00000a1: cmovbl %ecx, %eax *)
| 33 => Some (3,
    Move R_EAX (Ite (Var R_CF) (Cast CAST_LOW 32 (Var R_ECX)) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0xc00000a4: retl *)
| 36 => Some (1, 
    Move (V_TEMP 9 (* v28 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 9 (* v28 *)))
  )

| _ => None
end.
