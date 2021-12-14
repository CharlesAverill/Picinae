Require Import Picinae_i386.
Require Import NArith.
Open Scope N.
Definition my_prog : program := fun _ a => match a with

(* 0: pushl %ebp *)
| 0 => Some (1, 
    Move (V_TEMP 0 (* #1 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 0 (* #1 *))) LittleE 4)
  )

(* 0x1: movl %esp, %ebp *)
| 1 => Some (2,
    Move R_EBP (Var R_ESP)
  )

(* 0x3: subl $0x10, %esp *)
| 3 => Some (3, 
    Move (V_TEMP 1 (* #2 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 16 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 1 (* #2 *))) (Word 16 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 1 (* #2 *))) (Word 16 32)) (BinOp OP_XOR (Var (V_TEMP 1 (* #2 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 1 (* #2 *)))) (Word 16 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 32)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 32)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x6: movl $0x0, -0x4(%ebp) *)
| 6 => Some (7,
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var R_EBP) (Word 4294967292 32)) (Word 0 32) LittleE 4)
  )

(* 0xd: jmp 0x4 *)
| 13 => Some (2,
    Jmp (Word 19 32)
  )

(* 0xf: addl $0x1, -0x4(%ebp) *)
| 15 => Some (4, Nop
    (*
    Move (V_TEMP 4 (* #7 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) $;
    Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) (BinOp OP_PLUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Word 1 32)) LittleE 4) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Var (V_TEMP 4 (* #7 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* #7 *)))) (Word 0 1)) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* #7 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* #7 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Var (V_TEMP 4 (* #7 *)))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Word 4 32)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 32)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 32)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4))
     *)
  )

(* 0x13: cmpl $0xf423f, -0x4(%ebp) *)
| 19 => Some (7, 
    Move (V_TEMP 5 (* #5 *)) (BinOp OP_MINUS (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Word 999999 32)) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Word 999999 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Word 999999 32)) (BinOp OP_XOR (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4) (Var (V_TEMP 5 (* #5 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 5 (* #5 *))) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBP)) (Word 4294967292 32)) LittleE 4)) (Word 999999 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* #5 *))) (Word 4 32)) (Var (V_TEMP 5 (* #5 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 32)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 32)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* #5 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 5 (* #5 *))))
  )

(* 0x1a: jle -0xd *)
| 26 => Some (2,
    If (BinOp OP_OR (Var R_ZF) (BinOp OP_AND (BinOp OP_OR (Var R_SF) (Var R_OF)) (UnOp OP_NOT (BinOp OP_AND (Var R_SF) (Var R_OF))))) (
      Jmp (Word 15 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x1c: movl $0x2a, %eax *)
| 28 => Some (5,
    Move R_EAX (Word 42 32)
  )

(* 0x21: leave *)
| 33 => Some (1, 
    Move R_ESP (Var R_EBP) $;
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x22: retl *)
| 34 => Some (1, 
    Move (V_TEMP 6 (* #10 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 6 (* #10 *)))
  )

| _ => None
end.
