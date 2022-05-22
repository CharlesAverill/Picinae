Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition my_prog : program := fun _ a => match a with
(* 0: pushq %rbp *)
| 0 => Some (1, 
    Move (V_TEMP 0 (* #1 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0 (* #1 *))) LittleE 8)
  )

(* 0x1: movq %rsp, %rbp *)
| 1 => Some (3,
    Move R_RBP (Var R_RSP)
  )

(* 0x4: subq $0x50, %rsp *)
| 4 => Some (4, 
    Move (V_TEMP 1 (* #2 *)) (Var R_RSP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 80 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 1 (* #2 *))) (Word 80 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 1 (* #2 *))) (Word 80 64)) (BinOp OP_XOR (Var (V_TEMP 1 (* #2 *))) (Var R_RSP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSP) (Var (V_TEMP 1 (* #2 *)))) (Word 80 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x8: movq %rdi, -0x38(%rbp) *)
| 8 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) (Var R_RDI) LittleE 8)
  )

(* 0xc: movq %rsi, -0x40(%rbp) *)
| 12 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) (Var R_RSI) LittleE 8)
  )

(* 0x10: movq %rdx, -0x48(%rbp) *)
| 16 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) (Var R_RDX) LittleE 8)
  )

(* 0x14: movl %ecx, -0x4c(%rbp) *)
| 20 => Some (3,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551540 64)) (Cast CAST_LOW 32 (Var R_RCX)) LittleE 4)
  )

(* 0x17: movq $0x0, -0x8(%rbp) *)
| 23 => Some (8,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (Word 0 64) LittleE 8)
  )

(* 0x1f: movq -0x48(%rbp), %rax *)
| 31 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x23: movl 0x10(%rax), %eax *)
| 35 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 16 64)) LittleE 4))
  )

(* 0x26: cltq *)
| 38 => Some (2,
    Move R_RAX (Cast CAST_SIGNED 64 (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x28: movq %rax, -0x18(%rbp) *)
| 40 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) (Var R_RAX) LittleE 8)
  )

(* 0x2c: movq -0x48(%rbp), %rax *)
| 44 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x30: movq 0x20(%rax), %rax *)
| 48 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 32 64)) LittleE 8)
  )

(* 0x34: testq %rax, %rax *)
| 52 => Some (3, 
    Move (V_TEMP 4 (* #5 *)) (Var R_RAX) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* #5 *))) (Word 4 64)) (Var (V_TEMP 4 (* #5 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* #5 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 4 (* #5 *))))
  )

(* 0x37: je 0x18 *)
| 55 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 81 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x39: movq -0x48(%rbp), %rax *)
| 57 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x3d: movq 0x20(%rax), %rax *)
| 61 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 32 64)) LittleE 8)
  )

(* 0x41: cmpq %rax, -0x18(%rbp) *)
| 65 => Some (4, 
    Move (V_TEMP 5 (* #154 *)) (BinOp OP_MINUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var (V_TEMP 5 (* #154 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 5 (* #154 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (Var R_RAX)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 5 (* #154 *))) (Word 4 64)) (Var (V_TEMP 5 (* #154 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* #154 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 5 (* #154 *))))
  )

(* 0x45: jbe 0xa *)
| 69 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 81 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x47: movl $0xfffffaec, %eax *)
| 71 => Some (5,
    Move R_RAX (Word 4294965996 64)
  )

(* 0x4c: jmp 0x327 *)
| 76 => Some (5,
    Jmp (Word 888 64)
  )

(* 0x51: movq -0x48(%rbp), %rax *)
| 81 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x55: movl 0x28(%rax), %eax *)
| 85 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 40 64)) LittleE 4))
  )

(* 0x58: cmpl $0x2, %eax *)
| 88 => Some (3, 
    Move (V_TEMP 6 (* #7 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Var (V_TEMP 6 (* #7 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 6 (* #7 *))) (Cast CAST_LOW 32 (Var R_RAX))) (Word 2 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* #7 *))) (Word 4 32)) (Var (V_TEMP 6 (* #7 *)))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* #7 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 6 (* #7 *))))
  )

(* 0x5b: jne 0xa1 *)
| 91 => Some (6,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 258 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x61: jmp 0x5 *)
| 97 => Some (2,
    Jmp (Word 104 64)
  )

(* 0x63: subq $0x1, -0x18(%rbp) *)
| 99 => Some (5, 
    Move (V_TEMP 9 (* #151 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) (BinOp OP_MINUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 9 (* #151 *))) (Word 1 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 9 (* #151 *))) (Word 1 64)) (BinOp OP_XOR (Var (V_TEMP 9 (* #151 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var (V_TEMP 9 (* #151 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8))
  )

(* 0x68: cmpq $0x0, -0x18(%rbp) *)
| 104 => Some (5, 
    Move (V_TEMP 10 (* #117 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 0 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var (V_TEMP 10 (* #117 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (Var (V_TEMP 10 (* #117 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* #117 *))) (Word 4 64)) (Var (V_TEMP 10 (* #117 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* #117 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 10 (* #117 *))))
  )

(* 0x6d: je 0x1a *)
| 109 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 137 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x6f: movq -0x48(%rbp), %rax *)
| 111 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x73: movq 0x8(%rax), %rax *)
| 115 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0x77: movq -0x18(%rbp), %rdx *)
| 119 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)
  )

(* 0x7b: subq $0x1, %rdx *)
| 123 => Some (4, 
    Move (V_TEMP 11 (* #143 *)) (Var R_RDX) $;
    Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 1 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 11 (* #143 *))) (Word 1 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 11 (* #143 *))) (Word 1 64)) (BinOp OP_XOR (Var (V_TEMP 11 (* #143 *))) (Var R_RDX)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RDX) (Var (V_TEMP 11 (* #143 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RDX) (Word 4 64)) (Var R_RDX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RDX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RDX))
  )

(* 0x7f: addq %rdx, %rax *)
| 127 => Some (3, 
    Move (V_TEMP 12 (* #146 *)) (Var R_RAX) $;
    Move (V_TEMP 13 (* #147 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 13 (* #147 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 12 (* #146 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* #146 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 13 (* #147 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* #146 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 12 (* #146 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 12 (* #146 *)))) (Var (V_TEMP 13 (* #147 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x82: movzbl (%rax), %eax *)
| 130 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x85: cmpb $-0x1, %al *)
| 133 => Some (2, 
    Move (V_TEMP 14 (* #149 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Var R_RAX)) (Word 255 8)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Var R_RAX)) (Word 255 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Word 255 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Var (V_TEMP 14 (* #149 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 14 (* #149 *))) (Cast CAST_LOW 8 (Var R_RAX))) (Word 255 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 16 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 14 (* #149 *))) (Word 4 8)) (Var (V_TEMP 14 (* #149 *)))) (Let (V_TEMP 15 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* $1 *))) (Word 2 8)) (Var (V_TEMP 16 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* $2 *))) (Word 1 8)) (Var (V_TEMP 15 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 14 (* #149 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 14 (* #149 *))))
  )

(* 0x87: je -0x26 *)
| 135 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 99 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x89: cmpq $0xc, -0x18(%rbp) *)
| 137 => Some (5, 
    Move (V_TEMP 17 (* #119 *)) (BinOp OP_MINUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 12 64)) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 12 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Word 12 64)) (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var (V_TEMP 17 (* #119 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 17 (* #119 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (Word 12 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* #119 *))) (Word 4 64)) (Var (V_TEMP 17 (* #119 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 17 (* #119 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 17 (* #119 *))))
  )

(* 0x8e: jbe 0xa *)
| 142 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 154 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x90: movl $0xfffffaec, %eax *)
| 144 => Some (5,
    Move R_RAX (Word 4294965996 64)
  )

(* 0x95: jmp 0x2de *)
| 149 => Some (5,
    Jmp (Word 888 64)
  )

(* 0x9a: movq $0x0, -0x8(%rbp) *)
| 154 => Some (8,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (Word 0 64) LittleE 8)
  )

(* 0xa2: jmp 0x3b *)
| 162 => Some (2,
    Jmp (Word 223 64)
  )

(* 0xa4: movq -0x48(%rbp), %rax *)
| 164 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0xa8: movq 0x8(%rax), %rdx *)
| 168 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0xac: movq -0x8(%rbp), %rax *)
| 172 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0xb0: addq %rdx, %rax *)
| 176 => Some (3, 
    Move (V_TEMP 18 (* #123 *)) (Var R_RAX) $;
    Move (V_TEMP 19 (* #124 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 19 (* #124 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 18 (* #123 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* #123 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 19 (* #124 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* #123 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* #123 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 18 (* #123 *)))) (Var (V_TEMP 19 (* #124 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0xb3: movzbl (%rax), %eax *)
| 179 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0xb6: cmpb $0x2f, %al *)
| 182 => Some (2, 
    Move (V_TEMP 20 (* #126 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Var R_RAX)) (Word 47 8)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Var R_RAX)) (Word 47 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Word 47 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Var (V_TEMP 20 (* #126 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 20 (* #126 *))) (Cast CAST_LOW 8 (Var R_RAX))) (Word 47 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 16 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 20 (* #126 *))) (Word 4 8)) (Var (V_TEMP 20 (* #126 *)))) (Let (V_TEMP 15 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* $1 *))) (Word 2 8)) (Var (V_TEMP 16 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* $2 *))) (Word 1 8)) (Var (V_TEMP 15 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 20 (* #126 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 20 (* #126 *))))
  )

(* 0xb8: jbe 0x16 *)
| 184 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 208 64)
    ) (* else *) (
      Nop
    )
  )

(* 0xba: movq -0x48(%rbp), %rax *)
| 186 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0xbe: movq 0x8(%rax), %rdx *)
| 190 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0xc2: movq -0x8(%rbp), %rax *)
| 194 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0xc6: addq %rdx, %rax *)
| 198 => Some (3, 
    Move (V_TEMP 21 (* #131 *)) (Var R_RAX) $;
    Move (V_TEMP 22 (* #132 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 22 (* #132 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 21 (* #131 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 21 (* #131 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 22 (* #132 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 21 (* #131 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 21 (* #131 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 21 (* #131 *)))) (Var (V_TEMP 22 (* #132 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0xc9: movzbl (%rax), %eax *)
| 201 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0xcc: cmpb $0x39, %al *)
| 204 => Some (2, 
    Move (V_TEMP 23 (* #134 *)) (BinOp OP_MINUS (Cast CAST_LOW 8 (Var R_RAX)) (Word 57 8)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 8 (Var R_RAX)) (Word 57 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Word 57 8)) (BinOp OP_XOR (Cast CAST_LOW 8 (Var R_RAX)) (Var (V_TEMP 23 (* #134 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 8) (BinOp OP_AND (Word 16 8) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 23 (* #134 *))) (Cast CAST_LOW 8 (Var R_RAX))) (Word 57 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 16 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 23 (* #134 *))) (Word 4 8)) (Var (V_TEMP 23 (* #134 *)))) (Let (V_TEMP 15 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* $1 *))) (Word 2 8)) (Var (V_TEMP 16 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* $2 *))) (Word 1 8)) (Var (V_TEMP 15 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 23 (* #134 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 8) (Var (V_TEMP 23 (* #134 *))))
  )

(* 0xce: jbe 0xa *)
| 206 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 218 64)
    ) (* else *) (
      Nop
    )
  )

(* 0xd0: movl $0xfffffaec, %eax *)
| 208 => Some (5,
    Move R_RAX (Word 4294965996 64)
  )

(* 0xd5: jmp 0x29e *)
| 213 => Some (5,
    Jmp (Word 888 64)
  )

(* 0xda: addq $0x1, -0x8(%rbp) *)
| 218 => Some (5, 
    Move (V_TEMP 24 (* #128 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (BinOp OP_PLUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Var (V_TEMP 24 (* #128 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* #128 *)))) (Word 0 1)) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* #128 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 24 (* #128 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Var (V_TEMP 24 (* #128 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8))
  )

(* 0xdf: movq -0x8(%rbp), %rax *)
| 223 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0xe3: cmpq -0x18(%rbp), %rax *)
| 227 => Some (4, 
    Move (V_TEMP 25 (* #121 *)) (BinOp OP_MINUS (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 25 (* #121 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 25 (* #121 *))) (Var R_RAX)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 25 (* #121 *))) (Word 4 64)) (Var (V_TEMP 25 (* #121 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 25 (* #121 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 25 (* #121 *))))
  )

(* 0xe7: jb -0x45 *)
| 231 => Some (2,
    If (Var R_CF) (
      Jmp (Word 164 64)
    ) (* else *) (
      Nop
    )
  )

(* 0xe9: movq -0x18(%rbp), %rax *)
| 233 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)
  )

(* 0xed: orl $0x20, %eax *)
| 237 => Some (3, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Cast CAST_LOW 32 (Var R_RAX)) (Word 32 32))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0xf0: movl %eax, %edx *)
| 240 => Some (2,
    Move R_RDX (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0xf2: movq -0x38(%rbp), %rax *)
| 242 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0xf6: movb %dl, (%rax) *)
| 246 => Some (2,
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_LOW 8 (Var R_RDX)) LittleE 1)
  )

(* 0xf8: addq $0x1, -0x38(%rbp) *)
| 248 => Some (5, 
    Move (V_TEMP 26 (* #137 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) (BinOp OP_PLUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8) (Var (V_TEMP 26 (* #137 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* #137 *)))) (Word 0 1)) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* #137 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 26 (* #137 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8) (Var (V_TEMP 26 (* #137 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8))
  )

(* 0xfd: subq $0x1, -0x40(%rbp) *)
| 253 => Some (5, 
    Move (V_TEMP 27 (* #140 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) (BinOp OP_MINUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 27 (* #140 *))) (Word 1 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 27 (* #140 *))) (Word 1 64)) (BinOp OP_XOR (Var (V_TEMP 27 (* #140 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8) (Var (V_TEMP 27 (* #140 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8))
  )

(* 0x102: movq -0x48(%rbp), %rax *)
| 258 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x106: movl 0x28(%rax), %eax *)
| 262 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 40 64)) LittleE 4))
  )

(* 0x109: testl %eax, %eax *)
| 265 => Some (2, 
    Move (V_TEMP 28 (* #9 *)) (Cast CAST_LOW 32 (Var R_RAX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* #9 *))) (Word 4 32)) (Var (V_TEMP 28 (* #9 *)))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 28 (* #9 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 28 (* #9 *))))
  )

(* 0x10b: jne 0x3c *)
| 267 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 329 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x10d: movq -0x18(%rbp), %rax *)
| 269 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)
  )

(* 0x111: cmpq -0x40(%rbp), %rax *)
| 273 => Some (4, 
    Move (V_TEMP 29 (* #115 *)) (BinOp OP_MINUS (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)) (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 29 (* #115 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 29 (* #115 *))) (Var R_RAX)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 29 (* #115 *))) (Word 4 64)) (Var (V_TEMP 29 (* #115 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 29 (* #115 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 29 (* #115 *))))
  )

(* 0x115: jbe 0xa *)
| 277 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 289 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x117: movl $0xfffffae9, %eax *)
| 279 => Some (5,
    Move R_RAX (Word 4294965993 64)
  )

(* 0x11c: jmp 0x257 *)
| 284 => Some (5,
    Jmp (Word 888 64)
  )

(* 0x121: movq -0x48(%rbp), %rax *)
| 289 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x125: movq 0x8(%rax), %rcx *)
| 293 => Some (4,
    Move R_RCX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0x129: movq -0x18(%rbp), %rdx *)
| 297 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)
  )

(* 0x12d: movq -0x38(%rbp), %rax *)
| 301 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0x131: movq %rcx, %rsi *)
| 305 => Some (3,
    Move R_RSI (Var R_RCX)
  )

(* 0x134: movq %rax, %rdi *)
| 308 => Some (3,
    Move R_RDI (Var R_RAX)
  )

(* 0x137: callq -0x9c442e *)
| 311 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 316 64) LittleE 8) $;
    Jmp (Word 18446744073699310862 64)
  )

(* 0x13c: movq -0x18(%rbp), %rax *)
| 316 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)
  )

(* 0x140: movq %rax, -0x8(%rbp) *)
| 320 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (Var R_RAX) LittleE 8)
  )

(* 0x144: jmp 0x179 *)
| 324 => Some (5,
    Jmp (Word 706 64)
  )

(* 0x149: movq -0x48(%rbp), %rax *)
| 329 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x14d: movl 0x28(%rax), %eax *)
| 333 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 40 64)) LittleE 4))
  )

(* 0x150: cmpl $0x1, %eax *)
| 336 => Some (3, 
    Move (V_TEMP 30 (* #11 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_RAX)) (Word 1 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_RAX)) (Word 1 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Word 1 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Var (V_TEMP 30 (* #11 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 30 (* #11 *))) (Cast CAST_LOW 32 (Var R_RAX))) (Word 1 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 30 (* #11 *))) (Word 4 32)) (Var (V_TEMP 30 (* #11 *)))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* #11 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 30 (* #11 *))))
  )

(* 0x153: je 0x10 *)
| 339 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 357 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x155: movq -0x48(%rbp), %rax *)
| 341 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x159: movl 0x28(%rax), %eax *)
| 345 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 40 64)) LittleE 4))
  )

(* 0x15c: cmpl $0x2, %eax *)
| 348 => Some (3, 
    Move (V_TEMP 31 (* #113 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Word 2 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Var (V_TEMP 31 (* #113 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 31 (* #113 *))) (Cast CAST_LOW 32 (Var R_RAX))) (Word 2 32)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* #113 *))) (Word 4 32)) (Var (V_TEMP 31 (* #113 *)))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 31 (* #113 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 31 (* #113 *))))
  )

(* 0x15f: jne 0x15d *)
| 351 => Some (6,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 706 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x165: movq -0x40(%rbp), %rax *)
| 357 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551552 64)) LittleE 8)
  )

(* 0x169: addq %rax, %rax *)
| 361 => Some (3, 
    Move (V_TEMP 32 (* #13 *)) (Var R_RAX) $;
    Move (V_TEMP 33 (* #14 *)) (Var R_RAX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 33 (* #14 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 32 (* #13 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 32 (* #13 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 33 (* #14 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 32 (* #13 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 32 (* #13 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 32 (* #13 *)))) (Var (V_TEMP 33 (* #14 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x16c: cmpq %rax, -0x18(%rbp) *)
| 364 => Some (4, 
    Move (V_TEMP 34 (* #16 *)) (BinOp OP_MINUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var R_RAX)) (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8) (Var (V_TEMP 34 (* #16 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 34 (* #16 *))) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (Var R_RAX)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 34 (* #16 *))) (Word 4 64)) (Var (V_TEMP 34 (* #16 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 34 (* #16 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 34 (* #16 *))))
  )

(* 0x170: jbe 0xa *)
| 368 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 380 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x172: movl $0xfffffae9, %eax *)
| 370 => Some (5,
    Move R_RAX (Word 4294965993 64)
  )

(* 0x177: jmp 0x1fc *)
| 375 => Some (5,
    Jmp (Word 888 64)
  )

(* 0x17c: movq $0x0, -0x10(%rbp) *)
| 380 => Some (8,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) (Word 0 64) LittleE 8)
  )

(* 0x184: movq -0x10(%rbp), %rax *)
| 388 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x188: movq %rax, -0x8(%rbp) *)
| 392 => Some (4,
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (Var R_RAX) LittleE 8)
  )

(* 0x18c: jmp 0xc6 *)
| 396 => Some (5,
    Jmp (Word 599 64)
  )

(* 0x191: callq -0x9c4068 *)
| 401 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 406 64) LittleE 8) $;
    Jmp (Word 18446744073699311918 64)
  )

(* 0x196: movq (%rax), %rdx *)
| 406 => Some (3,
    Move R_RDX (Load (Var V_MEM64) (Var R_RAX) LittleE 8)
  )

(* 0x199: movq -0x48(%rbp), %rax *)
| 409 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x19d: movq 0x8(%rax), %rcx *)
| 413 => Some (4,
    Move R_RCX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0x1a1: movq -0x10(%rbp), %rax *)
| 417 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x1a5: addq %rcx, %rax *)
| 421 => Some (3, 
    Move (V_TEMP 35 (* #20 *)) (Var R_RAX) $;
    Move (V_TEMP 36 (* #21 *)) (Var R_RCX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 36 (* #21 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 35 (* #20 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 35 (* #20 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 36 (* #21 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 35 (* #20 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 35 (* #20 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 35 (* #20 *)))) (Var (V_TEMP 36 (* #21 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1a8: movzbl (%rax), %eax *)
| 424 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x1ab: movzbl %al, %eax *)
| 427 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 8 (Var R_RAX))))
  )

(* 0x1ae: addq %rax, %rax *)
| 430 => Some (3, 
    Move (V_TEMP 37 (* #23 *)) (Var R_RAX) $;
    Move (V_TEMP 38 (* #24 *)) (Var R_RAX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 38 (* #24 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 37 (* #23 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 37 (* #23 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 38 (* #24 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 37 (* #23 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 37 (* #23 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 37 (* #23 *)))) (Var (V_TEMP 38 (* #24 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1b1: addq %rdx, %rax *)
| 433 => Some (3, 
    Move (V_TEMP 39 (* #26 *)) (Var R_RAX) $;
    Move (V_TEMP 40 (* #27 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 40 (* #27 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 39 (* #26 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 39 (* #26 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 40 (* #27 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 39 (* #26 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 39 (* #26 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 39 (* #26 *)))) (Var (V_TEMP 40 (* #27 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1b4: movzwl (%rax), %eax *)
| 436 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 2)))
  )

(* 0x1b7: movzwl %ax, %eax *)
| 439 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 16 (Var R_RAX))))
  )

(* 0x1ba: andl $0x800, %eax *)
| 442 => Some (5, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Cast CAST_LOW 32 (Var R_RAX)) (Word 2048 32))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x1bf: testl %eax, %eax *)
| 447 => Some (2, 
    Move (V_TEMP 41 (* #30 *)) (Cast CAST_LOW 32 (Var R_RAX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 41 (* #30 *))) (Word 4 32)) (Var (V_TEMP 41 (* #30 *)))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 41 (* #30 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 41 (* #30 *))))
  )

(* 0x1c1: jne 0xa *)
| 449 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 461 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x1cd: movq -0x38(%rbp), %rdx *)
| 461 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0x1d1: movq -0x8(%rbp), %rax *)
| 465 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0x1d5: addq %rdx, %rax *)
| 469 => Some (3, 
    Move (V_TEMP 42 (* #32 *)) (Var R_RAX) $;
    Move (V_TEMP 43 (* #33 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 43 (* #33 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 42 (* #32 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* #32 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 43 (* #33 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* #32 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 42 (* #32 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 42 (* #32 *)))) (Var (V_TEMP 43 (* #33 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1d8: movzbl (%rax), %edx *)
| 472 => Some (3,
    Move R_RDX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x1db: movq -0x38(%rbp), %rcx *)
| 475 => Some (4,
    Move R_RCX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0x1df: movq -0x8(%rbp), %rax *)
| 479 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0x1e3: addq %rcx, %rax *)
| 483 => Some (3, 
    Move (V_TEMP 44 (* #35 *)) (Var R_RAX) $;
    Move (V_TEMP 45 (* #36 *)) (Var R_RCX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 45 (* #36 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 44 (* #35 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 44 (* #35 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 45 (* #36 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 44 (* #35 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 44 (* #35 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 44 (* #35 *)))) (Var (V_TEMP 45 (* #36 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1e6: shll $0x4, %edx *)
| 486 => Some (3, 
    Move (V_TEMP 46 (* #38 *)) (Cast CAST_LOW 32 (Var R_RDX)) $;
    Move R_RDX (Cast CAST_UNSIGNED 64 (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_RDX)) (Word 4 32))) $;
    Move R_CF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 46 (* #38 *))) (Word 28 32))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RDX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RDX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Unknown 1)
  )

(* 0x1e9: movb %dl, (%rax) *)
| 489 => Some (2,
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_LOW 8 (Var R_RDX)) LittleE 1)
  )

(* 0x1eb: movq -0x38(%rbp), %rdx *)
| 491 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0x1ef: movq -0x8(%rbp), %rax *)
| 495 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0x1f3: addq %rdx, %rax *)
| 499 => Some (3, 
    Move (V_TEMP 47 (* #40 *)) (Var R_RAX) $;
    Move (V_TEMP 48 (* #41 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 48 (* #41 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 47 (* #40 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 47 (* #40 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 48 (* #41 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 47 (* #40 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 47 (* #40 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 47 (* #40 *)))) (Var (V_TEMP 48 (* #41 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x1f6: movzbl (%rax), %eax *)
| 502 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x1f9: movl %eax, %esi *)
| 505 => Some (2,
    Move R_RSI (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x1fb: movq -0x48(%rbp), %rax *)
| 507 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x1ff: movq 0x8(%rax), %rdx *)
| 511 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0x203: movq -0x10(%rbp), %rax *)
| 515 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x207: addq %rdx, %rax *)
| 519 => Some (3, 
    Move (V_TEMP 49 (* #43 *)) (Var R_RAX) $;
    Move (V_TEMP 50 (* #44 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 50 (* #44 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 49 (* #43 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 49 (* #43 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 50 (* #44 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 49 (* #43 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 49 (* #43 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 49 (* #43 *)))) (Var (V_TEMP 50 (* #44 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x20a: movzbl (%rax), %eax *)
| 522 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x20d: movzbl %al, %eax *)
| 525 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 8 (Var R_RAX))))
  )

(* 0x210: sarl %eax *)
| 528 => Some (2, 
    Move (V_TEMP 51 (* #46 *)) (Cast CAST_LOW 32 (Var R_RAX)) $;
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_ARSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 1 32))) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_LSHIFT (Var (V_TEMP 51 (* #46 *))) (Word 31 32))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_AF (Unknown 1) $;
    Move R_OF (Word 0 1)
  )

(* 0x212: andl $0x7, %eax *)
| 530 => Some (3, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Cast CAST_LOW 32 (Var R_RAX)) (Word 7 32))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x215: movl %eax, %ecx *)
| 533 => Some (2,
    Move R_RCX (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x217: movq -0x48(%rbp), %rax *)
| 535 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551544 64)) LittleE 8)
  )

(* 0x21b: movq 0x8(%rax), %rdx *)
| 539 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RAX) (Word 8 64)) LittleE 8)
  )

(* 0x21f: movq -0x10(%rbp), %rax *)
| 543 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x223: addq %rdx, %rax *)
| 547 => Some (3, 
    Move (V_TEMP 52 (* #49 *)) (Var R_RAX) $;
    Move (V_TEMP 53 (* #50 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 53 (* #50 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 52 (* #49 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* #49 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 53 (* #50 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* #49 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 52 (* #49 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 52 (* #49 *)))) (Var (V_TEMP 53 (* #50 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x226: movzbl (%rax), %eax *)
| 550 => Some (3,
    Move R_RAX (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 32 (Load (Var V_MEM64) (Var R_RAX) LittleE 1)))
  )

(* 0x229: andl $0xf, %eax *)
| 553 => Some (3, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Cast CAST_LOW 32 (Var R_RAX)) (Word 15 32))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x22c: xorl %ecx, %eax *)
| 556 => Some (2, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_RAX)) (Cast CAST_LOW 32 (Var R_RCX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x22e: orl %eax, %esi *)
| 558 => Some (2, 
    Move R_RSI (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Cast CAST_LOW 32 (Var R_RSI)) (Cast CAST_LOW 32 (Var R_RAX)))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RSI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RSI))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RSI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RSI)))
  )

(* 0x230: movl %esi, %ecx *)
| 560 => Some (2,
    Move R_RCX (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RSI)))
  )

(* 0x232: movq -0x38(%rbp), %rdx *)
| 562 => Some (4,
    Move R_RDX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551560 64)) LittleE 8)
  )

(* 0x236: movq -0x8(%rbp), %rax *)
| 566 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)
  )

(* 0x23a: addq %rdx, %rax *)
| 570 => Some (3, 
    Move (V_TEMP 54 (* #55 *)) (Var R_RAX) $;
    Move (V_TEMP 55 (* #56 *)) (Var R_RDX) $;
    Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 55 (* #56 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Var (V_TEMP 54 (* #55 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 54 (* #55 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 55 (* #56 *))))) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 54 (* #55 *)))) (Cast CAST_HIGH 1 (Var R_RAX))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 54 (* #55 *)))) (Cast CAST_HIGH 1 (Var R_RAX)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 54 (* #55 *)))) (Var (V_TEMP 55 (* #56 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x23d: movl %ecx, %edx *)
| 573 => Some (2,
    Move R_RDX (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RCX)))
  )

(* 0x23f: movb %dl, (%rax) *)
| 575 => Some (2,
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Cast CAST_LOW 8 (Var R_RDX)) LittleE 1)
  )

(* 0x241: movq -0x10(%rbp), %rax *)
| 577 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x245: andl $0x1, %eax *)
| 581 => Some (3, 
    Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Cast CAST_LOW 32 (Var R_RAX)) (Word 1 32))) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_RAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_RAX))) (Let (V_TEMP 7 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* $1 *))) (Word 2 32)) (Var (V_TEMP 8 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* $2 *))) (Word 1 32)) (Var (V_TEMP 7 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_RAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_RAX)))
  )

(* 0x248: testq %rax, %rax *)
| 584 => Some (3, 
    Move (V_TEMP 56 (* #59 *)) (Var R_RAX) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown 1) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 56 (* #59 *))) (Word 4 64)) (Var (V_TEMP 56 (* #59 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 56 (* #59 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 56 (* #59 *))))
  )

(* 0x24b: je 0x5 *)
| 587 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 594 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x24d: addq $0x1, -0x8(%rbp) *)
| 589 => Some (5, 
    Move (V_TEMP 57 (* #64 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) (BinOp OP_PLUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Var (V_TEMP 57 (* #64 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 57 (* #64 *)))) (Word 0 1)) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 57 (* #64 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 57 (* #64 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Var (V_TEMP 57 (* #64 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551608 64)) LittleE 8))
  )

(* 0x252: addq $0x1, -0x10(%rbp) *)
| 594 => Some (5, 
    Move (V_TEMP 58 (* #61 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8) $;
    Move V_MEM64 (Store (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) (BinOp OP_PLUS (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8) (Word 1 64)) LittleE 8) $;
    Move R_CF (BinOp OP_LT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8) (Var (V_TEMP 58 (* #61 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 58 (* #61 *)))) (Word 0 1)) (BinOp OP_AND (BinOp OP_OR (Cast CAST_HIGH 1 (Var (V_TEMP 58 (* #61 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8))) (UnOp OP_NOT (BinOp OP_AND (Cast CAST_HIGH 1 (Var (V_TEMP 58 (* #61 *)))) (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8) (Var (V_TEMP 58 (* #61 *)))) (Word 1 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8) (Word 4 64)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8))
  )

(* 0x257: movq -0x10(%rbp), %rax *)
| 599 => Some (4,
    Move R_RAX (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551600 64)) LittleE 8)
  )

(* 0x25b: cmpq -0x18(%rbp), %rax *)
| 603 => Some (4, 
    Move (V_TEMP 59 (* #18 *)) (BinOp OP_MINUS (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var R_RAX) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)) (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 59 (* #18 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 59 (* #18 *))) (Var R_RAX)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_RBP) (Word 18446744073709551592 64)) LittleE 8)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 59 (* #18 *))) (Word 4 64)) (Var (V_TEMP 59 (* #18 *)))) (Let (V_TEMP 2 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* $1 *))) (Word 2 64)) (Var (V_TEMP 3 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* $2 *))) (Word 1 64)) (Var (V_TEMP 2 (* $2 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 59 (* #18 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 59 (* #18 *))))
  )

(* 0x25f: jb -0xd4 *)
| 607 => Some (6,
    If (Var R_CF) (
      Jmp (Word 401 64)
    ) (* else *) (
      Nop
    )
  )

| _ => None
end.
