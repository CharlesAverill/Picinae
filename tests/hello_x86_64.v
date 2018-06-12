Add LoadPath "..".
Require Import Bap_x86_64.
Import BAP_x86_64.
Require Import NArith.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x4003c8: subq $0x8, %rsp *)
| 4195272%N => Some (4, 
    Move (Va (V_TEMP (0%N) (* v286 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (1%N) (* v287 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (0%N) (* v286 *)) (NumT 64))) (Var (Va (V_TEMP (1%N) (* v287 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (0%N) (* v286 *)) (NumT 64))) (Var (Va (V_TEMP (1%N) (* v287 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (0%N) (* v286 *)) (NumT 64))) (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (0%N) (* v286 *)) (NumT 64)))) (Var (Va (V_TEMP (1%N) (* v287 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (2%N) (* v288 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (2%N) (* v288 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (2%N) (* v288 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (2%N) (* v288 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (2%N) (* v288 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (2%N) (* v288 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x4003cc: movq 0x200c25(%rip), %rax *)
| 4195276%N => Some (7,
    Move (Va (R_RAX) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Word (6295544%N, 64)) LittleE 64)
  )

(* 0x4003d3: testq %rax, %rax *)
| 4195283%N => Some (3, 
    Move (Va (V_TEMP (3%N) (* v292 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (4%N) (* v293 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (3%N) (* v292 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (3%N) (* v292 *)) (NumT 64)))) (Let (Va (V_TEMP (4%N) (* v293 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (4%N) (* v293 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (4%N) (* v293 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (4%N) (* v293 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (4%N) (* v293 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (3%N) (* v292 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (3%N) (* v292 *)) (NumT 64))))
  )

(* 0x4003d6: je 0x5 *)
| 4195286%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (4195293%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x4003d8: callq 0x43 *)
| 4195288%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195293%N, 64)) LittleE 64) $;
    Jmp (Word (4195360%N, 64))
  )

(* 0x4003dd: addq $0x8, %rsp *)
| 4195293%N => Some (4, 
    Move (Va (V_TEMP (5%N) (* v302 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (6%N) (* v303 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (6%N) (* v303 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (5%N) (* v302 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (5%N) (* v302 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (6%N) (* v303 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (5%N) (* v302 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (5%N) (* v302 *)) (NumT 64)))) (Var (Va (V_TEMP (6%N) (* v303 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (7%N) (* v304 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (7%N) (* v304 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (7%N) (* v304 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (7%N) (* v304 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (7%N) (* v304 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (7%N) (* v304 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x4003e1: retq *)
| 4195297%N => Some (1, 
    Move (Va (V_TEMP (8%N) (* v308 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (8%N) (* v308 *)) (NumT 64)))
  )

(* 0x400400: jmpq *0x200c12(%rip) *)
| 4195328%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word (6295576%N, 64)) LittleE 64)
  )

(* 0x400410: jmpq *0x200c0a(%rip) *)
| 4195344%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word (6295584%N, 64)) LittleE 64)
  )

(* 0x400420: jmpq *0x200bd2(%rip) *)
| 4195360%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word (6295544%N, 64)) LittleE 64)
  )

(* 0x400430: subq $0x8, %rsp *)
| 4195376%N => Some (4, 
    Move (Va (V_TEMP (9%N) (* v258 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (10%N) (* v259 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (9%N) (* v258 *)) (NumT 64))) (Var (Va (V_TEMP (10%N) (* v259 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (9%N) (* v258 *)) (NumT 64))) (Var (Va (V_TEMP (10%N) (* v259 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (9%N) (* v258 *)) (NumT 64))) (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (9%N) (* v258 *)) (NumT 64)))) (Var (Va (V_TEMP (10%N) (* v259 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (11%N) (* v260 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (11%N) (* v260 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (11%N) (* v260 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (11%N) (* v260 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (11%N) (* v260 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (11%N) (* v260 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x400434: movl $0x4005d4, %edi *)
| 4195380%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word (4195796%N, 64))
  )

(* 0x400439: callq -0x3e *)
| 4195385%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195390%N, 64)) LittleE 64) $;
    Jmp (Word (4195328%N, 64))
  )

(* 0x40043e: xorl %eax, %eax *)
| 4195390%N => Some (2, 
    Move (Va (R_RAX) (NumT 64)) (Word (0%N, 64)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_PF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_SF) (NumT 1)) (Word (0%N, 1))
  )

(* 0x400440: addq $0x8, %rsp *)
| 4195392%N => Some (4, 
    Move (Va (V_TEMP (12%N) (* v264 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (13%N) (* v265 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (13%N) (* v265 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (12%N) (* v264 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (12%N) (* v264 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (13%N) (* v265 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (12%N) (* v264 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (12%N) (* v264 *)) (NumT 64)))) (Var (Va (V_TEMP (13%N) (* v265 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (14%N) (* v266 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (14%N) (* v266 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (14%N) (* v266 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (14%N) (* v266 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (14%N) (* v266 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (14%N) (* v266 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x400444: retq *)
| 4195396%N => Some (1, 
    Move (Va (V_TEMP (15%N) (* v270 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (15%N) (* v270 *)) (NumT 64)))
  )

(* 0x400450: xorl %ebp, %ebp *)
| 4195408%N => Some (2, 
    Move (Va (R_RBP) (NumT 64)) (Word (0%N, 64)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_PF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_SF) (NumT 1)) (Word (0%N, 1))
  )

(* 0x400452: movq %rdx, %r9 *)
| 4195410%N => Some (3,
    Move (Va (R_R9) (NumT 64)) (Var (Va (R_RDX) (NumT 64)))
  )

(* 0x400455: popq %rsi *)
| 4195413%N => Some (1, 
    Move (Va (R_RSI) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x400456: movq %rsp, %rdx *)
| 4195414%N => Some (3,
    Move (Va (R_RDX) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x400459: andq $-0x10, %rsp *)
| 4195417%N => Some (4, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_AND (Var (Va (R_RSP) (NumT 64))) (Word (18446744073709551600%N, 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (16%N) (* v328 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (16%N) (* v328 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (16%N) (* v328 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (16%N) (* v328 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (16%N) (* v328 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (16%N) (* v328 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x40045d: pushq %rax *)
| 4195421%N => Some (1, 
    Move (Va (V_TEMP (17%N) (* v330 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (17%N) (* v330 *)) (NumT 64))) LittleE 64)
  )

(* 0x40045e: pushq %rsp *)
| 4195422%N => Some (1, 
    Move (Va (V_TEMP (18%N) (* v332 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (18%N) (* v332 *)) (NumT 64))) LittleE 64)
  )

(* 0x40045f: movq $0x4005c0, %r8 *)
| 4195423%N => Some (7,
    Move (Va (R_R8) (NumT 64)) (Word (4195776%N, 64))
  )

(* 0x400466: movq $0x400550, %rcx *)
| 4195430%N => Some (7,
    Move (Va (R_RCX) (NumT 64)) (Word (4195664%N, 64))
  )

(* 0x40046d: movq $0x400430, %rdi *)
| 4195437%N => Some (7,
    Move (Va (R_RDI) (NumT 64)) (Word (4195376%N, 64))
  )

(* 0x400474: callq -0x69 *)
| 4195444%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195449%N, 64)) LittleE 64) $;
    Jmp (Word (4195344%N, 64))
  )

(* 0x400479: hlt *)
| 4195449%N => Some (1,
    Nop
  )

(* 0x40047a: nopw (%rax,%rax) *)
| 4195450%N => Some (6,
    Nop
  )

(* 0x400480: movl $0x60103f, %eax *)
| 4195456%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word (6295615%N, 64))
  )

(* 0x400485: pushq %rbp *)
| 4195461%N => Some (1, 
    Move (Va (V_TEMP (19%N) (* v310 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (19%N) (* v310 *)) (NumT 64))) LittleE 64)
  )

(* 0x400486: subq $0x601038, %rax *)
| 4195462%N => Some (6, 
    Move (Va (V_TEMP (20%N) (* v312 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (V_TEMP (21%N) (* v313 *)) (NumT 64)) (Word (6295608%N, 64)) $;
    Move (Va (R_RAX) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RAX) (NumT 64))) (Word (6295608%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (20%N) (* v312 *)) (NumT 64))) (Var (Va (V_TEMP (21%N) (* v313 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (20%N) (* v312 *)) (NumT 64))) (Var (Va (V_TEMP (21%N) (* v313 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (20%N) (* v312 *)) (NumT 64))) (Var (Va (R_RAX) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Var (Va (V_TEMP (20%N) (* v312 *)) (NumT 64)))) (Var (Va (V_TEMP (21%N) (* v313 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (22%N) (* v314 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RAX) (NumT 64)))) (Let (Va (V_TEMP (22%N) (* v314 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (22%N) (* v314 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (22%N) (* v314 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (22%N) (* v314 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (22%N) (* v314 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RAX) (NumT 64))))
  )

(* 0x40048c: cmpq $0xe, %rax *)
| 4195468%N => Some (4, 
    Move (Va (V_TEMP (23%N) (* v318 *)) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RAX) (NumT 64))) (Word (14%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RAX) (NumT 64))) (Word (14%N, 64))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Word (14%N, 64))) (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64))) (Var (Va (R_RAX) (NumT 64)))) (Word (14%N, 64))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (24%N) (* v319 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64)))) (Let (Va (V_TEMP (24%N) (* v319 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (24%N) (* v319 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (24%N) (* v319 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (24%N) (* v319 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (24%N) (* v319 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (23%N) (* v318 *)) (NumT 64))))
  )

(* 0x400490: movq %rsp, %rbp *)
| 4195472%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x400493: jbe 0x1b *)
| 4195475%N => Some (2,
    If (BinOp OP_OR (Var (Va (R_CF) (NumT 1))) (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word (4195504%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x400495: movl $0x0, %eax *)
| 4195477%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word (0%N, 64))
  )

(* 0x40049a: testq %rax, %rax *)
| 4195482%N => Some (3, 
    Move (Va (V_TEMP (25%N) (* v346 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (26%N) (* v347 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (25%N) (* v346 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (25%N) (* v346 *)) (NumT 64)))) (Let (Va (V_TEMP (26%N) (* v347 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (26%N) (* v347 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (26%N) (* v347 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (26%N) (* v347 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (26%N) (* v347 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (25%N) (* v346 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (25%N) (* v346 *)) (NumT 64))))
  )

(* 0x40049d: je 0x11 *)
| 4195485%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (4195504%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x40049f: popq %rbp *)
| 4195487%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4004a0: movl $0x601038, %edi *)
| 4195488%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word (6295608%N, 64))
  )

(* 0x4004a5: jmpq *%rax *)
| 4195493%N => Some (2,
    Jmp (Var (Va (R_RAX) (NumT 64)))
  )

(* 0x4004b0: popq %rbp *)
| 4195504%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4004b1: retq *)
| 4195505%N => Some (1, 
    Move (Va (V_TEMP (27%N) (* v322 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (27%N) (* v322 *)) (NumT 64)))
  )

(* 0x4004c0: movl $0x601038, %esi *)
| 4195520%N => Some (5,
    Move (Va (R_RSI) (NumT 64)) (Word (6295608%N, 64))
  )

(* 0x4004c5: pushq %rbp *)
| 4195525%N => Some (1, 
    Move (Va (V_TEMP (28%N) (* v204 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (28%N) (* v204 *)) (NumT 64))) LittleE 64)
  )

(* 0x4004c6: subq $0x601038, %rsi *)
| 4195526%N => Some (7, 
    Move (Va (V_TEMP (29%N) (* v206 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (V_TEMP (30%N) (* v207 *)) (NumT 64)) (Word (6295608%N, 64)) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSI) (NumT 64))) (Word (6295608%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (29%N) (* v206 *)) (NumT 64))) (Var (Va (V_TEMP (30%N) (* v207 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (29%N) (* v206 *)) (NumT 64))) (Var (Va (V_TEMP (30%N) (* v207 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (29%N) (* v206 *)) (NumT 64))) (Var (Va (R_RSI) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (29%N) (* v206 *)) (NumT 64)))) (Var (Va (V_TEMP (30%N) (* v207 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (31%N) (* v208 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (31%N) (* v208 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (31%N) (* v208 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (31%N) (* v208 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (31%N) (* v208 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (31%N) (* v208 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSI) (NumT 64))))
  )

(* 0x4004cd: sarq $0x3, %rsi *)
| 4195533%N => Some (4, 
    Move (Va (V_TEMP (32%N) (* tmp212 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (3%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (32%N) (* tmp212 *)) (NumT 64))) (Word (64%N, 64))) (BinOp OP_AND (Word (3%N, 64)) (BinOp OP_MINUS (Word (64%N, 64)) (Word (1%N, 64)))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (33%N) (* v213 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (33%N) (* v213 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (33%N) (* v213 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (33%N) (* v213 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (33%N) (* v213 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (33%N) (* v213 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x4004d1: movq %rsp, %rbp *)
| 4195537%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x4004d4: movq %rsi, %rax *)
| 4195540%N => Some (3,
    Move (Va (R_RAX) (NumT 64)) (Var (Va (R_RSI) (NumT 64)))
  )

(* 0x4004d7: shrq $0x3f, %rax *)
| 4195543%N => Some (4, 
    Move (Va (V_TEMP (34%N) (* tmp216 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RAX) (NumT 64)) (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word (63%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (34%N) (* tmp216 *)) (NumT 64))) (Word (64%N, 64))) (BinOp OP_AND (Word (63%N, 64)) (BinOp OP_MINUS (Word (64%N, 64)) (Word (1%N, 64)))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (35%N) (* v217 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RAX) (NumT 64)))) (Let (Va (V_TEMP (35%N) (* v217 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (35%N) (* v217 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (35%N) (* v217 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (35%N) (* v217 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (35%N) (* v217 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x4004db: addq %rax, %rsi *)
| 4195547%N => Some (3, 
    Move (Va (V_TEMP (36%N) (* v220 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (V_TEMP (37%N) (* v221 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (37%N) (* v221 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (36%N) (* v220 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (36%N) (* v220 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (37%N) (* v221 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (36%N) (* v220 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (36%N) (* v220 *)) (NumT 64)))) (Var (Va (V_TEMP (37%N) (* v221 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (38%N) (* v222 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (38%N) (* v222 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (38%N) (* v222 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (38%N) (* v222 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (38%N) (* v222 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (38%N) (* v222 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSI) (NumT 64))))
  )

(* 0x4004de: sarq %rsi *)
| 4195550%N => Some (3, 
    Move (Va (V_TEMP (39%N) (* tmp226 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (1%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (39%N) (* tmp226 *)) (NumT 64))) (Word (64%N, 64))) (BinOp OP_AND (Word (1%N, 64)) (BinOp OP_MINUS (Word (64%N, 64)) (Word (1%N, 64)))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (40%N) (* v227 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (40%N) (* v227 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (40%N) (* v227 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (40%N) (* v227 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (40%N) (* v227 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (40%N) (* v227 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1))
  )

(* 0x4004e1: je 0x15 *)
| 4195553%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (4195576%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x4004e3: movl $0x0, %eax *)
| 4195555%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word (0%N, 64))
  )

(* 0x4004e8: testq %rax, %rax *)
| 4195560%N => Some (3, 
    Move (Va (V_TEMP (41%N) (* v298 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (42%N) (* v299 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (41%N) (* v298 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (41%N) (* v298 *)) (NumT 64)))) (Let (Va (V_TEMP (42%N) (* v299 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (42%N) (* v299 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (42%N) (* v299 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (42%N) (* v299 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (42%N) (* v299 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (41%N) (* v298 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (41%N) (* v298 *)) (NumT 64))))
  )

(* 0x4004eb: je 0xb *)
| 4195563%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (4195576%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x4004ed: popq %rbp *)
| 4195565%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4004ee: movl $0x601038, %edi *)
| 4195566%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word (6295608%N, 64))
  )

(* 0x4004f3: jmpq *%rax *)
| 4195571%N => Some (2,
    Jmp (Var (Va (R_RAX) (NumT 64)))
  )

(* 0x4004f8: popq %rbp *)
| 4195576%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4004f9: retq *)
| 4195577%N => Some (1, 
    Move (Va (V_TEMP (43%N) (* v334 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (43%N) (* v334 *)) (NumT 64)))
  )

(* 0x40053a: pushq %rbp *)
| 4195642%N => Some (1, 
    Move (Va (V_TEMP (44%N) (* v272 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (44%N) (* v272 *)) (NumT 64))) LittleE 64)
  )

(* 0x40053b: movq %rsp, %rbp *)
| 4195643%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x40053e: callq *%rax *)
| 4195646%N => Some (2, 
    Move (Va (V_TEMP (45%N) (* v274 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195648%N, 64)) LittleE 64) $;
    Jmp (Var (Va (V_TEMP (45%N) (* v274 *)) (NumT 64)))
  )

(* 0x400540: popq %rbp *)
| 4195648%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x400541: jmp -0x86 *)
| 4195649%N => Some (5,
    Jmp (Word (4195520%N, 64))
  )

(* 0x400550: pushq %r15 *)
| 4195664%N => Some (2, 
    Move (Va (V_TEMP (46%N) (* v230 *)) (NumT 64)) (Var (Va (R_R15) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (46%N) (* v230 *)) (NumT 64))) LittleE 64)
  )

(* 0x400552: pushq %r14 *)
| 4195666%N => Some (2, 
    Move (Va (V_TEMP (47%N) (* v232 *)) (NumT 64)) (Var (Va (R_R14) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (47%N) (* v232 *)) (NumT 64))) LittleE 64)
  )

(* 0x400554: movl %edi, %r15d *)
| 4195668%N => Some (3,
    Move (Va (R_R15) (NumT 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var (Va (R_RDI) (NumT 64)))))
  )

(* 0x400557: pushq %r13 *)
| 4195671%N => Some (2, 
    Move (Va (V_TEMP (48%N) (* v234 *)) (NumT 64)) (Var (Va (R_R13) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (48%N) (* v234 *)) (NumT 64))) LittleE 64)
  )

(* 0x400559: pushq %r12 *)
| 4195673%N => Some (2, 
    Move (Va (V_TEMP (49%N) (* v236 *)) (NumT 64)) (Var (Va (R_R12) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (49%N) (* v236 *)) (NumT 64))) LittleE 64)
  )

(* 0x40055b: leaq 0x2008ae(%rip), %r12 *)
| 4195675%N => Some (7,
    Move (Va (R_R12) (NumT 64)) (Word (6295056%N, 64))
  )

(* 0x400562: pushq %rbp *)
| 4195682%N => Some (1, 
    Move (Va (V_TEMP (50%N) (* v238 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (50%N) (* v238 *)) (NumT 64))) LittleE 64)
  )

(* 0x400563: leaq 0x2008ae(%rip), %rbp *)
| 4195683%N => Some (7,
    Move (Va (R_RBP) (NumT 64)) (Word (6295064%N, 64))
  )

(* 0x40056a: pushq %rbx *)
| 4195690%N => Some (1, 
    Move (Va (V_TEMP (51%N) (* v240 *)) (NumT 64)) (Var (Va (R_RBX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (51%N) (* v240 *)) (NumT 64))) LittleE 64)
  )

(* 0x40056b: movq %rsi, %r14 *)
| 4195691%N => Some (3,
    Move (Va (R_R14) (NumT 64)) (Var (Va (R_RSI) (NumT 64)))
  )

(* 0x40056e: movq %rdx, %r13 *)
| 4195694%N => Some (3,
    Move (Va (R_R13) (NumT 64)) (Var (Va (R_RDX) (NumT 64)))
  )

(* 0x400571: subq %r12, %rbp *)
| 4195697%N => Some (3, 
    Move (Va (V_TEMP (52%N) (* v242 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (V_TEMP (53%N) (* v243 *)) (NumT 64)) (Var (Va (R_R12) (NumT 64))) $;
    Move (Va (R_RBP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RBP) (NumT 64))) (Var (Va (R_R12) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (52%N) (* v242 *)) (NumT 64))) (Var (Va (V_TEMP (53%N) (* v243 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (52%N) (* v242 *)) (NumT 64))) (Var (Va (V_TEMP (53%N) (* v243 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (52%N) (* v242 *)) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RBP) (NumT 64))) (Var (Va (V_TEMP (52%N) (* v242 *)) (NumT 64)))) (Var (Va (V_TEMP (53%N) (* v243 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (54%N) (* v244 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RBP) (NumT 64)))) (Let (Va (V_TEMP (54%N) (* v244 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (54%N) (* v244 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (54%N) (* v244 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (54%N) (* v244 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (54%N) (* v244 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RBP) (NumT 64))))
  )

(* 0x400574: subq $0x8, %rsp *)
| 4195700%N => Some (4, 
    Move (Va (V_TEMP (55%N) (* v248 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (56%N) (* v249 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (55%N) (* v248 *)) (NumT 64))) (Var (Va (V_TEMP (56%N) (* v249 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (55%N) (* v248 *)) (NumT 64))) (Var (Va (V_TEMP (56%N) (* v249 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (55%N) (* v248 *)) (NumT 64))) (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (55%N) (* v248 *)) (NumT 64)))) (Var (Va (V_TEMP (56%N) (* v249 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (57%N) (* v250 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (57%N) (* v250 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (57%N) (* v250 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (57%N) (* v250 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (57%N) (* v250 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (57%N) (* v250 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x400578: sarq $0x3, %rbp *)
| 4195704%N => Some (4, 
    Move (Va (V_TEMP (58%N) (* tmp254 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RBP) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RBP) (NumT 64))) (Word (3%N, 64))) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (58%N) (* tmp254 *)) (NumT 64))) (Word (64%N, 64))) (BinOp OP_AND (Word (3%N, 64)) (BinOp OP_MINUS (Word (64%N, 64)) (Word (1%N, 64)))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (59%N) (* v255 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RBP) (NumT 64)))) (Let (Va (V_TEMP (59%N) (* v255 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59%N) (* v255 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (59%N) (* v255 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (59%N) (* v255 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (59%N) (* v255 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x40057c: callq -0x1b9 *)
| 4195708%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195713%N, 64)) LittleE 64) $;
    Jmp (Word (4195272%N, 64))
  )

(* 0x400581: testq %rbp, %rbp *)
| 4195713%N => Some (3, 
    Move (Va (V_TEMP (60%N) (* v324 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (61%N) (* v325 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (60%N) (* v324 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (60%N) (* v324 *)) (NumT 64)))) (Let (Va (V_TEMP (61%N) (* v325 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (61%N) (* v325 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (61%N) (* v325 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (61%N) (* v325 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (61%N) (* v325 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (60%N) (* v324 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (60%N) (* v324 *)) (NumT 64))))
  )

(* 0x400584: je 0x20 *)
| 4195716%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word (4195750%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x400586: xorl %ebx, %ebx *)
| 4195718%N => Some (2, 
    Move (Va (R_RBX) (NumT 64)) (Word (0%N, 64)) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_PF) (NumT 1)) (Word (1%N, 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_CF) (NumT 1)) (Word (0%N, 1)) $;
    Move (Va (R_SF) (NumT 1)) (Word (0%N, 1))
  )

(* 0x400588: nopl (%rax,%rax) *)
| 4195720%N => Some (8,
    Nop
  )

(* 0x400590: movq %r13, %rdx *)
| 4195728%N => Some (3,
    Move (Va (R_RDX) (NumT 64)) (Var (Va (R_R13) (NumT 64)))
  )

(* 0x400593: movq %r14, %rsi *)
| 4195731%N => Some (3,
    Move (Va (R_RSI) (NumT 64)) (Var (Va (R_R14) (NumT 64)))
  )

(* 0x400596: movl %r15d, %edi *)
| 4195734%N => Some (3,
    Move (Va (R_RDI) (NumT 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var (Va (R_R15) (NumT 64)))))
  )

(* 0x400599: callq *(%r12,%rbx,8) *)
| 4195737%N => Some (4, 
    Move (Va (V_TEMP (62%N) (* v284 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (BinOp OP_PLUS (Var (Va (R_R12) (NumT 64))) (BinOp OP_LSHIFT (Var (Va (R_RBX) (NumT 64))) (Word (3%N, 64)))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word (4195741%N, 64)) LittleE 64) $;
    Jmp (Var (Va (V_TEMP (62%N) (* v284 *)) (NumT 64)))
  )

(* 0x40059d: addq $0x1, %rbx *)
| 4195741%N => Some (4, 
    Move (Va (V_TEMP (63%N) (* v336 *)) (NumT 64)) (Var (Va (R_RBX) (NumT 64))) $;
    Move (Va (V_TEMP (64%N) (* v337 *)) (NumT 64)) (Word (1%N, 64)) $;
    Move (Va (R_RBX) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (64%N) (* v337 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (63%N) (* v336 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (63%N) (* v336 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (64%N) (* v337 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (63%N) (* v336 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RBX) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (63%N) (* v336 *)) (NumT 64)))) (Var (Va (V_TEMP (64%N) (* v337 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (65%N) (* v338 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBX) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RBX) (NumT 64)))) (Let (Va (V_TEMP (65%N) (* v338 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (65%N) (* v338 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (65%N) (* v338 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (65%N) (* v338 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (65%N) (* v338 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RBX) (NumT 64))))
  )

(* 0x4005a1: cmpq %rbp, %rbx *)
| 4195745%N => Some (3, 
    Move (Va (V_TEMP (66%N) (* v342 *)) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64))) (Var (Va (R_RBX) (NumT 64)))) (Var (Va (R_RBP) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (67%N) (* v343 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64))) (Word (4%N, 64))) (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64)))) (Let (Va (V_TEMP (67%N) (* v343 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (67%N) (* v343 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (67%N) (* v343 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (67%N) (* v343 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (67%N) (* v343 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (V_TEMP (66%N) (* v342 *)) (NumT 64))))
  )

(* 0x4005a4: jne -0x16 *)
| 4195748%N => Some (2,
    If (UnOp OP_NOT (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word (4195728%N, 64))
    ) (* else *) (
      Nop
    )
  )

(* 0x4005a6: addq $0x8, %rsp *)
| 4195750%N => Some (4, 
    Move (Va (V_TEMP (68%N) (* v276 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (69%N) (* v277 *)) (NumT 64)) (Word (8%N, 64)) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (69%N) (* v277 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (68%N) (* v276 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (68%N) (* v276 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (69%N) (* v277 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (68%N) (* v276 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word (16%N, 64)) (BinOp OP_AND (Word (16%N, 64)) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (68%N) (* v276 *)) (NumT 64)))) (Var (Va (V_TEMP (69%N) (* v277 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (70%N) (* v278 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word (4%N, 64))) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (70%N) (* v278 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (70%N) (* v278 *)) (NumT 64))) (Word (2%N, 64))) (Var (Va (V_TEMP (70%N) (* v278 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (70%N) (* v278 *)) (NumT 64))) (Word (1%N, 64))) (Var (Va (V_TEMP (70%N) (* v278 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word (0%N, 64)) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x4005aa: popq %rbx *)
| 4195754%N => Some (1, 
    Move (Va (R_RBX) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005ab: popq %rbp *)
| 4195755%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005ac: popq %r12 *)
| 4195756%N => Some (2, 
    Move (Va (R_R12) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005ae: popq %r13 *)
| 4195758%N => Some (2, 
    Move (Va (R_R13) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005b0: popq %r14 *)
| 4195760%N => Some (2, 
    Move (Va (R_R14) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005b2: popq %r15 *)
| 4195762%N => Some (2, 
    Move (Va (R_R15) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64)))
  )

(* 0x4005b4: retq *)
| 4195764%N => Some (1, 
    Move (Va (V_TEMP (71%N) (* v282 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (71%N) (* v282 *)) (NumT 64)))
  )

(* 0x4005c0: retq *)
| 4195776%N => Some (2, 
    Move (Va (V_TEMP (72%N) (* v296 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word (8%N, 64))) $;
    Jmp (Var (Va (V_TEMP (72%N) (* v296 *)) (NumT 64)))
  )

| _ => None
end.
