Add LoadPath "..".
Require Import Bap_x86_64.
Import BAP_x86_64.
Require Import NArith.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x4003c8: subq $0x8, %rsp *)
| 4195272%N => Some (4, 
    Move (Va (V_TEMP (0%N) (* v211 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (1%N) (* v212 *)) (NumT 64)) (Word 8%N 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (0%N) (* v211 *)) (NumT 64))) (Var (Va (V_TEMP (1%N) (* v212 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (0%N) (* v211 *)) (NumT 64))) (Var (Va (V_TEMP (1%N) (* v212 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (0%N) (* v211 *)) (NumT 64))) (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (0%N) (* v211 *)) (NumT 64)))) (Var (Va (V_TEMP (1%N) (* v212 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (2%N) (* v213 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (2%N) (* v213 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (2%N) (* v213 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (2%N) (* v213 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (2%N) (* v213 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (2%N) (* v213 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x4003cc: movq 0x200c25(%rip), %rax *)
| 4195276%N => Some (7,
    Move (Va (R_RAX) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Word 6295544%N 64) LittleE 8)
  )

(* 0x4003d3: testq %rax, %rax *)
| 4195283%N => Some (3, 
    Move (Va (V_TEMP (3%N) (* v217 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (4%N) (* v218 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (3%N) (* v217 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (3%N) (* v217 *)) (NumT 64)))) (Let (Va (V_TEMP (4%N) (* v218 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (4%N) (* v218 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (4%N) (* v218 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (4%N) (* v218 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (4%N) (* v218 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (3%N) (* v217 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (3%N) (* v217 *)) (NumT 64))))
  )

(* 0x4003d6: je 0x5 *)
| 4195286%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word 4195293%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4003d8: callq 0x43 *)
| 4195288%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195293%N 64) LittleE 8) $;
    Jmp (Word 4195360%N 64)
  )

(* 0x4003dd: addq $0x8, %rsp *)
| 4195293%N => Some (4, 
    Move (Va (V_TEMP (5%N) (* v251 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (6%N) (* v252 *)) (NumT 64)) (Word 8%N 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (6%N) (* v252 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (5%N) (* v251 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (5%N) (* v251 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (6%N) (* v252 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (5%N) (* v251 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (5%N) (* v251 *)) (NumT 64)))) (Var (Va (V_TEMP (6%N) (* v252 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (7%N) (* v253 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (7%N) (* v253 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (7%N) (* v253 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (7%N) (* v253 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (7%N) (* v253 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (7%N) (* v253 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x4003e1: retq *)
| 4195297%N => Some (1, 
    Move (Va (V_TEMP (8%N) (* v257 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (8%N) (* v257 *)) (NumT 64)))
  )

(* 0x400400: jmpq *0x200c12(%rip) *)
| 4195328%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word 6295576%N 64) LittleE 8)
  )

(* 0x400410: jmpq *0x200c0a(%rip) *)
| 4195344%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word 6295584%N 64) LittleE 8)
  )

(* 0x400420: jmpq *0x200bd2(%rip) *)
| 4195360%N => Some (6,
    Jmp (Load (Var (Va (V_MEM64) (MemT 64))) (Word 6295544%N 64) LittleE 8)
  )

(* 0x400430: xorl %ebp, %ebp *)
| 4195376%N => Some (2, 
    Move (Va (R_RBP) (NumT 64)) (Word 0%N 64) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word 1%N 1) $;
    Move (Va (R_PF) (NumT 1)) (Word 1%N 1) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_SF) (NumT 1)) (Word 0%N 1)
  )

(* 0x400432: movq %rdx, %r9 *)
| 4195378%N => Some (3,
    Move (Va (R_R9) (NumT 64)) (Var (Va (R_RDX) (NumT 64)))
  )

(* 0x400435: popq %rsi *)
| 4195381%N => Some (1, 
    Move (Va (R_RSI) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x400436: movq %rsp, %rdx *)
| 4195382%N => Some (3,
    Move (Va (R_RDX) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x400439: andq $-0x10, %rsp *)
| 4195385%N => Some (4, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_AND (Var (Va (R_RSP) (NumT 64))) (Word 18446744073709551600%N 64)) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (9%N) (* v191 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (9%N) (* v191 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (9%N) (* v191 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (9%N) (* v191 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (9%N) (* v191 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (9%N) (* v191 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x40043d: pushq %rax *)
| 4195389%N => Some (1, 
    Move (Va (V_TEMP (10%N) (* v193 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (10%N) (* v193 *)) (NumT 64))) LittleE 8)
  )

(* 0x40043e: pushq %rsp *)
| 4195390%N => Some (1, 
    Move (Va (V_TEMP (11%N) (* v195 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (11%N) (* v195 *)) (NumT 64))) LittleE 8)
  )

(* 0x40043f: movq $0x4005b0, %r8 *)
| 4195391%N => Some (7,
    Move (Va (R_R8) (NumT 64)) (Word 4195760%N 64)
  )

(* 0x400446: movq $0x400540, %rcx *)
| 4195398%N => Some (7,
    Move (Va (R_RCX) (NumT 64)) (Word 4195648%N 64)
  )

(* 0x40044d: movq $0x400526, %rdi *)
| 4195405%N => Some (7,
    Move (Va (R_RDI) (NumT 64)) (Word 4195622%N 64)
  )

(* 0x400454: callq -0x49 *)
| 4195412%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195417%N 64) LittleE 8) $;
    Jmp (Word 4195344%N 64)
  )

(* 0x400459: hlt *)
| 4195417%N => Some (1,
    Nop
  )

(* 0x40045a: nopw (%rax,%rax) *)
| 4195418%N => Some (6,
    Nop
  )

(* 0x400460: movl $0x60103f, %eax *)
| 4195424%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word 6295615%N 64)
  )

(* 0x400465: pushq %rbp *)
| 4195429%N => Some (1, 
    Move (Va (V_TEMP (12%N) (* v313 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (12%N) (* v313 *)) (NumT 64))) LittleE 8)
  )

(* 0x400466: subq $0x601038, %rax *)
| 4195430%N => Some (6, 
    Move (Va (V_TEMP (13%N) (* v315 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (V_TEMP (14%N) (* v316 *)) (NumT 64)) (Word 6295608%N 64) $;
    Move (Va (R_RAX) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RAX) (NumT 64))) (Word 6295608%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (13%N) (* v315 *)) (NumT 64))) (Var (Va (V_TEMP (14%N) (* v316 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (13%N) (* v315 *)) (NumT 64))) (Var (Va (V_TEMP (14%N) (* v316 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (13%N) (* v315 *)) (NumT 64))) (Var (Va (R_RAX) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Var (Va (V_TEMP (13%N) (* v315 *)) (NumT 64)))) (Var (Va (V_TEMP (14%N) (* v316 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (15%N) (* v317 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RAX) (NumT 64)))) (Let (Va (V_TEMP (15%N) (* v317 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (15%N) (* v317 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (15%N) (* v317 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (15%N) (* v317 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (15%N) (* v317 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RAX) (NumT 64))))
  )

(* 0x40046c: cmpq $0xe, %rax *)
| 4195436%N => Some (4, 
    Move (Va (V_TEMP (16%N) (* v321 *)) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RAX) (NumT 64))) (Word 14%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RAX) (NumT 64))) (Word 14%N 64)) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Word 14%N 64)) (BinOp OP_XOR (Var (Va (R_RAX) (NumT 64))) (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64))) (Var (Va (R_RAX) (NumT 64)))) (Word 14%N 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (17%N) (* v322 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64)))) (Let (Va (V_TEMP (17%N) (* v322 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (17%N) (* v322 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (17%N) (* v322 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (17%N) (* v322 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (17%N) (* v322 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (16%N) (* v321 *)) (NumT 64))))
  )

(* 0x400470: movq %rsp, %rbp *)
| 4195440%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x400473: jbe 0x1b *)
| 4195443%N => Some (2,
    If (BinOp OP_OR (Var (Va (R_CF) (NumT 1))) (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word 4195472%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400475: movl $0x0, %eax *)
| 4195445%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word 0%N 64)
  )

(* 0x40047a: testq %rax, %rax *)
| 4195450%N => Some (3, 
    Move (Va (V_TEMP (18%N) (* v207 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (19%N) (* v208 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (18%N) (* v207 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (18%N) (* v207 *)) (NumT 64)))) (Let (Va (V_TEMP (19%N) (* v208 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (19%N) (* v208 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (19%N) (* v208 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (19%N) (* v208 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (19%N) (* v208 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (18%N) (* v207 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (18%N) (* v207 *)) (NumT 64))))
  )

(* 0x40047d: je 0x11 *)
| 4195453%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word 4195472%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x40047f: popq %rbp *)
| 4195455%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x400480: movl $0x601038, %edi *)
| 4195456%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word 6295608%N 64)
  )

(* 0x400485: jmpq *%rax *)
| 4195461%N => Some (2,
    Jmp (Var (Va (R_RAX) (NumT 64)))
  )

(* 0x400490: popq %rbp *)
| 4195472%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x400491: retq *)
| 4195473%N => Some (1, 
    Move (Va (V_TEMP (20%N) (* v189 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (20%N) (* v189 *)) (NumT 64)))
  )

(* 0x4004a0: movl $0x601038, %esi *)
| 4195488%N => Some (5,
    Move (Va (R_RSI) (NumT 64)) (Word 6295608%N 64)
  )

(* 0x4004a5: pushq %rbp *)
| 4195493%N => Some (1, 
    Move (Va (V_TEMP (21%N) (* v221 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (21%N) (* v221 *)) (NumT 64))) LittleE 8)
  )

(* 0x4004a6: subq $0x601038, %rsi *)
| 4195494%N => Some (7, 
    Move (Va (V_TEMP (22%N) (* v223 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (V_TEMP (23%N) (* v224 *)) (NumT 64)) (Word 6295608%N 64) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSI) (NumT 64))) (Word 6295608%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (22%N) (* v223 *)) (NumT 64))) (Var (Va (V_TEMP (23%N) (* v224 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (22%N) (* v223 *)) (NumT 64))) (Var (Va (V_TEMP (23%N) (* v224 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (22%N) (* v223 *)) (NumT 64))) (Var (Va (R_RSI) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (22%N) (* v223 *)) (NumT 64)))) (Var (Va (V_TEMP (23%N) (* v224 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (24%N) (* v225 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (24%N) (* v225 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (24%N) (* v225 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (24%N) (* v225 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (24%N) (* v225 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (24%N) (* v225 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSI) (NumT 64))))
  )

(* 0x4004ad: sarq $0x3, %rsi *)
| 4195501%N => Some (4, 
    Move (Va (V_TEMP (25%N) (* tmp229 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 3%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (25%N) (* tmp229 *)) (NumT 64))) (Word 64%N 64)) (BinOp OP_AND (Word 3%N 64) (BinOp OP_MINUS (Word 64%N 64) (Word 1%N 64))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (26%N) (* v230 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (26%N) (* v230 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (26%N) (* v230 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (26%N) (* v230 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (26%N) (* v230 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (26%N) (* v230 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x4004b1: movq %rsp, %rbp *)
| 4195505%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x4004b4: movq %rsi, %rax *)
| 4195508%N => Some (3,
    Move (Va (R_RAX) (NumT 64)) (Var (Va (R_RSI) (NumT 64)))
  )

(* 0x4004b7: shrq $0x3f, %rax *)
| 4195511%N => Some (4, 
    Move (Va (V_TEMP (27%N) (* tmp233 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RAX) (NumT 64)) (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word 63%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (27%N) (* tmp233 *)) (NumT 64))) (Word 64%N 64)) (BinOp OP_AND (Word 63%N 64) (BinOp OP_MINUS (Word 64%N 64) (Word 1%N 64))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RAX) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (28%N) (* v234 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RAX) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RAX) (NumT 64)))) (Let (Va (V_TEMP (28%N) (* v234 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (28%N) (* v234 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (28%N) (* v234 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (28%N) (* v234 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (28%N) (* v234 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x4004bb: addq %rax, %rsi *)
| 4195515%N => Some (3, 
    Move (Va (V_TEMP (29%N) (* v237 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (V_TEMP (30%N) (* v238 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (30%N) (* v238 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (29%N) (* v237 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (29%N) (* v237 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (30%N) (* v238 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (29%N) (* v237 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSI) (NumT 64))) (Var (Va (V_TEMP (29%N) (* v237 *)) (NumT 64)))) (Var (Va (V_TEMP (30%N) (* v238 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (31%N) (* v239 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (31%N) (* v239 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (31%N) (* v239 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (31%N) (* v239 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (31%N) (* v239 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (31%N) (* v239 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSI) (NumT 64))))
  )

(* 0x4004be: sarq %rsi *)
| 4195518%N => Some (3, 
    Move (Va (V_TEMP (32%N) (* tmp243 *)) (NumT 64)) (Var (Va (R_RSI) (NumT 64))) $;
    Move (Va (R_RSI) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 1%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (32%N) (* tmp243 *)) (NumT 64))) (Word 64%N 64)) (BinOp OP_AND (Word 1%N 64) (BinOp OP_MINUS (Word 64%N 64) (Word 1%N 64))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSI) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (33%N) (* v244 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSI) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSI) (NumT 64)))) (Let (Va (V_TEMP (33%N) (* v244 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (33%N) (* v244 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (33%N) (* v244 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (33%N) (* v244 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (33%N) (* v244 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1)
  )

(* 0x4004c1: je 0x15 *)
| 4195521%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word 4195544%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4004c3: movl $0x0, %eax *)
| 4195523%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word 0%N 64)
  )

(* 0x4004c8: testq %rax, %rax *)
| 4195528%N => Some (3, 
    Move (Va (V_TEMP (34%N) (* v301 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (35%N) (* v302 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (34%N) (* v301 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (34%N) (* v301 *)) (NumT 64)))) (Let (Va (V_TEMP (35%N) (* v302 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (35%N) (* v302 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (35%N) (* v302 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (35%N) (* v302 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (35%N) (* v302 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (34%N) (* v301 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (34%N) (* v301 *)) (NumT 64))))
  )

(* 0x4004cb: je 0xb *)
| 4195531%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word 4195544%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4004cd: popq %rbp *)
| 4195533%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x4004ce: movl $0x601038, %edi *)
| 4195534%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word 6295608%N 64)
  )

(* 0x4004d3: jmpq *%rax *)
| 4195539%N => Some (2,
    Jmp (Var (Va (R_RAX) (NumT 64)))
  )

(* 0x4004d8: popq %rbp *)
| 4195544%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x4004d9: retq *)
| 4195545%N => Some (1, 
    Move (Va (V_TEMP (36%N) (* v197 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (36%N) (* v197 *)) (NumT 64)))
  )

(* 0x40051a: pushq %rbp *)
| 4195610%N => Some (1, 
    Move (Va (V_TEMP (37%N) (* v247 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (37%N) (* v247 *)) (NumT 64))) LittleE 8)
  )

(* 0x40051b: movq %rsp, %rbp *)
| 4195611%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x40051e: callq *%rax *)
| 4195614%N => Some (2, 
    Move (Va (V_TEMP (38%N) (* v249 *)) (NumT 64)) (Var (Va (R_RAX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195616%N 64) LittleE 8) $;
    Jmp (Var (Va (V_TEMP (38%N) (* v249 *)) (NumT 64)))
  )

(* 0x400520: popq %rbp *)
| 4195616%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x400521: jmp -0x86 *)
| 4195617%N => Some (5,
    Jmp (Word 4195488%N 64)
  )

(* 0x400526: pushq %rbp *)
| 4195622%N => Some (1, 
    Move (Va (V_TEMP (39%N) (* v259 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (39%N) (* v259 *)) (NumT 64))) LittleE 8)
  )

(* 0x400527: movq %rsp, %rbp *)
| 4195623%N => Some (3,
    Move (Va (R_RBP) (NumT 64)) (Var (Va (R_RSP) (NumT 64)))
  )

(* 0x40052a: movl $0x4005c4, %edi *)
| 4195626%N => Some (5,
    Move (Va (R_RDI) (NumT 64)) (Word 4195780%N 64)
  )

(* 0x40052f: callq -0x134 *)
| 4195631%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195636%N 64) LittleE 8) $;
    Jmp (Word 4195328%N 64)
  )

(* 0x400534: movl $0x0, %eax *)
| 4195636%N => Some (5,
    Move (Va (R_RAX) (NumT 64)) (Word 0%N 64)
  )

(* 0x400539: popq %rbp *)
| 4195641%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x40053a: retq *)
| 4195642%N => Some (1, 
    Move (Va (V_TEMP (40%N) (* v271 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (40%N) (* v271 *)) (NumT 64)))
  )

(* 0x400540: pushq %r15 *)
| 4195648%N => Some (2, 
    Move (Va (V_TEMP (41%N) (* v273 *)) (NumT 64)) (Var (Va (R_R15) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (41%N) (* v273 *)) (NumT 64))) LittleE 8)
  )

(* 0x400542: pushq %r14 *)
| 4195650%N => Some (2, 
    Move (Va (V_TEMP (42%N) (* v275 *)) (NumT 64)) (Var (Va (R_R14) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (42%N) (* v275 *)) (NumT 64))) LittleE 8)
  )

(* 0x400544: movl %edi, %r15d *)
| 4195652%N => Some (3,
    Move (Va (R_R15) (NumT 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var (Va (R_RDI) (NumT 64)))))
  )

(* 0x400547: pushq %r13 *)
| 4195655%N => Some (2, 
    Move (Va (V_TEMP (43%N) (* v277 *)) (NumT 64)) (Var (Va (R_R13) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (43%N) (* v277 *)) (NumT 64))) LittleE 8)
  )

(* 0x400549: pushq %r12 *)
| 4195657%N => Some (2, 
    Move (Va (V_TEMP (44%N) (* v279 *)) (NumT 64)) (Var (Va (R_R12) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (44%N) (* v279 *)) (NumT 64))) LittleE 8)
  )

(* 0x40054b: leaq 0x2008be(%rip), %r12 *)
| 4195659%N => Some (7,
    Move (Va (R_R12) (NumT 64)) (Word 6295056%N 64)
  )

(* 0x400552: pushq %rbp *)
| 4195666%N => Some (1, 
    Move (Va (V_TEMP (45%N) (* v281 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (45%N) (* v281 *)) (NumT 64))) LittleE 8)
  )

(* 0x400553: leaq 0x2008be(%rip), %rbp *)
| 4195667%N => Some (7,
    Move (Va (R_RBP) (NumT 64)) (Word 6295064%N 64)
  )

(* 0x40055a: pushq %rbx *)
| 4195674%N => Some (1, 
    Move (Va (V_TEMP (46%N) (* v283 *)) (NumT 64)) (Var (Va (R_RBX) (NumT 64))) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (46%N) (* v283 *)) (NumT 64))) LittleE 8)
  )

(* 0x40055b: movq %rsi, %r14 *)
| 4195675%N => Some (3,
    Move (Va (R_R14) (NumT 64)) (Var (Va (R_RSI) (NumT 64)))
  )

(* 0x40055e: movq %rdx, %r13 *)
| 4195678%N => Some (3,
    Move (Va (R_R13) (NumT 64)) (Var (Va (R_RDX) (NumT 64)))
  )

(* 0x400561: subq %r12, %rbp *)
| 4195681%N => Some (3, 
    Move (Va (V_TEMP (47%N) (* v285 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (V_TEMP (48%N) (* v286 *)) (NumT 64)) (Var (Va (R_R12) (NumT 64))) $;
    Move (Va (R_RBP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RBP) (NumT 64))) (Var (Va (R_R12) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (47%N) (* v285 *)) (NumT 64))) (Var (Va (V_TEMP (48%N) (* v286 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (47%N) (* v285 *)) (NumT 64))) (Var (Va (V_TEMP (48%N) (* v286 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (47%N) (* v285 *)) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RBP) (NumT 64))) (Var (Va (V_TEMP (47%N) (* v285 *)) (NumT 64)))) (Var (Va (V_TEMP (48%N) (* v286 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (49%N) (* v287 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RBP) (NumT 64)))) (Let (Va (V_TEMP (49%N) (* v287 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (49%N) (* v287 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (49%N) (* v287 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (49%N) (* v287 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (49%N) (* v287 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RBP) (NumT 64))))
  )

(* 0x400564: subq $0x8, %rsp *)
| 4195684%N => Some (4, 
    Move (Va (V_TEMP (50%N) (* v291 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (51%N) (* v292 *)) (NumT 64)) (Word 8%N 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (V_TEMP (50%N) (* v291 *)) (NumT 64))) (Var (Va (V_TEMP (51%N) (* v292 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (V_TEMP (50%N) (* v291 *)) (NumT 64))) (Var (Va (V_TEMP (51%N) (* v292 *)) (NumT 64)))) (BinOp OP_XOR (Var (Va (V_TEMP (50%N) (* v291 *)) (NumT 64))) (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (50%N) (* v291 *)) (NumT 64)))) (Var (Va (V_TEMP (51%N) (* v292 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (52%N) (* v293 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (52%N) (* v293 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (52%N) (* v293 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (52%N) (* v293 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (52%N) (* v293 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (52%N) (* v293 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x400568: sarq $0x3, %rbp *)
| 4195688%N => Some (4, 
    Move (Va (V_TEMP (53%N) (* tmp297 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_RBP) (NumT 64)) (BinOp OP_ARSHIFT (Var (Va (R_RBP) (NumT 64))) (Word 3%N 64)) $;
    Move (Va (R_CF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (Va (V_TEMP (53%N) (* tmp297 *)) (NumT 64))) (Word 64%N 64)) (BinOp OP_AND (Word 3%N 64) (BinOp OP_MINUS (Word 64%N 64) (Word 1%N 64))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (54%N) (* v298 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RBP) (NumT 64)))) (Let (Va (V_TEMP (54%N) (* v298 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (54%N) (* v298 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (54%N) (* v298 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (54%N) (* v298 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (54%N) (* v298 *)) (NumT 64)))))))) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_OF) (NumT 1)) (Unknown (NumT 1))
  )

(* 0x40056c: callq -0x1a9 *)
| 4195692%N => Some (5, 
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195697%N 64) LittleE 8) $;
    Jmp (Word 4195272%N 64)
  )

(* 0x400571: testq %rbp, %rbp *)
| 4195697%N => Some (3, 
    Move (Va (V_TEMP (55%N) (* v203 *)) (NumT 64)) (Var (Va (R_RBP) (NumT 64))) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (56%N) (* v204 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (55%N) (* v203 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (55%N) (* v203 *)) (NumT 64)))) (Let (Va (V_TEMP (56%N) (* v204 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (56%N) (* v204 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (56%N) (* v204 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (56%N) (* v204 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (56%N) (* v204 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (55%N) (* v203 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (55%N) (* v203 *)) (NumT 64))))
  )

(* 0x400574: je 0x20 *)
| 4195700%N => Some (2,
    If (Var (Va (R_ZF) (NumT 1))) (
      Jmp (Word 4195734%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400576: xorl %ebx, %ebx *)
| 4195702%N => Some (2, 
    Move (Va (R_RBX) (NumT 64)) (Word 0%N 64) $;
    Move (Va (R_AF) (NumT 1)) (Unknown (NumT 1)) $;
    Move (Va (R_ZF) (NumT 1)) (Word 1%N 1) $;
    Move (Va (R_PF) (NumT 1)) (Word 1%N 1) $;
    Move (Va (R_OF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_CF) (NumT 1)) (Word 0%N 1) $;
    Move (Va (R_SF) (NumT 1)) (Word 0%N 1)
  )

(* 0x400578: nopl (%rax,%rax) *)
| 4195704%N => Some (8,
    Nop
  )

(* 0x400580: movq %r13, %rdx *)
| 4195712%N => Some (3,
    Move (Va (R_RDX) (NumT 64)) (Var (Va (R_R13) (NumT 64)))
  )

(* 0x400583: movq %r14, %rsi *)
| 4195715%N => Some (3,
    Move (Va (R_RSI) (NumT 64)) (Var (Va (R_R14) (NumT 64)))
  )

(* 0x400586: movl %r15d, %edi *)
| 4195718%N => Some (3,
    Move (Va (R_RDI) (NumT 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var (Va (R_R15) (NumT 64)))))
  )

(* 0x400589: callq *(%r12,%rbx,8) *)
| 4195721%N => Some (4, 
    Move (Va (V_TEMP (57%N) (* v199 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (BinOp OP_PLUS (Var (Va (R_R12) (NumT 64))) (BinOp OP_LSHIFT (Var (Va (R_RBX) (NumT 64))) (Word 3%N 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Move (Va (V_MEM64) (MemT 64)) (Store (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) (Word 4195725%N 64) LittleE 8) $;
    Jmp (Var (Va (V_TEMP (57%N) (* v199 *)) (NumT 64)))
  )

(* 0x40058d: addq $0x1, %rbx *)
| 4195725%N => Some (4, 
    Move (Va (V_TEMP (58%N) (* v261 *)) (NumT 64)) (Var (Va (R_RBX) (NumT 64))) $;
    Move (Va (V_TEMP (59%N) (* v262 *)) (NumT 64)) (Word 1%N 64) $;
    Move (Va (R_RBX) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (59%N) (* v262 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (58%N) (* v261 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (58%N) (* v261 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (59%N) (* v262 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (58%N) (* v261 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RBX) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (58%N) (* v261 *)) (NumT 64)))) (Var (Va (V_TEMP (59%N) (* v262 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (60%N) (* v263 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RBX) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RBX) (NumT 64)))) (Let (Va (V_TEMP (60%N) (* v263 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (60%N) (* v263 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (60%N) (* v263 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (60%N) (* v263 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (60%N) (* v263 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RBX) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RBX) (NumT 64))))
  )

(* 0x400591: cmpq %rbp, %rbx *)
| 4195729%N => Some (3, 
    Move (Va (V_TEMP (61%N) (* v267 *)) (NumT 64)) (BinOp OP_MINUS (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (R_RBP) (NumT 64)))) (BinOp OP_XOR (Var (Va (R_RBX) (NumT 64))) (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64))) (Var (Va (R_RBX) (NumT 64)))) (Var (Va (R_RBP) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (62%N) (* v268 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64))) (Word 4%N 64)) (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64)))) (Let (Va (V_TEMP (62%N) (* v268 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (62%N) (* v268 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (62%N) (* v268 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (62%N) (* v268 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (62%N) (* v268 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (V_TEMP (61%N) (* v267 *)) (NumT 64))))
  )

(* 0x400594: jne -0x16 *)
| 4195732%N => Some (2,
    If (UnOp OP_NOT (Var (Va (R_ZF) (NumT 1)))) (
      Jmp (Word 4195712%N 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400596: addq $0x8, %rsp *)
| 4195734%N => Some (4, 
    Move (Va (V_TEMP (63%N) (* v305 *)) (NumT 64)) (Var (Va (R_RSP) (NumT 64))) $;
    Move (Va (V_TEMP (64%N) (* v306 *)) (NumT 64)) (Word 8%N 64) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (64%N) (* v306 *)) (NumT 64)))) $;
    Move (Va (R_CF) (NumT 1)) (BinOp OP_LT (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (63%N) (* v305 *)) (NumT 64)))) $;
    Move (Va (R_OF) (NumT 1)) (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (Va (V_TEMP (63%N) (* v305 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (V_TEMP (64%N) (* v306 *)) (NumT 64))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (Va (V_TEMP (63%N) (* v305 *)) (NumT 64)))) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))))) $;
    Move (Va (R_AF) (NumT 1)) (BinOp OP_EQ (Word 16%N 64) (BinOp OP_AND (Word 16%N 64) (BinOp OP_XOR (BinOp OP_XOR (Var (Va (R_RSP) (NumT 64))) (Var (Va (V_TEMP (63%N) (* v305 *)) (NumT 64)))) (Var (Va (V_TEMP (64%N) (* v306 *)) (NumT 64)))))) $;
    Move (Va (R_PF) (NumT 1)) (UnOp OP_NOT (Cast CAST_LOW 1 (Let (Va (V_TEMP (65%N) (* v307 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (R_RSP) (NumT 64))) (Word 4%N 64)) (Var (Va (R_RSP) (NumT 64)))) (Let (Va (V_TEMP (65%N) (* v307 *)) (NumT 64)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (65%N) (* v307 *)) (NumT 64))) (Word 2%N 64)) (Var (Va (V_TEMP (65%N) (* v307 *)) (NumT 64)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (Va (V_TEMP (65%N) (* v307 *)) (NumT 64))) (Word 1%N 64)) (Var (Va (V_TEMP (65%N) (* v307 *)) (NumT 64)))))))) $;
    Move (Va (R_SF) (NumT 1)) (Cast CAST_HIGH 1 (Var (Va (R_RSP) (NumT 64)))) $;
    Move (Va (R_ZF) (NumT 1)) (BinOp OP_EQ (Word 0%N 64) (Var (Va (R_RSP) (NumT 64))))
  )

(* 0x40059a: popq %rbx *)
| 4195738%N => Some (1, 
    Move (Va (R_RBX) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x40059b: popq %rbp *)
| 4195739%N => Some (1, 
    Move (Va (R_RBP) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x40059c: popq %r12 *)
| 4195740%N => Some (2, 
    Move (Va (R_R12) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x40059e: popq %r13 *)
| 4195742%N => Some (2, 
    Move (Va (R_R13) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x4005a0: popq %r14 *)
| 4195744%N => Some (2, 
    Move (Va (R_R14) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x4005a2: popq %r15 *)
| 4195746%N => Some (2, 
    Move (Va (R_R15) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64))
  )

(* 0x4005a4: retq *)
| 4195748%N => Some (1, 
    Move (Va (V_TEMP (66%N) (* v311 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (66%N) (* v311 *)) (NumT 64)))
  )

(* 0x4005b0: retq *)
| 4195760%N => Some (2, 
    Move (Va (V_TEMP (67%N) (* v201 *)) (NumT 64)) (Load (Var (Va (V_MEM64) (MemT 64))) (Var (Va (R_RSP) (NumT 64))) LittleE 8) $;
    Move (Va (R_RSP) (NumT 64)) (BinOp OP_PLUS (Var (Va (R_RSP) (NumT 64))) (Word 8%N 64)) $;
    Jmp (Var (Va (V_TEMP (67%N) (* v201 *)) (NumT 64)))
  )

| _ => None
end.
