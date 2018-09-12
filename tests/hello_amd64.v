Add LoadPath "..".
Require Import Picinae_amd64.
Import PArch_amd64.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x4003c8: subq $0x8, %rsp *)
| 4195272 => Some (4, 
    Move (V_TEMP 0 (* v211 *)) (Var R_RSP) $;
    Move (V_TEMP 1 (* v212 *)) (Word 8 64) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 0 (* v211 *))) (Var (V_TEMP 1 (* v212 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 0 (* v211 *))) (Var (V_TEMP 1 (* v212 *)))) (BinOp OP_XOR (Var (V_TEMP 0 (* v211 *))) (Var R_RSP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSP) (Var (V_TEMP 0 (* v211 *)))) (Var (V_TEMP 1 (* v212 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 2 (* v213 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 2 (* v213 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v213 *))) (Word 2 64)) (Var (V_TEMP 2 (* v213 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 2 (* v213 *))) (Word 1 64)) (Var (V_TEMP 2 (* v213 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x4003cc: movq 0x200c25(%rip), %rax *)
| 4195276 => Some (7,
    Move R_RAX (Load (Var V_MEM64) (Word 6295544 64) LittleE 8)
  )

(* 0x4003d3: testq %rax, %rax *)
| 4195283 => Some (3, 
    Move (V_TEMP 3 (* v217 *)) (Var R_RAX) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 4 (* v218 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v217 *))) (Word 4 64)) (Var (V_TEMP 3 (* v217 *)))) (Let (V_TEMP 4 (* v218 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v218 *))) (Word 2 64)) (Var (V_TEMP 4 (* v218 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 4 (* v218 *))) (Word 1 64)) (Var (V_TEMP 4 (* v218 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 3 (* v217 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 3 (* v217 *))))
  )

(* 0x4003d6: je 0x5 *)
| 4195286 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 4195293 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4003d8: callq 0x43 *)
| 4195288 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195293 64) LittleE 8) $;
    Jmp (Word 4195360 64)
  )

(* 0x4003dd: addq $0x8, %rsp *)
| 4195293 => Some (4, 
    Move (V_TEMP 5 (* v251 *)) (Var R_RSP) $;
    Move (V_TEMP 6 (* v252 *)) (Word 8 64) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 6 (* v252 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RSP) (Var (V_TEMP 5 (* v251 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* v251 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 6 (* v252 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* v251 *)))) (Cast CAST_HIGH 1 (Var R_RSP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSP) (Var (V_TEMP 5 (* v251 *)))) (Var (V_TEMP 6 (* v252 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 7 (* v253 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 7 (* v253 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v253 *))) (Word 2 64)) (Var (V_TEMP 7 (* v253 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v253 *))) (Word 1 64)) (Var (V_TEMP 7 (* v253 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x4003e1: retq *)
| 4195297 => Some (1, 
    Move (V_TEMP 8 (* v257 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 8 (* v257 *)))
  )

(* 0x400400: jmpq *0x200c12(%rip) *)
| 4195328 => Some (6,
    Jmp (Load (Var V_MEM64) (Word 6295576 64) LittleE 8)
  )

(* 0x400410: jmpq *0x200c0a(%rip) *)
| 4195344 => Some (6,
    Jmp (Load (Var V_MEM64) (Word 6295584 64) LittleE 8)
  )

(* 0x400420: jmpq *0x200bd2(%rip) *)
| 4195360 => Some (6,
    Jmp (Load (Var V_MEM64) (Word 6295544 64) LittleE 8)
  )

(* 0x400430: xorl %ebp, %ebp *)
| 4195376 => Some (2, 
    Move R_RBP (Word 0 64) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0x400432: movq %rdx, %r9 *)
| 4195378 => Some (3,
    Move R_R9 (Var R_RDX)
  )

(* 0x400435: popq %rsi *)
| 4195381 => Some (1, 
    Move R_RSI (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x400436: movq %rsp, %rdx *)
| 4195382 => Some (3,
    Move R_RDX (Var R_RSP)
  )

(* 0x400439: andq $-0x10, %rsp *)
| 4195385 => Some (4, 
    Move R_RSP (BinOp OP_AND (Var R_RSP) (Word 18446744073709551600 64)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 9 (* v191 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 9 (* v191 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v191 *))) (Word 2 64)) (Var (V_TEMP 9 (* v191 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* v191 *))) (Word 1 64)) (Var (V_TEMP 9 (* v191 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x40043d: pushq %rax *)
| 4195389 => Some (1, 
    Move (V_TEMP 10 (* v193 *)) (Var R_RAX) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 10 (* v193 *))) LittleE 8)
  )

(* 0x40043e: pushq %rsp *)
| 4195390 => Some (1, 
    Move (V_TEMP 11 (* v195 *)) (Var R_RSP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 11 (* v195 *))) LittleE 8)
  )

(* 0x40043f: movq $0x4005b0, %r8 *)
| 4195391 => Some (7,
    Move R_R8 (Word 4195760 64)
  )

(* 0x400446: movq $0x400540, %rcx *)
| 4195398 => Some (7,
    Move R_RCX (Word 4195648 64)
  )

(* 0x40044d: movq $0x400526, %rdi *)
| 4195405 => Some (7,
    Move R_RDI (Word 4195622 64)
  )

(* 0x400454: callq -0x49 *)
| 4195412 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195417 64) LittleE 8) $;
    Jmp (Word 4195344 64)
  )

(* 0x400459: hlt *)
| 4195417 => Some (1,
    Nop
  )

(* 0x40045a: nopw (%rax,%rax) *)
| 4195418 => Some (6,
    Nop
  )

(* 0x400460: movl $0x60103f, %eax *)
| 4195424 => Some (5,
    Move R_RAX (Word 6295615 64)
  )

(* 0x400465: pushq %rbp *)
| 4195429 => Some (1, 
    Move (V_TEMP 12 (* v313 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 12 (* v313 *))) LittleE 8)
  )

(* 0x400466: subq $0x601038, %rax *)
| 4195430 => Some (6, 
    Move (V_TEMP 13 (* v315 *)) (Var R_RAX) $;
    Move (V_TEMP 14 (* v316 *)) (Word 6295608 64) $;
    Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Word 6295608 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 13 (* v315 *))) (Var (V_TEMP 14 (* v316 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 13 (* v315 *))) (Var (V_TEMP 14 (* v316 *)))) (BinOp OP_XOR (Var (V_TEMP 13 (* v315 *))) (Var R_RAX)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 13 (* v315 *)))) (Var (V_TEMP 14 (* v316 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 15 (* v317 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 15 (* v317 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v317 *))) (Word 2 64)) (Var (V_TEMP 15 (* v317 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 15 (* v317 *))) (Word 1 64)) (Var (V_TEMP 15 (* v317 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX))
  )

(* 0x40046c: cmpq $0xe, %rax *)
| 4195436 => Some (4, 
    Move (V_TEMP 16 (* v321 *)) (BinOp OP_MINUS (Var R_RAX) (Word 14 64)) $;
    Move R_CF (BinOp OP_LT (Var R_RAX) (Word 14 64)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var R_RAX) (Word 14 64)) (BinOp OP_XOR (Var R_RAX) (Var (V_TEMP 16 (* v321 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 16 (* v321 *))) (Var R_RAX)) (Word 14 64)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 17 (* v322 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 16 (* v321 *))) (Word 4 64)) (Var (V_TEMP 16 (* v321 *)))) (Let (V_TEMP 17 (* v322 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v322 *))) (Word 2 64)) (Var (V_TEMP 17 (* v322 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 17 (* v322 *))) (Word 1 64)) (Var (V_TEMP 17 (* v322 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 16 (* v321 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 16 (* v321 *))))
  )

(* 0x400470: movq %rsp, %rbp *)
| 4195440 => Some (3,
    Move R_RBP (Var R_RSP)
  )

(* 0x400473: jbe 0x1b *)
| 4195443 => Some (2,
    If (BinOp OP_OR (Var R_CF) (Var R_ZF)) (
      Jmp (Word 4195472 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400475: movl $0x0, %eax *)
| 4195445 => Some (5,
    Move R_RAX (Word 0 64)
  )

(* 0x40047a: testq %rax, %rax *)
| 4195450 => Some (3, 
    Move (V_TEMP 18 (* v207 *)) (Var R_RAX) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 19 (* v208 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 18 (* v207 *))) (Word 4 64)) (Var (V_TEMP 18 (* v207 *)))) (Let (V_TEMP 19 (* v208 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v208 *))) (Word 2 64)) (Var (V_TEMP 19 (* v208 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 19 (* v208 *))) (Word 1 64)) (Var (V_TEMP 19 (* v208 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 18 (* v207 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 18 (* v207 *))))
  )

(* 0x40047d: je 0x11 *)
| 4195453 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 4195472 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x40047f: popq %rbp *)
| 4195455 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x400480: movl $0x601038, %edi *)
| 4195456 => Some (5,
    Move R_RDI (Word 6295608 64)
  )

(* 0x400485: jmpq *%rax *)
| 4195461 => Some (2,
    Jmp (Var R_RAX)
  )

(* 0x400490: popq %rbp *)
| 4195472 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x400491: retq *)
| 4195473 => Some (1, 
    Move (V_TEMP 20 (* v189 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 20 (* v189 *)))
  )

(* 0x4004a0: movl $0x601038, %esi *)
| 4195488 => Some (5,
    Move R_RSI (Word 6295608 64)
  )

(* 0x4004a5: pushq %rbp *)
| 4195493 => Some (1, 
    Move (V_TEMP 21 (* v221 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 21 (* v221 *))) LittleE 8)
  )

(* 0x4004a6: subq $0x601038, %rsi *)
| 4195494 => Some (7, 
    Move (V_TEMP 22 (* v223 *)) (Var R_RSI) $;
    Move (V_TEMP 23 (* v224 *)) (Word 6295608 64) $;
    Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 6295608 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 22 (* v223 *))) (Var (V_TEMP 23 (* v224 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 22 (* v223 *))) (Var (V_TEMP 23 (* v224 *)))) (BinOp OP_XOR (Var (V_TEMP 22 (* v223 *))) (Var R_RSI)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSI) (Var (V_TEMP 22 (* v223 *)))) (Var (V_TEMP 23 (* v224 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 24 (* v225 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSI) (Word 4 64)) (Var R_RSI)) (Let (V_TEMP 24 (* v225 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v225 *))) (Word 2 64)) (Var (V_TEMP 24 (* v225 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 24 (* v225 *))) (Word 1 64)) (Var (V_TEMP 24 (* v225 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSI)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSI))
  )

(* 0x4004ad: sarq $0x3, %rsi *)
| 4195501 => Some (4, 
    Move (V_TEMP 25 (* tmp229 *)) (Var R_RSI) $;
    Move R_RSI (BinOp OP_ARSHIFT (Var R_RSI) (Word 3 64)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 25 (* tmp229 *))) (Word 64 64)) (BinOp OP_AND (Word 3 64) (BinOp OP_MINUS (Word 64 64) (Word 1 64))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSI)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSI)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 26 (* v230 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSI) (Word 4 64)) (Var R_RSI)) (Let (V_TEMP 26 (* v230 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v230 *))) (Word 2 64)) (Var (V_TEMP 26 (* v230 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v230 *))) (Word 1 64)) (Var (V_TEMP 26 (* v230 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x4004b1: movq %rsp, %rbp *)
| 4195505 => Some (3,
    Move R_RBP (Var R_RSP)
  )

(* 0x4004b4: movq %rsi, %rax *)
| 4195508 => Some (3,
    Move R_RAX (Var R_RSI)
  )

(* 0x4004b7: shrq $0x3f, %rax *)
| 4195511 => Some (4, 
    Move (V_TEMP 27 (* tmp233 *)) (Var R_RAX) $;
    Move R_RAX (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 27 (* tmp233 *))) (Word 64 64)) (BinOp OP_AND (Word 63 64) (BinOp OP_MINUS (Word 64 64) (Word 1 64))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RAX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RAX)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 28 (* v234 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RAX) (Word 4 64)) (Var R_RAX)) (Let (V_TEMP 28 (* v234 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v234 *))) (Word 2 64)) (Var (V_TEMP 28 (* v234 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 28 (* v234 *))) (Word 1 64)) (Var (V_TEMP 28 (* v234 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x4004bb: addq %rax, %rsi *)
| 4195515 => Some (3, 
    Move (V_TEMP 29 (* v237 *)) (Var R_RSI) $;
    Move (V_TEMP 30 (* v238 *)) (Var R_RAX) $;
    Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 30 (* v238 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RSI) (Var (V_TEMP 29 (* v237 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 29 (* v237 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v238 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 29 (* v237 *)))) (Cast CAST_HIGH 1 (Var R_RSI)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSI) (Var (V_TEMP 29 (* v237 *)))) (Var (V_TEMP 30 (* v238 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 31 (* v239 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSI) (Word 4 64)) (Var R_RSI)) (Let (V_TEMP 31 (* v239 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v239 *))) (Word 2 64)) (Var (V_TEMP 31 (* v239 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v239 *))) (Word 1 64)) (Var (V_TEMP 31 (* v239 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSI)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSI))
  )

(* 0x4004be: sarq %rsi *)
| 4195518 => Some (3, 
    Move (V_TEMP 32 (* tmp243 *)) (Var R_RSI) $;
    Move R_RSI (BinOp OP_ARSHIFT (Var R_RSI) (Word 1 64)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 32 (* tmp243 *))) (Word 64 64)) (BinOp OP_AND (Word 1 64) (BinOp OP_MINUS (Word 64 64) (Word 1 64))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSI)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSI)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 33 (* v244 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSI) (Word 4 64)) (Var R_RSI)) (Let (V_TEMP 33 (* v244 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v244 *))) (Word 2 64)) (Var (V_TEMP 33 (* v244 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 33 (* v244 *))) (Word 1 64)) (Var (V_TEMP 33 (* v244 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Word 0 1)
  )

(* 0x4004c1: je 0x15 *)
| 4195521 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 4195544 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4004c3: movl $0x0, %eax *)
| 4195523 => Some (5,
    Move R_RAX (Word 0 64)
  )

(* 0x4004c8: testq %rax, %rax *)
| 4195528 => Some (3, 
    Move (V_TEMP 34 (* v301 *)) (Var R_RAX) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 35 (* v302 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 34 (* v301 *))) (Word 4 64)) (Var (V_TEMP 34 (* v301 *)))) (Let (V_TEMP 35 (* v302 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v302 *))) (Word 2 64)) (Var (V_TEMP 35 (* v302 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v302 *))) (Word 1 64)) (Var (V_TEMP 35 (* v302 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 34 (* v301 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 34 (* v301 *))))
  )

(* 0x4004cb: je 0xb *)
| 4195531 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 4195544 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x4004cd: popq %rbp *)
| 4195533 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x4004ce: movl $0x601038, %edi *)
| 4195534 => Some (5,
    Move R_RDI (Word 6295608 64)
  )

(* 0x4004d3: jmpq *%rax *)
| 4195539 => Some (2,
    Jmp (Var R_RAX)
  )

(* 0x4004d8: popq %rbp *)
| 4195544 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x4004d9: retq *)
| 4195545 => Some (1, 
    Move (V_TEMP 36 (* v197 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 36 (* v197 *)))
  )

(* 0x40051a: pushq %rbp *)
| 4195610 => Some (1, 
    Move (V_TEMP 37 (* v247 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 37 (* v247 *))) LittleE 8)
  )

(* 0x40051b: movq %rsp, %rbp *)
| 4195611 => Some (3,
    Move R_RBP (Var R_RSP)
  )

(* 0x40051e: callq *%rax *)
| 4195614 => Some (2, 
    Move (V_TEMP 38 (* v249 *)) (Var R_RAX) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195616 64) LittleE 8) $;
    Jmp (Var (V_TEMP 38 (* v249 *)))
  )

(* 0x400520: popq %rbp *)
| 4195616 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x400521: jmp -0x86 *)
| 4195617 => Some (5,
    Jmp (Word 4195488 64)
  )

(* 0x400526: pushq %rbp *)
| 4195622 => Some (1, 
    Move (V_TEMP 39 (* v259 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 39 (* v259 *))) LittleE 8)
  )

(* 0x400527: movq %rsp, %rbp *)
| 4195623 => Some (3,
    Move R_RBP (Var R_RSP)
  )

(* 0x40052a: movl $0x4005c4, %edi *)
| 4195626 => Some (5,
    Move R_RDI (Word 4195780 64)
  )

(* 0x40052f: callq -0x134 *)
| 4195631 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195636 64) LittleE 8) $;
    Jmp (Word 4195328 64)
  )

(* 0x400534: movl $0x0, %eax *)
| 4195636 => Some (5,
    Move R_RAX (Word 0 64)
  )

(* 0x400539: popq %rbp *)
| 4195641 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x40053a: retq *)
| 4195642 => Some (1, 
    Move (V_TEMP 40 (* v271 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 40 (* v271 *)))
  )

(* 0x400540: pushq %r15 *)
| 4195648 => Some (2, 
    Move (V_TEMP 41 (* v273 *)) (Var R_R15) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 41 (* v273 *))) LittleE 8)
  )

(* 0x400542: pushq %r14 *)
| 4195650 => Some (2, 
    Move (V_TEMP 42 (* v275 *)) (Var R_R14) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 42 (* v275 *))) LittleE 8)
  )

(* 0x400544: movl %edi, %r15d *)
| 4195652 => Some (3,
    Move R_R15 (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_RDI)))
  )

(* 0x400547: pushq %r13 *)
| 4195655 => Some (2, 
    Move (V_TEMP 43 (* v277 *)) (Var R_R13) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 43 (* v277 *))) LittleE 8)
  )

(* 0x400549: pushq %r12 *)
| 4195657 => Some (2, 
    Move (V_TEMP 44 (* v279 *)) (Var R_R12) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 44 (* v279 *))) LittleE 8)
  )

(* 0x40054b: leaq 0x2008be(%rip), %r12 *)
| 4195659 => Some (7,
    Move R_R12 (Word 6295056 64)
  )

(* 0x400552: pushq %rbp *)
| 4195666 => Some (1, 
    Move (V_TEMP 45 (* v281 *)) (Var R_RBP) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 45 (* v281 *))) LittleE 8)
  )

(* 0x400553: leaq 0x2008be(%rip), %rbp *)
| 4195667 => Some (7,
    Move R_RBP (Word 6295064 64)
  )

(* 0x40055a: pushq %rbx *)
| 4195674 => Some (1, 
    Move (V_TEMP 46 (* v283 *)) (Var R_RBX) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 46 (* v283 *))) LittleE 8)
  )

(* 0x40055b: movq %rsi, %r14 *)
| 4195675 => Some (3,
    Move R_R14 (Var R_RSI)
  )

(* 0x40055e: movq %rdx, %r13 *)
| 4195678 => Some (3,
    Move R_R13 (Var R_RDX)
  )

(* 0x400561: subq %r12, %rbp *)
| 4195681 => Some (3, 
    Move (V_TEMP 47 (* v285 *)) (Var R_RBP) $;
    Move (V_TEMP 48 (* v286 *)) (Var R_R12) $;
    Move R_RBP (BinOp OP_MINUS (Var R_RBP) (Var R_R12)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 47 (* v285 *))) (Var (V_TEMP 48 (* v286 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 47 (* v285 *))) (Var (V_TEMP 48 (* v286 *)))) (BinOp OP_XOR (Var (V_TEMP 47 (* v285 *))) (Var R_RBP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RBP) (Var (V_TEMP 47 (* v285 *)))) (Var (V_TEMP 48 (* v286 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 49 (* v287 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RBP) (Word 4 64)) (Var R_RBP)) (Let (V_TEMP 49 (* v287 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 49 (* v287 *))) (Word 2 64)) (Var (V_TEMP 49 (* v287 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 49 (* v287 *))) (Word 1 64)) (Var (V_TEMP 49 (* v287 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RBP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RBP))
  )

(* 0x400564: subq $0x8, %rsp *)
| 4195684 => Some (4, 
    Move (V_TEMP 50 (* v291 *)) (Var R_RSP) $;
    Move (V_TEMP 51 (* v292 *)) (Word 8 64) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 50 (* v291 *))) (Var (V_TEMP 51 (* v292 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 50 (* v291 *))) (Var (V_TEMP 51 (* v292 *)))) (BinOp OP_XOR (Var (V_TEMP 50 (* v291 *))) (Var R_RSP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSP) (Var (V_TEMP 50 (* v291 *)))) (Var (V_TEMP 51 (* v292 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 52 (* v293 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 52 (* v293 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 52 (* v293 *))) (Word 2 64)) (Var (V_TEMP 52 (* v293 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 52 (* v293 *))) (Word 1 64)) (Var (V_TEMP 52 (* v293 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x400568: sarq $0x3, %rbp *)
| 4195688 => Some (4, 
    Move (V_TEMP 53 (* tmp297 *)) (Var R_RBP) $;
    Move R_RBP (BinOp OP_ARSHIFT (Var R_RBP) (Word 3 64)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 53 (* tmp297 *))) (Word 64 64)) (BinOp OP_AND (Word 3 64) (BinOp OP_MINUS (Word 64 64) (Word 1 64))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RBP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RBP)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 54 (* v298 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RBP) (Word 4 64)) (Var R_RBP)) (Let (V_TEMP 54 (* v298 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 54 (* v298 *))) (Word 2 64)) (Var (V_TEMP 54 (* v298 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 54 (* v298 *))) (Word 1 64)) (Var (V_TEMP 54 (* v298 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x40056c: callq -0x1a9 *)
| 4195692 => Some (5, 
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195697 64) LittleE 8) $;
    Jmp (Word 4195272 64)
  )

(* 0x400571: testq %rbp, %rbp *)
| 4195697 => Some (3, 
    Move (V_TEMP 55 (* v203 *)) (Var R_RBP) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 56 (* v204 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 55 (* v203 *))) (Word 4 64)) (Var (V_TEMP 55 (* v203 *)))) (Let (V_TEMP 56 (* v204 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 56 (* v204 *))) (Word 2 64)) (Var (V_TEMP 56 (* v204 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 56 (* v204 *))) (Word 1 64)) (Var (V_TEMP 56 (* v204 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 55 (* v203 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 55 (* v203 *))))
  )

(* 0x400574: je 0x20 *)
| 4195700 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 4195734 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400576: xorl %ebx, %ebx *)
| 4195702 => Some (2, 
    Move R_RBX (Word 0 64) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0x400578: nopl (%rax,%rax) *)
| 4195704 => Some (8,
    Nop
  )

(* 0x400580: movq %r13, %rdx *)
| 4195712 => Some (3,
    Move R_RDX (Var R_R13)
  )

(* 0x400583: movq %r14, %rsi *)
| 4195715 => Some (3,
    Move R_RSI (Var R_R14)
  )

(* 0x400586: movl %r15d, %edi *)
| 4195718 => Some (3,
    Move R_RDI (Cast CAST_UNSIGNED 64 (Cast CAST_LOW 32 (Var R_R15)))
  )

(* 0x400589: callq *(%r12,%rbx,8) *)
| 4195721 => Some (4, 
    Move (V_TEMP 57 (* v199 *)) (Load (Var V_MEM64) (BinOp OP_PLUS (Var R_R12) (BinOp OP_LSHIFT (Var R_RBX) (Word 3 64))) LittleE 8) $;
    Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 8 64)) $;
    Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 4195725 64) LittleE 8) $;
    Jmp (Var (V_TEMP 57 (* v199 *)))
  )

(* 0x40058d: addq $0x1, %rbx *)
| 4195725 => Some (4, 
    Move (V_TEMP 58 (* v261 *)) (Var R_RBX) $;
    Move (V_TEMP 59 (* v262 *)) (Word 1 64) $;
    Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Var (V_TEMP 59 (* v262 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RBX) (Var (V_TEMP 58 (* v261 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 58 (* v261 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 59 (* v262 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 58 (* v261 *)))) (Cast CAST_HIGH 1 (Var R_RBX)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RBX) (Var (V_TEMP 58 (* v261 *)))) (Var (V_TEMP 59 (* v262 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 60 (* v263 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RBX) (Word 4 64)) (Var R_RBX)) (Let (V_TEMP 60 (* v263 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 60 (* v263 *))) (Word 2 64)) (Var (V_TEMP 60 (* v263 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 60 (* v263 *))) (Word 1 64)) (Var (V_TEMP 60 (* v263 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RBX)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RBX))
  )

(* 0x400591: cmpq %rbp, %rbx *)
| 4195729 => Some (3, 
    Move (V_TEMP 61 (* v267 *)) (BinOp OP_MINUS (Var R_RBX) (Var R_RBP)) $;
    Move R_CF (BinOp OP_LT (Var R_RBX) (Var R_RBP)) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var R_RBX) (Var R_RBP)) (BinOp OP_XOR (Var R_RBX) (Var (V_TEMP 61 (* v267 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 61 (* v267 *))) (Var R_RBX)) (Var R_RBP)))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 62 (* v268 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 61 (* v267 *))) (Word 4 64)) (Var (V_TEMP 61 (* v267 *)))) (Let (V_TEMP 62 (* v268 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 62 (* v268 *))) (Word 2 64)) (Var (V_TEMP 62 (* v268 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 62 (* v268 *))) (Word 1 64)) (Var (V_TEMP 62 (* v268 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 61 (* v267 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var (V_TEMP 61 (* v267 *))))
  )

(* 0x400594: jne -0x16 *)
| 4195732 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 4195712 64)
    ) (* else *) (
      Nop
    )
  )

(* 0x400596: addq $0x8, %rsp *)
| 4195734 => Some (4, 
    Move (V_TEMP 63 (* v305 *)) (Var R_RSP) $;
    Move (V_TEMP 64 (* v306 *)) (Word 8 64) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 64 (* v306 *)))) $;
    Move R_CF (BinOp OP_LT (Var R_RSP) (Var (V_TEMP 63 (* v305 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 63 (* v305 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 64 (* v306 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 63 (* v305 *)))) (Cast CAST_HIGH 1 (Var R_RSP)))) $;
    Move R_AF (BinOp OP_EQ (Word 16 64) (BinOp OP_AND (Word 16 64) (BinOp OP_XOR (BinOp OP_XOR (Var R_RSP) (Var (V_TEMP 63 (* v305 *)))) (Var (V_TEMP 64 (* v306 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 65 (* v307 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var R_RSP) (Word 4 64)) (Var R_RSP)) (Let (V_TEMP 65 (* v307 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 65 (* v307 *))) (Word 2 64)) (Var (V_TEMP 65 (* v307 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 65 (* v307 *))) (Word 1 64)) (Var (V_TEMP 65 (* v307 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var R_RSP)) $;
    Move R_ZF (BinOp OP_EQ (Word 0 64) (Var R_RSP))
  )

(* 0x40059a: popq %rbx *)
| 4195738 => Some (1, 
    Move R_RBX (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x40059b: popq %rbp *)
| 4195739 => Some (1, 
    Move R_RBP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x40059c: popq %r12 *)
| 4195740 => Some (2, 
    Move R_R12 (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x40059e: popq %r13 *)
| 4195742 => Some (2, 
    Move R_R13 (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x4005a0: popq %r14 *)
| 4195744 => Some (2, 
    Move R_R14 (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x4005a2: popq %r15 *)
| 4195746 => Some (2, 
    Move R_R15 (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64))
  )

(* 0x4005a4: retq *)
| 4195748 => Some (1, 
    Move (V_TEMP 66 (* v311 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 66 (* v311 *)))
  )

(* 0x4005b0: retq *)
| 4195760 => Some (2, 
    Move (V_TEMP 67 (* v201 *)) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
    Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
    Jmp (Var (V_TEMP 67 (* v201 *)))
  )

| _ => None
end.
