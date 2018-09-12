Add LoadPath "..".
Require Import Picinae_i386.
Import PArch_i386.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition my_prog : program := fun a => match a with

(* 0x80482a8: pushl %ebx *)
| 134513320 => Some (1, 
    Move (V_TEMP 0 (* v433 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 0 (* v433 *))) LittleE 4)
  )

(* 0x80482a9: subl $0x8, %esp *)
| 134513321 => Some (3, 
    Move (V_TEMP 1 (* v435 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 2 (* v436 *)) (Word 8 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 8 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 1 (* v435 *))) (Var (V_TEMP 2 (* v436 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 1 (* v435 *))) (Var (V_TEMP 2 (* v436 *)))) (BinOp OP_XOR (Var (V_TEMP 1 (* v435 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 1 (* v435 *)))) (Var (V_TEMP 2 (* v436 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 3 (* v437 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 3 (* v437 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v437 *))) (Word 2 32)) (Var (V_TEMP 3 (* v437 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3 (* v437 *))) (Word 1 32)) (Var (V_TEMP 3 (* v437 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80482ac: calll 0x8f *)
| 134513324 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513329 32) LittleE 4) $;
    Jmp (Word 134513472 32)
  )

(* 0x80482b1: addl $0x1d4f, %ebx *)
| 134513329 => Some (6, 
    Move (V_TEMP 4 (* v525 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move (V_TEMP 5 (* v526 *)) (Word 7503 32) $;
    Move R_EBX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 5 (* v526 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 4 (* v525 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v525 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 5 (* v526 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 4 (* v525 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 4 (* v525 *)))) (Var (V_TEMP 5 (* v526 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 6 (* v527 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 6 (* v527 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v527 *))) (Word 2 32)) (Var (V_TEMP 6 (* v527 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 6 (* v527 *))) (Word 1 32)) (Var (V_TEMP 6 (* v527 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0x80482b7: movl -0x4(%ebx), %eax *)
| 134513335 => Some (6,
    Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EBX) (Word 4294967292 32)) LittleE 4)
  )

(* 0x80482bd: testl %eax, %eax *)
| 134513341 => Some (2, 
    Move (V_TEMP 7 (* v531 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 8 (* v532 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 7 (* v531 *))) (Word 4 32)) (Var (V_TEMP 7 (* v531 *)))) (Let (V_TEMP 8 (* v532 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v532 *))) (Word 2 32)) (Var (V_TEMP 8 (* v532 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 8 (* v532 *))) (Word 1 32)) (Var (V_TEMP 8 (* v532 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 7 (* v531 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 7 (* v531 *))))
  )

(* 0x80482bf: je 0x5 *)
| 134513343 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 134513350 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x80482c1: calll 0x3a *)
| 134513345 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513350 32) LittleE 4) $;
    Jmp (Word 134513408 32)
  )

(* 0x80482c6: addl $0x8, %esp *)
| 134513350 => Some (3, 
    Move (V_TEMP 9 (* v571 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 10 (* v572 *)) (Word 8 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 10 (* v572 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 9 (* v571 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 9 (* v571 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 10 (* v572 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 9 (* v571 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 9 (* v571 *)))) (Var (V_TEMP 10 (* v572 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 11 (* v573 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 11 (* v573 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v573 *))) (Word 2 32)) (Var (V_TEMP 11 (* v573 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 11 (* v573 *))) (Word 1 32)) (Var (V_TEMP 11 (* v573 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80482c9: popl %ebx *)
| 134513353 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x80482ca: retl *)
| 134513354 => Some (1, 
    Move (V_TEMP 12 (* v577 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 12 (* v577 *)))
  )

(* 0x80482e0: jmpl *0x804a00c *)
| 134513376 => Some (6,
    Jmp (Load (Var V_MEM32) (Word 134520844 32) LittleE 4)
  )

(* 0x80482f0: jmpl *0x804a010 *)
| 134513392 => Some (6,
    Jmp (Load (Var V_MEM32) (Word 134520848 32) LittleE 4)
  )

(* 0x8048300: jmpl *0x8049ffc *)
| 134513408 => Some (6,
    Jmp (Load (Var V_MEM32) (Word 134520828 32) LittleE 4)
  )

(* 0x8048310: xorl %ebp, %ebp *)
| 134513424 => Some (2, 
    Move R_EBP (Word 0 32) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0x8048312: popl %esi *)
| 134513426 => Some (1, 
    Move R_ESI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x8048313: movl %esp, %ecx *)
| 134513427 => Some (2,
    Move R_ECX (Var R_ESP)
  )

(* 0x8048315: andl $-0x10, %esp *)
| 134513429 => Some (3, 
    Move R_ESP (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ESP)) (Word 4294967280 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 13 (* v375 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 13 (* v375 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v375 *))) (Word 2 32)) (Var (V_TEMP 13 (* v375 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 13 (* v375 *))) (Word 1 32)) (Var (V_TEMP 13 (* v375 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048318: pushl %eax *)
| 134513432 => Some (1, 
    Move (V_TEMP 14 (* v377 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 14 (* v377 *))) LittleE 4)
  )

(* 0x8048319: pushl %esp *)
| 134513433 => Some (1, 
    Move (V_TEMP 15 (* v379 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 15 (* v379 *))) LittleE 4)
  )

(* 0x804831a: pushl %edx *)
| 134513434 => Some (1, 
    Move (V_TEMP 16 (* v381 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 16 (* v381 *))) LittleE 4)
  )

(* 0x804831b: pushl $0x80484a0 *)
| 134513435 => Some (5, 
    Move (V_TEMP 17 (* v383 *)) (Word 134513824 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 17 (* v383 *))) LittleE 4)
  )

(* 0x8048320: pushl $0x8048440 *)
| 134513440 => Some (5, 
    Move (V_TEMP 18 (* v385 *)) (Word 134513728 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 18 (* v385 *))) LittleE 4)
  )

(* 0x8048325: pushl %ecx *)
| 134513445 => Some (1, 
    Move (V_TEMP 19 (* v387 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 19 (* v387 *))) LittleE 4)
  )

(* 0x8048326: pushl %esi *)
| 134513446 => Some (1, 
    Move (V_TEMP 20 (* v389 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 20 (* v389 *))) LittleE 4)
  )

(* 0x8048327: pushl $0x804840b *)
| 134513447 => Some (5, 
    Move (V_TEMP 21 (* v391 *)) (Word 134513675 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 21 (* v391 *))) LittleE 4)
  )

(* 0x804832c: calll -0x41 *)
| 134513452 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513457 32) LittleE 4) $;
    Jmp (Word 134513392 32)
  )

(* 0x8048331: hlt *)
| 134513457 => Some (1,
    Nop
  )

(* 0x8048332: nop *)
| 134513458 => Some (2,
    Nop
  )

(* 0x8048334: nop *)
| 134513460 => Some (2,
    Nop
  )

(* 0x8048336: nop *)
| 134513462 => Some (2,
    Nop
  )

(* 0x8048338: nop *)
| 134513464 => Some (2,
    Nop
  )

(* 0x804833a: nop *)
| 134513466 => Some (2,
    Nop
  )

(* 0x804833c: nop *)
| 134513468 => Some (2,
    Nop
  )

(* 0x804833e: nop *)
| 134513470 => Some (2,
    Nop
  )

(* 0x8048340: movl (%esp), %ebx *)
| 134513472 => Some (3,
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4)
  )

(* 0x8048343: retl *)
| 134513475 => Some (1, 
    Move (V_TEMP 22 (* v409 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 22 (* v409 *)))
  )

(* 0x8048368: pushl %ebp *)
| 134513512 => Some (1, 
    Move (V_TEMP 23 (* v441 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 23 (* v441 *))) LittleE 4)
  )

(* 0x8048369: movl %esp, %ebp *)
| 134513513 => Some (2,
    Move R_EBP (Var R_ESP)
  )

(* 0x804836b: subl $0x14, %esp *)
| 134513515 => Some (3, 
    Move (V_TEMP 24 (* v443 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 25 (* v444 *)) (Word 20 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 20 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 24 (* v443 *))) (Var (V_TEMP 25 (* v444 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 24 (* v443 *))) (Var (V_TEMP 25 (* v444 *)))) (BinOp OP_XOR (Var (V_TEMP 24 (* v443 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 24 (* v443 *)))) (Var (V_TEMP 25 (* v444 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 26 (* v445 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 26 (* v445 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v445 *))) (Word 2 32)) (Var (V_TEMP 26 (* v445 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 26 (* v445 *))) (Word 1 32)) (Var (V_TEMP 26 (* v445 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x804836e: pushl $0x804a01c *)
| 134513518 => Some (5, 
    Move (V_TEMP 27 (* v449 *)) (Word 134520860 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 27 (* v449 *))) LittleE 4)
  )

(* 0x8048373: calll *%eax *)
| 134513523 => Some (2, 
    Move (V_TEMP 28 (* v451 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513525 32) LittleE 4) $;
    Jmp (Var (V_TEMP 28 (* v451 *)))
  )

(* 0x8048375: addl $0x10, %esp *)
| 134513525 => Some (3, 
    Move (V_TEMP 29 (* v605 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 30 (* v606 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 30 (* v606 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 29 (* v605 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 29 (* v605 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 30 (* v606 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 29 (* v605 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 29 (* v605 *)))) (Var (V_TEMP 30 (* v606 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 31 (* v607 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 31 (* v607 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v607 *))) (Word 2 32)) (Var (V_TEMP 31 (* v607 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 31 (* v607 *))) (Word 1 32)) (Var (V_TEMP 31 (* v607 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048378: leave *)
| 134513528 => Some (1, 
    Move R_ESP (Var R_EBP) $;
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x8048379: retl *)
| 134513529 => Some (2, 
    Move (V_TEMP 32 (* v611 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 32 (* v611 *)))
  )

(* 0x8048380: movl $0x804a01c, %eax *)
| 134513536 => Some (5,
    Move R_EAX (Word 134520860 32)
  )

(* 0x8048385: subl $0x804a01c, %eax *)
| 134513541 => Some (5, 
    Move (V_TEMP 33 (* v453 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 34 (* v454 *)) (Word 134520860 32) $;
    Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 134520860 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 33 (* v453 *))) (Var (V_TEMP 34 (* v454 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 33 (* v453 *))) (Var (V_TEMP 34 (* v454 *)))) (BinOp OP_XOR (Var (V_TEMP 33 (* v453 *))) (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 33 (* v453 *)))) (Var (V_TEMP 34 (* v454 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 35 (* v455 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 35 (* v455 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v455 *))) (Word 2 32)) (Var (V_TEMP 35 (* v455 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 35 (* v455 *))) (Word 1 32)) (Var (V_TEMP 35 (* v455 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x804838a: sarl $0x2, %eax *)
| 134513546 => Some (3, 
    Move (V_TEMP 36 (* tmp459 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_ARSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 2 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 36 (* tmp459 *))) (Word 32 32)) (BinOp OP_AND (Word 2 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 37 (* v460 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 37 (* v460 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 37 (* v460 *))) (Word 2 32)) (Var (V_TEMP 37 (* v460 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 37 (* v460 *))) (Word 1 32)) (Var (V_TEMP 37 (* v460 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x804838d: movl %eax, %edx *)
| 134513549 => Some (2,
    Move R_EDX (Var R_EAX)
  )

(* 0x804838f: shrl $0x1f, %edx *)
| 134513551 => Some (3, 
    Move (V_TEMP 38 (* tmp463 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EDX (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 31 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 38 (* tmp463 *))) (Word 32 32)) (BinOp OP_AND (Word 31 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 39 (* v464 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDX))) (Let (V_TEMP 39 (* v464 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v464 *))) (Word 2 32)) (Var (V_TEMP 39 (* v464 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 39 (* v464 *))) (Word 1 32)) (Var (V_TEMP 39 (* v464 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x8048392: addl %edx, %eax *)
| 134513554 => Some (2, 
    Move (V_TEMP 40 (* v467 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move (V_TEMP 41 (* v468 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_EAX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 41 (* v468 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 40 (* v467 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 40 (* v467 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 41 (* v468 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 40 (* v467 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 40 (* v467 *)))) (Var (V_TEMP 41 (* v468 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 42 (* v469 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 42 (* v469 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 42 (* v469 *))) (Word 2 32)) (Var (V_TEMP 42 (* v469 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 42 (* v469 *))) (Word 1 32)) (Var (V_TEMP 42 (* v469 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x8048394: sarl %eax *)
| 134513556 => Some (2, 
    Move (V_TEMP 43 (* tmp473 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_EAX (BinOp OP_ARSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 1 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 43 (* tmp473 *))) (Word 32 32)) (BinOp OP_AND (Word 1 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 44 (* v474 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 44 (* v474 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 44 (* v474 *))) (Word 2 32)) (Var (V_TEMP 44 (* v474 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 44 (* v474 *))) (Word 1 32)) (Var (V_TEMP 44 (* v474 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Word 0 1)
  )

(* 0x8048396: je 0x1b *)
| 134513558 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 134513587 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x8048398: movl $0x0, %edx *)
| 134513560 => Some (5,
    Move R_EDX (Word 0 32)
  )

(* 0x804839d: testl %edx, %edx *)
| 134513565 => Some (2, 
    Move (V_TEMP 45 (* v479 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 46 (* v480 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 45 (* v479 *))) (Word 4 32)) (Var (V_TEMP 45 (* v479 *)))) (Let (V_TEMP 46 (* v480 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 46 (* v480 *))) (Word 2 32)) (Var (V_TEMP 46 (* v480 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 46 (* v480 *))) (Word 1 32)) (Var (V_TEMP 46 (* v480 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 45 (* v479 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 45 (* v479 *))))
  )

(* 0x804839f: je 0x12 *)
| 134513567 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 134513587 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x80483a1: pushl %ebp *)
| 134513569 => Some (1, 
    Move (V_TEMP 47 (* v535 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 47 (* v535 *))) LittleE 4)
  )

(* 0x80483a2: movl %esp, %ebp *)
| 134513570 => Some (2,
    Move R_EBP (Var R_ESP)
  )

(* 0x80483a4: subl $0x10, %esp *)
| 134513572 => Some (3, 
    Move (V_TEMP 48 (* v491 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 49 (* v492 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 16 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 48 (* v491 *))) (Var (V_TEMP 49 (* v492 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 48 (* v491 *))) (Var (V_TEMP 49 (* v492 *)))) (BinOp OP_XOR (Var (V_TEMP 48 (* v491 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 48 (* v491 *)))) (Var (V_TEMP 49 (* v492 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 50 (* v493 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 50 (* v493 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 50 (* v493 *))) (Word 2 32)) (Var (V_TEMP 50 (* v493 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 50 (* v493 *))) (Word 1 32)) (Var (V_TEMP 50 (* v493 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80483a7: pushl %eax *)
| 134513575 => Some (1, 
    Move (V_TEMP 51 (* v497 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 51 (* v497 *))) LittleE 4)
  )

(* 0x80483a8: pushl $0x804a01c *)
| 134513576 => Some (5, 
    Move (V_TEMP 52 (* v499 *)) (Word 134520860 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 52 (* v499 *))) LittleE 4)
  )

(* 0x80483ad: calll *%edx *)
| 134513581 => Some (2, 
    Move (V_TEMP 53 (* v501 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513583 32) LittleE 4) $;
    Jmp (Var (V_TEMP 53 (* v501 *)))
  )

(* 0x80483af: addl $0x10, %esp *)
| 134513583 => Some (3, 
    Move (V_TEMP 54 (* v579 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 55 (* v580 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 55 (* v580 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 54 (* v579 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 54 (* v579 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 55 (* v580 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 54 (* v579 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 54 (* v579 *)))) (Var (V_TEMP 55 (* v580 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 56 (* v581 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 56 (* v581 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 56 (* v581 *))) (Word 2 32)) (Var (V_TEMP 56 (* v581 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 56 (* v581 *))) (Word 1 32)) (Var (V_TEMP 56 (* v581 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80483b2: leave *)
| 134513586 => Some (1, 
    Move R_ESP (Var R_EBP) $;
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x80483b3: retl *)
| 134513587 => Some (2, 
    Move (V_TEMP 57 (* v407 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 57 (* v407 *)))
  )

(* 0x80483f9: pushl %ebp *)
| 134513657 => Some (1, 
    Move (V_TEMP 58 (* v593 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 58 (* v593 *))) LittleE 4)
  )

(* 0x80483fa: movl %esp, %ebp *)
| 134513658 => Some (2,
    Move R_EBP (Var R_ESP)
  )

(* 0x80483fc: subl $0x14, %esp *)
| 134513660 => Some (3, 
    Move (V_TEMP 59 (* v595 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 60 (* v596 *)) (Word 20 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 20 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 59 (* v595 *))) (Var (V_TEMP 60 (* v596 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 59 (* v595 *))) (Var (V_TEMP 60 (* v596 *)))) (BinOp OP_XOR (Var (V_TEMP 59 (* v595 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 59 (* v595 *)))) (Var (V_TEMP 60 (* v596 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 61 (* v597 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 61 (* v597 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 61 (* v597 *))) (Word 2 32)) (Var (V_TEMP 61 (* v597 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 61 (* v597 *))) (Word 1 32)) (Var (V_TEMP 61 (* v597 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80483ff: pushl %eax *)
| 134513663 => Some (1, 
    Move (V_TEMP 62 (* v601 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 62 (* v601 *))) LittleE 4)
  )

(* 0x8048400: calll *%edx *)
| 134513664 => Some (2, 
    Move (V_TEMP 63 (* v603 *)) (Cast CAST_LOW 32 (Var R_EDX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513666 32) LittleE 4) $;
    Jmp (Var (V_TEMP 63 (* v603 *)))
  )

(* 0x8048402: addl $0x10, %esp *)
| 134513666 => Some (3, 
    Move (V_TEMP 64 (* v427 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 65 (* v428 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 65 (* v428 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 64 (* v427 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 64 (* v427 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 65 (* v428 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 64 (* v427 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 64 (* v427 *)))) (Var (V_TEMP 65 (* v428 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 66 (* v429 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 66 (* v429 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 66 (* v429 *))) (Word 2 32)) (Var (V_TEMP 66 (* v429 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 66 (* v429 *))) (Word 1 32)) (Var (V_TEMP 66 (* v429 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048405: leave *)
| 134513669 => Some (1, 
    Move R_ESP (Var R_EBP) $;
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x8048406: jmp -0x8b *)
| 134513670 => Some (5,
    Jmp (Word 134513536 32)
  )

(* 0x804840b: leal 0x4(%esp), %ecx *)
| 134513675 => Some (4,
    Move R_ECX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)))
  )

(* 0x804840f: andl $-0x10, %esp *)
| 134513679 => Some (3, 
    Move R_ESP (BinOp OP_AND (Cast CAST_LOW 32 (Var R_ESP)) (Word 4294967280 32)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 67 (* v503 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 67 (* v503 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 67 (* v503 *))) (Word 2 32)) (Var (V_TEMP 67 (* v503 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 67 (* v503 *))) (Word 1 32)) (Var (V_TEMP 67 (* v503 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048412: pushl -0x4(%ecx) *)
| 134513682 => Some (3, 
    Move (V_TEMP 68 (* v505 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_ECX))) (Word 4294967292 32)) LittleE 4) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 68 (* v505 *))) LittleE 4)
  )

(* 0x8048415: pushl %ebp *)
| 134513685 => Some (1, 
    Move (V_TEMP 69 (* v507 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 69 (* v507 *))) LittleE 4)
  )

(* 0x8048416: movl %esp, %ebp *)
| 134513686 => Some (2,
    Move R_EBP (Var R_ESP)
  )

(* 0x8048418: pushl %ecx *)
| 134513688 => Some (1, 
    Move (V_TEMP 70 (* v509 *)) (Cast CAST_LOW 32 (Var R_ECX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 70 (* v509 *))) LittleE 4)
  )

(* 0x8048419: subl $0x4, %esp *)
| 134513689 => Some (3, 
    Move (V_TEMP 71 (* v511 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 72 (* v512 *)) (Word 4 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 71 (* v511 *))) (Var (V_TEMP 72 (* v512 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 71 (* v511 *))) (Var (V_TEMP 72 (* v512 *)))) (BinOp OP_XOR (Var (V_TEMP 71 (* v511 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 71 (* v511 *)))) (Var (V_TEMP 72 (* v512 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 73 (* v513 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 73 (* v513 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 73 (* v513 *))) (Word 2 32)) (Var (V_TEMP 73 (* v513 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 73 (* v513 *))) (Word 1 32)) (Var (V_TEMP 73 (* v513 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x804841c: subl $0xc, %esp *)
| 134513692 => Some (3, 
    Move (V_TEMP 74 (* v517 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 75 (* v518 *)) (Word 12 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 12 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 74 (* v517 *))) (Var (V_TEMP 75 (* v518 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 74 (* v517 *))) (Var (V_TEMP 75 (* v518 *)))) (BinOp OP_XOR (Var (V_TEMP 74 (* v517 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 74 (* v517 *)))) (Var (V_TEMP 75 (* v518 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 76 (* v519 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 76 (* v519 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 76 (* v519 *))) (Word 2 32)) (Var (V_TEMP 76 (* v519 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 76 (* v519 *))) (Word 1 32)) (Var (V_TEMP 76 (* v519 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x804841f: pushl $0x80484c0 *)
| 134513695 => Some (5, 
    Move (V_TEMP 77 (* v523 *)) (Word 134513856 32) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 77 (* v523 *))) LittleE 4)
  )

(* 0x8048424: calll -0x149 *)
| 134513700 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513705 32) LittleE 4) $;
    Jmp (Word 134513376 32)
  )

(* 0x8048429: addl $0x10, %esp *)
| 134513705 => Some (3, 
    Move (V_TEMP 78 (* v367 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 79 (* v368 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 79 (* v368 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 78 (* v367 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 78 (* v367 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 79 (* v368 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 78 (* v367 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 78 (* v367 *)))) (Var (V_TEMP 79 (* v368 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 80 (* v369 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 80 (* v369 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 80 (* v369 *))) (Word 2 32)) (Var (V_TEMP 80 (* v369 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 80 (* v369 *))) (Word 1 32)) (Var (V_TEMP 80 (* v369 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x804842c: movl $0x0, %eax *)
| 134513708 => Some (5,
    Move R_EAX (Word 0 32)
  )

(* 0x8048431: movl -0x4(%ebp), %ecx *)
| 134513713 => Some (3,
    Move R_ECX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_EBP) (Word 4294967292 32)) LittleE 4)
  )

(* 0x8048434: leave *)
| 134513716 => Some (1, 
    Move R_ESP (Var R_EBP) $;
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x8048435: leal -0x4(%ecx), %esp *)
| 134513717 => Some (3,
    Move R_ESP (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_ECX))) (Word 4294967292 32)))
  )

(* 0x8048438: retl *)
| 134513720 => Some (1, 
    Move (V_TEMP 81 (* v373 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 81 (* v373 *)))
  )

(* 0x8048440: pushl %ebp *)
| 134513728 => Some (1, 
    Move (V_TEMP 82 (* v483 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 82 (* v483 *))) LittleE 4)
  )

(* 0x8048441: pushl %edi *)
| 134513729 => Some (1, 
    Move (V_TEMP 83 (* v485 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 83 (* v485 *))) LittleE 4)
  )

(* 0x8048442: pushl %esi *)
| 134513730 => Some (1, 
    Move (V_TEMP 84 (* v487 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 84 (* v487 *))) LittleE 4)
  )

(* 0x8048443: pushl %ebx *)
| 134513731 => Some (1, 
    Move (V_TEMP 85 (* v489 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 85 (* v489 *))) LittleE 4)
  )

(* 0x8048444: calll -0x109 *)
| 134513732 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513737 32) LittleE 4) $;
    Jmp (Word 134513472 32)
  )

(* 0x8048449: addl $0x1bb7, %ebx *)
| 134513737 => Some (6, 
    Move (V_TEMP 86 (* v537 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move (V_TEMP 87 (* v538 *)) (Word 7095 32) $;
    Move R_EBX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 87 (* v538 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 86 (* v537 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 86 (* v537 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 87 (* v538 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 86 (* v537 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 86 (* v537 *)))) (Var (V_TEMP 87 (* v538 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 88 (* v539 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 88 (* v539 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 88 (* v539 *))) (Word 2 32)) (Var (V_TEMP 88 (* v539 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 88 (* v539 *))) (Word 1 32)) (Var (V_TEMP 88 (* v539 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0x804844f: subl $0xc, %esp *)
| 134513743 => Some (3, 
    Move (V_TEMP 89 (* v543 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 90 (* v544 *)) (Word 12 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 12 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 89 (* v543 *))) (Var (V_TEMP 90 (* v544 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 89 (* v543 *))) (Var (V_TEMP 90 (* v544 *)))) (BinOp OP_XOR (Var (V_TEMP 89 (* v543 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 89 (* v543 *)))) (Var (V_TEMP 90 (* v544 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 91 (* v545 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 91 (* v545 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 91 (* v545 *))) (Word 2 32)) (Var (V_TEMP 91 (* v545 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 91 (* v545 *))) (Word 1 32)) (Var (V_TEMP 91 (* v545 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048452: movl 0x20(%esp), %ebp *)
| 134513746 => Some (4,
    Move R_EBP (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 32 32)) LittleE 4)
  )

(* 0x8048456: leal -0xf4(%ebx), %esi *)
| 134513750 => Some (6,
    Move R_ESI (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EBX))) (Word 4294967052 32)))
  )

(* 0x804845c: calll -0x1b9 *)
| 134513756 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513761 32) LittleE 4) $;
    Jmp (Word 134513320 32)
  )

(* 0x8048461: leal -0xf8(%ebx), %eax *)
| 134513761 => Some (6,
    Move R_EAX (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_EBX))) (Word 4294967048 32)))
  )

(* 0x8048467: subl %eax, %esi *)
| 134513767 => Some (2, 
    Move (V_TEMP 92 (* v549 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move (V_TEMP 93 (* v550 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
    Move R_ESI (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESI)) (Cast CAST_LOW 32 (Var R_EAX))) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 92 (* v549 *))) (Var (V_TEMP 93 (* v550 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 92 (* v549 *))) (Var (V_TEMP 93 (* v550 *)))) (BinOp OP_XOR (Var (V_TEMP 92 (* v549 *))) (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESI)) (Var (V_TEMP 92 (* v549 *)))) (Var (V_TEMP 93 (* v550 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 94 (* v551 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 94 (* v551 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 94 (* v551 *))) (Word 2 32)) (Var (V_TEMP 94 (* v551 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 94 (* v551 *))) (Word 1 32)) (Var (V_TEMP 94 (* v551 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI)))
  )

(* 0x8048469: sarl $0x2, %esi *)
| 134513769 => Some (3, 
    Move (V_TEMP 95 (* tmp555 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_ESI (BinOp OP_ARSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 2 32)) $;
    Move R_CF (Cast CAST_HIGH 1 (BinOp OP_MINUS (BinOp OP_LSHIFT (Var (V_TEMP 95 (* tmp555 *))) (Word 32 32)) (BinOp OP_AND (Word 2 32) (BinOp OP_MINUS (Word 32 32) (Word 1 32))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 96 (* v556 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESI))) (Let (V_TEMP 96 (* v556 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 96 (* v556 *))) (Word 2 32)) (Var (V_TEMP 96 (* v556 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 96 (* v556 *))) (Word 1 32)) (Var (V_TEMP 96 (* v556 *)))))))) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_OF (Unknown (NumT 1))
  )

(* 0x804846c: testl %esi, %esi *)
| 134513772 => Some (2, 
    Move (V_TEMP 97 (* v559 *)) (Cast CAST_LOW 32 (Var R_ESI)) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 98 (* v560 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 97 (* v559 *))) (Word 4 32)) (Var (V_TEMP 97 (* v559 *)))) (Let (V_TEMP 98 (* v560 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 98 (* v560 *))) (Word 2 32)) (Var (V_TEMP 98 (* v560 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 98 (* v560 *))) (Word 1 32)) (Var (V_TEMP 98 (* v560 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 97 (* v559 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 97 (* v559 *))))
  )

(* 0x804846e: je 0x25 *)
| 134513774 => Some (2,
    If (Var R_ZF) (
      Jmp (Word 134513813 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x8048470: xorl %edi, %edi *)
| 134513776 => Some (2, 
    Move R_EDI (Word 0 32) $;
    Move R_AF (Unknown (NumT 1)) $;
    Move R_ZF (Word 1 1) $;
    Move R_PF (Word 1 1) $;
    Move R_OF (Word 0 1) $;
    Move R_CF (Word 0 1) $;
    Move R_SF (Word 0 1)
  )

(* 0x8048472: leal (%esi), %esi *)
| 134513778 => Some (6,
    Move R_ESI (Cast CAST_LOW 32 (BinOp OP_PLUS (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 32 (Var R_ESI))) (Word 0 32)))
  )

(* 0x8048478: subl $0x4, %esp *)
| 134513784 => Some (3, 
    Move (V_TEMP 99 (* v393 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 100 (* v394 *)) (Word 4 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 99 (* v393 *))) (Var (V_TEMP 100 (* v394 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 99 (* v393 *))) (Var (V_TEMP 100 (* v394 *)))) (BinOp OP_XOR (Var (V_TEMP 99 (* v393 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 99 (* v393 *)))) (Var (V_TEMP 100 (* v394 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 101 (* v395 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 101 (* v395 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 101 (* v395 *))) (Word 2 32)) (Var (V_TEMP 101 (* v395 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 101 (* v395 *))) (Word 1 32)) (Var (V_TEMP 101 (* v395 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x804847b: pushl 0x2c(%esp) *)
| 134513787 => Some (4, 
    Move (V_TEMP 102 (* v399 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 44 32)) LittleE 4) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 102 (* v399 *))) LittleE 4)
  )

(* 0x804847f: pushl 0x2c(%esp) *)
| 134513791 => Some (4, 
    Move (V_TEMP 103 (* v401 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 44 32)) LittleE 4) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 103 (* v401 *))) LittleE 4)
  )

(* 0x8048483: pushl %ebp *)
| 134513795 => Some (1, 
    Move (V_TEMP 104 (* v403 *)) (Cast CAST_LOW 32 (Var R_EBP)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 104 (* v403 *))) LittleE 4)
  )

(* 0x8048484: calll *-0xf8(%ebx,%edi,4) *)
| 134513796 => Some (7, 
    Move (V_TEMP 105 (* v405 *)) (Load (Var V_MEM32) (BinOp OP_PLUS (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (BinOp OP_LSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 2 32))) (Word 4294967048 32)) LittleE 4) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513803 32) LittleE 4) $;
    Jmp (Var (V_TEMP 105 (* v405 *)))
  )

(* 0x804848b: addl $0x1, %edi *)
| 134513803 => Some (3, 
    Move (V_TEMP 106 (* v411 *)) (Cast CAST_LOW 32 (Var R_EDI)) $;
    Move (V_TEMP 107 (* v412 *)) (Word 1 32) $;
    Move R_EDI (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 107 (* v412 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 106 (* v411 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 106 (* v411 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 107 (* v412 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 106 (* v411 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 106 (* v411 *)))) (Var (V_TEMP 107 (* v412 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 108 (* v413 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EDI)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EDI))) (Let (V_TEMP 108 (* v413 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 108 (* v413 *))) (Word 2 32)) (Var (V_TEMP 108 (* v413 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 108 (* v413 *))) (Word 1 32)) (Var (V_TEMP 108 (* v413 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EDI))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EDI)))
  )

(* 0x804848e: addl $0x10, %esp *)
| 134513806 => Some (3, 
    Move (V_TEMP 109 (* v417 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 110 (* v418 *)) (Word 16 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 110 (* v418 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 109 (* v417 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 109 (* v417 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 110 (* v418 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 109 (* v417 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 109 (* v417 *)))) (Var (V_TEMP 110 (* v418 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 111 (* v419 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 111 (* v419 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 111 (* v419 *))) (Word 2 32)) (Var (V_TEMP 111 (* v419 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 111 (* v419 *))) (Word 1 32)) (Var (V_TEMP 111 (* v419 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048491: cmpl %esi, %edi *)
| 134513809 => Some (2, 
    Move (V_TEMP 112 (* v423 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EDI)) (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EDI)) (Cast CAST_LOW 32 (Var R_ESI))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Cast CAST_LOW 32 (Var R_ESI))) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EDI)) (Var (V_TEMP 112 (* v423 *)))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 112 (* v423 *))) (Cast CAST_LOW 32 (Var R_EDI))) (Cast CAST_LOW 32 (Var R_ESI))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 113 (* v424 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 112 (* v423 *))) (Word 4 32)) (Var (V_TEMP 112 (* v423 *)))) (Let (V_TEMP 113 (* v424 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 113 (* v424 *))) (Word 2 32)) (Var (V_TEMP 113 (* v424 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 113 (* v424 *))) (Word 1 32)) (Var (V_TEMP 113 (* v424 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 112 (* v423 *)))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 112 (* v423 *))))
  )

(* 0x8048493: jne -0x1d *)
| 134513811 => Some (2,
    If (UnOp OP_NOT (Var R_ZF)) (
      Jmp (Word 134513784 32)
    ) (* else *) (
      Nop
    )
  )

(* 0x8048495: addl $0xc, %esp *)
| 134513813 => Some (3, 
    Move (V_TEMP 114 (* v585 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 115 (* v586 *)) (Word 12 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 115 (* v586 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 114 (* v585 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 114 (* v585 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 115 (* v586 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 114 (* v585 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 114 (* v585 *)))) (Var (V_TEMP 115 (* v586 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 116 (* v587 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 116 (* v587 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 116 (* v587 *))) (Word 2 32)) (Var (V_TEMP 116 (* v587 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 116 (* v587 *))) (Word 1 32)) (Var (V_TEMP 116 (* v587 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x8048498: popl %ebx *)
| 134513816 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x8048499: popl %esi *)
| 134513817 => Some (1, 
    Move R_ESI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x804849a: popl %edi *)
| 134513818 => Some (1, 
    Move R_EDI (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x804849b: popl %ebp *)
| 134513819 => Some (1, 
    Move R_EBP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x804849c: retl *)
| 134513820 => Some (1, 
    Move (V_TEMP 117 (* v591 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 117 (* v591 *)))
  )

(* 0x80484a0: retl *)
| 134513824 => Some (2, 
    Move (V_TEMP 118 (* v477 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 118 (* v477 *)))
  )

(* 0x80484a4: pushl %ebx *)
| 134513828 => Some (1, 
    Move (V_TEMP 119 (* v563 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Var (V_TEMP 119 (* v563 *))) LittleE 4)
  )

(* 0x80484a5: subl $0x8, %esp *)
| 134513829 => Some (3, 
    Move (V_TEMP 120 (* v565 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 121 (* v566 *)) (Word 8 32) $;
    Move R_ESP (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_ESP)) (Word 8 32)) $;
    Move R_CF (BinOp OP_LT (Var (V_TEMP 120 (* v565 *))) (Var (V_TEMP 121 (* v566 *)))) $;
    Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 120 (* v565 *))) (Var (V_TEMP 121 (* v566 *)))) (BinOp OP_XOR (Var (V_TEMP 120 (* v565 *))) (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 120 (* v565 *)))) (Var (V_TEMP 121 (* v566 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 122 (* v567 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 122 (* v567 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 122 (* v567 *))) (Word 2 32)) (Var (V_TEMP 122 (* v567 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 122 (* v567 *))) (Word 1 32)) (Var (V_TEMP 122 (* v567 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80484a8: calll -0x16d *)
| 134513832 => Some (5, 
    Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 4 32)) $;
    Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Word 134513837 32) LittleE 4) $;
    Jmp (Word 134513472 32)
  )

(* 0x80484ad: addl $0x1b53, %ebx *)
| 134513837 => Some (6, 
    Move (V_TEMP 123 (* v613 *)) (Cast CAST_LOW 32 (Var R_EBX)) $;
    Move (V_TEMP 124 (* v614 *)) (Word 6995 32) $;
    Move R_EBX (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 124 (* v614 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 123 (* v613 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 123 (* v613 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 124 (* v614 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 123 (* v613 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EBX)) (Var (V_TEMP 123 (* v613 *)))) (Var (V_TEMP 124 (* v614 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 125 (* v615 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EBX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EBX))) (Let (V_TEMP 125 (* v615 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 125 (* v615 *))) (Word 2 32)) (Var (V_TEMP 125 (* v615 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 125 (* v615 *))) (Word 1 32)) (Var (V_TEMP 125 (* v615 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EBX))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EBX)))
  )

(* 0x80484b3: addl $0x8, %esp *)
| 134513843 => Some (3, 
    Move (V_TEMP 126 (* v619 *)) (Cast CAST_LOW 32 (Var R_ESP)) $;
    Move (V_TEMP 127 (* v620 *)) (Word 8 32) $;
    Move R_ESP (BinOp OP_PLUS (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 127 (* v620 *)))) $;
    Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 126 (* v619 *)))) $;
    Move R_OF (BinOp OP_AND (BinOp OP_EQ (Cast CAST_HIGH 1 (Var (V_TEMP 126 (* v619 *)))) (Cast CAST_HIGH 1 (Var (V_TEMP 127 (* v620 *))))) (BinOp OP_XOR (Cast CAST_HIGH 1 (Var (V_TEMP 126 (* v619 *)))) (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))))) $;
    Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_ESP)) (Var (V_TEMP 126 (* v619 *)))) (Var (V_TEMP 127 (* v620 *)))))) $;
    Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 128 (* v621 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_ESP)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_ESP))) (Let (V_TEMP 128 (* v621 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 128 (* v621 *))) (Word 2 32)) (Var (V_TEMP 128 (* v621 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 128 (* v621 *))) (Word 1 32)) (Var (V_TEMP 128 (* v621 *)))))))) $;
    Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_ESP))) $;
    Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_ESP)))
  )

(* 0x80484b6: popl %ebx *)
| 134513846 => Some (1, 
    Move R_EBX (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32))
  )

(* 0x80484b7: retl *)
| 134513847 => Some (1, 
    Move (V_TEMP 129 (* v625 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
    Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
    Jmp (Var (V_TEMP 129 (* v625 *)))
  )

| _ => None
end.
