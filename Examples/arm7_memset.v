Require Import Picinae_armv7.
Require Import NArith.
Open Scope N.

Definition memset_arm : program := fun _ a => match a with

(* 0xc0000040: mov r3, r0 *)
| 0 => Some (4,
    Move R_R3 (Var R_R0)
  )

(* 0xc0000044: cmp r2, #8 *)
| 4 => Some (4, 
    Move (V_TEMP 0 (* v130 *)) (Var R_R2) $;
    Move (V_TEMP 1 (* v128 *)) (BinOp OP_MINUS (Var R_R2) (Word 8 32)) $;
    Move R_CF (BinOp OP_LE (Word 8 32) (Var (V_TEMP 0 (* v130 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 0 (* v130 *))) (Word 8 32)) (BinOp OP_XOR (Var (V_TEMP 0 (* v130 *))) (Var (V_TEMP 1 (* v128 *)))))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 1 (* v128 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 1 (* v128 *))) (Word 0 32))
  )

(* 0xc0000048: blo #0x44 *)
| 8 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 0 1)) (
      Jmp (Word 84 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000004c: tst r3, #3 *)
| 12 => Some (4, 
    Move (V_TEMP 2 (* v132 *)) (BinOp OP_AND (Var R_R3) (Word 3 32)) $;
    Move R_CF (Unknown 1) $;
    Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 2 (* v132 *)))) $;
    Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2 (* v132 *))) (Word 0 32))
  )

(* 0xc0000050: strbne r1, [r3], #1 *)
| 16 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) ( 
      Move (V_TEMP 3 (* v135 *)) (Cast CAST_LOW 8 (Var R_R1)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R3) (Var (V_TEMP 3 (* v135 *))) LittleE 1) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000054: subne r2, r2, #1 *)
| 20 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000058: bne #-0x14 *)
| 24 => Some (4,
    If (BinOp OP_EQ (Var R_ZF) (Word 0 1)) (
      Jmp (Word 12 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc000005c: and r1, r1, #255 *)
| 28 => Some (4,
    Move R_R1 (BinOp OP_AND (Var R_R1) (Word 255 32))
  )

(* 0xc0000060: orr r1, r1, r1, lsl #8 *)
| 32 => Some (4, 
    Move (V_TEMP 4 (* v140 *)) (Var R_R1) $;
    Move R_R1 (BinOp OP_OR (Var R_R1) (BinOp OP_LSHIFT (Var (V_TEMP 4 (* v140 *))) (Word 8 32)))
  )

(* 0xc0000064: orr r1, r1, r1, lsl #16 *)
| 36 => Some (4, 
    Move (V_TEMP 5 (* v141 *)) (Var R_R1) $;
    Move R_R1 (BinOp OP_OR (Var R_R1) (BinOp OP_LSHIFT (Var (V_TEMP 5 (* v141 *))) (Word 16 32)))
  )

(* 0xc0000068: mov r12, r1 *)
| 40 => Some (4,
    Move R_R12 (Var R_R1)
  )

(* 0xc000006c: subs r2, r2, #8 *)
| 44 => Some (4, 
    Move (V_TEMP 6 (* v144 *)) (Var R_R2) $;
    Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 8 32)) $;
    Move R_CF (BinOp OP_LE (Word 8 32) (Var (V_TEMP 6 (* v144 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 6 (* v144 *))) (Word 8 32)) (BinOp OP_XOR (Var (V_TEMP 6 (* v144 *))) (Var R_R2)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
  )

(* 0xc0000070: stmhs r3!, {r1, r12} *)
| 48 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 7 (* v146 *)) (Var R_R3) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 7 (* v146 *))) (Var R_R1) LittleE 4) $;
      Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 7 (* v146 *))) (Word 4 32)) (Var R_R12) LittleE 4) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 8 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000074: subshs r2, r2, #8 *)
| 52 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 8 (* v148 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 8 32)) $;
      Move R_CF (BinOp OP_LE (Word 8 32) (Var (V_TEMP 8 (* v148 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 8 (* v148 *))) (Word 8 32)) (BinOp OP_XOR (Var (V_TEMP 8 (* v148 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000078: stmhs r3!, {r1, r12} *)
| 56 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 9 (* v150 *)) (Var R_R3) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 9 (* v150 *))) (Var R_R1) LittleE 4) $;
      Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 9 (* v150 *))) (Word 4 32)) (Var R_R12) LittleE 4) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 8 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000007c: subshs r2, r2, #8 *)
| 60 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 10 (* v152 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 8 32)) $;
      Move R_CF (BinOp OP_LE (Word 8 32) (Var (V_TEMP 10 (* v152 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 10 (* v152 *))) (Word 8 32)) (BinOp OP_XOR (Var (V_TEMP 10 (* v152 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000080: stmhs r3!, {r1, r12} *)
| 64 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 11 (* v154 *)) (Var R_R3) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 11 (* v154 *))) (Var R_R1) LittleE 4) $;
      Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 11 (* v154 *))) (Word 4 32)) (Var R_R12) LittleE 4) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 8 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000084: subshs r2, r2, #8 *)
| 68 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 12 (* v156 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 8 32)) $;
      Move R_CF (BinOp OP_LE (Word 8 32) (Var (V_TEMP 12 (* v156 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 12 (* v156 *))) (Word 8 32)) (BinOp OP_XOR (Var (V_TEMP 12 (* v156 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000088: stmhs r3!, {r1, r12} *)
| 72 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 13 (* v158 *)) (Var R_R3) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 13 (* v158 *))) (Var R_R1) LittleE 4) $;
      Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var (V_TEMP 13 (* v158 *))) (Word 4 32)) (Var R_R12) LittleE 4) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 8 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000008c: bhs #-0x28 *)
| 76 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) (
      Jmp (Word 44 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc0000090: and r2, r2, #7 *)
| 80 => Some (4,
    Move R_R2 (BinOp OP_AND (Var R_R2) (Word 7 32))
  )

(* 0xc0000094: subs r2, r2, #1 *)
| 84 => Some (4, 
    Move (V_TEMP 14 (* v108 *)) (Var R_R2) $;
    Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 1 32)) $;
    Move R_CF (BinOp OP_LE (Word 1 32) (Var (V_TEMP 14 (* v108 *)))) $;
    Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 14 (* v108 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 14 (* v108 *))) (Var R_R2)))) $;
    Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
    Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
  )

(* 0xc0000098: strbhs r1, [r3], #1 *)
| 88 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 15 (* v111 *)) (Cast CAST_LOW 8 (Var R_R1)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R3) (Var (V_TEMP 15 (* v111 *))) LittleE 1) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc000009c: subshs r2, r2, #1 *)
| 92 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 16 (* v113 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 1 32)) $;
      Move R_CF (BinOp OP_LE (Word 1 32) (Var (V_TEMP 16 (* v113 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 16 (* v113 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 16 (* v113 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a0: strbhs r1, [r3], #1 *)
| 96 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 17 (* v116 *)) (Cast CAST_LOW 8 (Var R_R1)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R3) (Var (V_TEMP 17 (* v116 *))) LittleE 1) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a4: subshs r2, r2, #1 *)
| 100 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 18 (* v118 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 1 32)) $;
      Move R_CF (BinOp OP_LE (Word 1 32) (Var (V_TEMP 18 (* v118 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 18 (* v118 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 18 (* v118 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000a8: strbhs r1, [r3], #1 *)
| 104 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 19 (* v121 *)) (Cast CAST_LOW 8 (Var R_R1)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R3) (Var (V_TEMP 19 (* v121 *))) LittleE 1) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000ac: subshs r2, r2, #1 *)
| 108 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 20 (* v123 *)) (Var R_R2) $;
      Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 1 32)) $;
      Move R_CF (BinOp OP_LE (Word 1 32) (Var (V_TEMP 20 (* v123 *)))) $;
      Move R_VF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 20 (* v123 *))) (Word 1 32)) (BinOp OP_XOR (Var (V_TEMP 20 (* v123 *))) (Var R_R2)))) $;
      Move R_NF (Cast CAST_HIGH 1 (Var R_R2)) $;
      Move R_ZF (BinOp OP_EQ (Var R_R2) (Word 0 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b0: strbhs r1, [r3], #1 *)
| 112 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) ( 
      Move (V_TEMP 21 (* v126 *)) (Cast CAST_LOW 8 (Var R_R1)) $;
      Move V_MEM32 (Store (Var V_MEM32) (Var R_R3) (Var (V_TEMP 21 (* v126 *))) LittleE 1) $;
      Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 1 32))
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b4: bhs #-0x28 *)
| 116 => Some (4,
    If (BinOp OP_EQ (Var R_CF) (Word 1 1)) (
      Jmp (Word 84 32)
    ) (* else *) (
      Nop
    )
  )

(* 0xc00000b8: bx lr *)
| 120 => Some (4,
    Jmp (Var R_LR)
  )

| _ => None
end.

(*
HAND-DECOMPILED
-----------------
void* memset(void* dest, int value, size_t size) {
	char* r0 = ( char* )dest;
	int r1 = value;
	int r12 = 0;
	int r2 = size;
	char* r3 = r0;

	if (r2 >= 8) {
		// Aligns dest to byte boundary
		while ((int)r3 & 0b11) {
			r3[0] = value;
			r3++;
			r2--;
		}

		// Prepare value
		r1 &= 255;
		r1 |= r1 << 8;
		r1 |= r1 << 16;
		r12 = r1;

		// Repeatedly fill 8-byte blocks until size < 8
		do {
			r2 -= 8;
			if (! (r2 < 0)) {
				*(( int* )r3) = r1;
				*(( int* )(r3 + sizeof(int))) = r12;
				r3 += 2 * sizeof(int);
			}

			if (! (r2 < 0)) {
				r2 -= 8;
			}
			if (! (r2 < 0)) {
				*(( int* )r3) = r1;
				*(( int* )(r3 + sizeof(int))) = r12;
				r3 += 2 * sizeof(int);
			}

			if (! (r2 < 0)) {
				r2 -= 8;
			}
			if (! (r2 < 0)) {
				*(( int* )r3) = r1;
				*(( int* )(r3 + sizeof(int))) = r12;
				r3 += 2 * sizeof(int);
			}

			if (! (r2 < 0)) {
				r2 -= 8;
			}
			if (! (r2 < 0)) {
				*(( int* )r3) = r1;
				*(( int* )(r3 + sizeof(int))) = r12;
				r3 += 2 * sizeof(int);
			}
		} while (! (r2 < 0));
		
		// this does abs(size) if fallthrough from (size > 8) case
		r2 &= 7;
	} 
	
	// Repeatedly fill 1-byte blocks until size <= 0
	do {
		r2--;

		if (! (r2 < 0)) {
			*r3 = (char)r1;
			r3++;
			r2--;
		}

		if (! (r2 < 0)) {
			*r3 = (char)r1;
			r3++;
			r2--;
		}

		if (! (r2 < 0)) {
			*r3 = (char)r1;
			r3++;
			r2--;
		}

		if (! (r2 < 0)) {
			*r3 = (char)r1;
			r3++;
		}
	} while (! (r2 < 0));

	return r0;
}

*)
