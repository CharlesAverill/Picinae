Require Import Picinae_armv7.
From Stdlib Require Import NArith.
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


(* BEGIN BIGSTEPS GENERATED LEMMAS *)
(* Generated by: bigsteps Examples/arm7_memset.v --invariants 0 12 44 84 120 --exits 120 *)
Import ARM7Notations.

Lemma memset_arm_stepfrom_0:
  forall invs exits s t
    (VC1: forall t0, effinv false memset_arm invs exits ((Addr 0, s) :: t0) = None)
    (VC2: forall l, effinv true memset_arm invs exits ((Addr 4, s[R_R3 := s R_R0]) :: l) = None)
    (VC3: forall l, effinv true memset_arm invs exits ((Addr 8, s[R_R3 := s R_R0][R_CF := if 8 <=? s R_R2 then 1 else 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC4: forall l, ((8 <=? s R_R2) = true) -> nextinv memset_arm invs exits true ((Addr 12, s[R_R3 := s R_R0][R_CF := 1][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l))
    (VC5: forall l, ((8 <=? s R_R2) = false) -> nextinv memset_arm invs exits true ((Addr 84, s[R_R3 := s R_R0][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l))
  ,
  nextinv memset_arm invs exits false ((Addr 0, s)::t).
Proof.
  intros; find_vcs (0::12::44::84::120::nil).
  Unshelve.
  all: match goal with H: _ |- _ =>
      solve [eapply H; first [eassumption | reflexivity]]
  end.
Qed.

Lemma memset_arm_stepfrom_12:
  forall invs exits s t
    (VC1: forall t0, effinv false memset_arm invs exits ((Addr 12, s) :: t0) = None)
    (VC2: forall n, forall l, effinv true memset_arm invs exits ((Addr 16, s[R_CF := n mod 2][R_NF := 0][R_ZF := if s R_R3 mod 4 =? 0 then 1 else 0]) :: l) = None)
    (VC3: forall n, forall l, effinv true memset_arm invs exits ((Addr 20, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1]) :: l) = None)
    (VC4: forall n, forall l, effinv true memset_arm invs exits ((Addr 24, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1]) :: l) = None)
    (VC5: forall n, forall l, effinv true memset_arm invs exits ((Addr 28, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1]) :: l) = None)
    (VC6: forall n, forall l, effinv true memset_arm invs exits ((Addr 32, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1][R_R1 := s R_R1 mod 2 ^ 8]) :: l) = None)
    (VC7: forall n, forall l, effinv true memset_arm invs exits ((Addr 36, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1][R_R1 := s R_R1 mod 2 ^ 8 .| s R_R1 mod 2 ^ 8 << 8]) :: l) = None)
    (VC8: forall n, forall l, effinv true memset_arm invs exits ((Addr 40, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1][R_R1 := s R_R1 mod 2 ^ 8 .| s R_R1 mod 2 ^ 8 << 8 .| ((s R_R1 mod 2 ^ 8 .| s R_R1 << 8) << 16) mod 2 ^ 32]) :: l) = None)
    (VC9: forall n, forall l, ((s R_R3 mod 4 =? 0) = true) -> nextinv memset_arm invs exits true ((Addr 44, s[R_CF := n mod 2][R_NF := 0][R_ZF := 1][R_R1 := s R_R1 mod 2 ^ 8 .| s R_R1 mod 2 ^ 8 << 8 .| ((s R_R1 mod 2 ^ 8 .| s R_R1 << 8) << 16) mod 2 ^ 32][R_R12 := s R_R1 mod 2 ^ 8 .| s R_R1 mod 2 ^ 8 << 8 .| ((s R_R1 mod 2 ^ 8 .| s R_R1 << 8) << 16) mod 2 ^ 32]) :: l))
    (VC10: forall n, forall l, effinv true memset_arm invs exits ((Addr 20, s[R_CF := n mod 2][R_NF := 0][R_ZF := 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3]) :: l) = None)
    (VC11: forall n, forall l, effinv true memset_arm invs exits ((Addr 24, s[R_CF := n mod 2][R_NF := 0][R_ZF := 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 1]) :: l) = None)
    (VC12: forall n, forall l, ((s R_R3 mod 4 =? 0) = false) -> nextinv memset_arm invs exits true ((Addr 12, s[R_CF := n mod 2][R_NF := 0][R_ZF := 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 1]) :: l))
  ,
  nextinv memset_arm invs exits false ((Addr 12, s)::t).
Proof.
  intros; find_vcs (0::12::44::84::120::nil).
  Unshelve.
  all: match goal with H: _ |- _ =>
      solve [eapply H; first [eassumption | reflexivity]]
  end.
Qed.

Lemma memset_arm_stepfrom_44:
  forall invs exits s t
    (VC1: forall t0, effinv false memset_arm invs exits ((Addr 44, s) :: t0) = None)
    (VC2: forall l, effinv true memset_arm invs exits ((Addr 48, s[R_R2 := s R_R2 ⊖ 8][R_CF := if 8 <=? s R_R2 then 1 else 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC3: forall l, effinv true memset_arm invs exits ((Addr 52, s[R_R2 := s R_R2 ⊖ 8][R_CF := 1][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3]) :: l) = None)
    (VC4: forall l, effinv true memset_arm invs exits ((Addr 56, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := if 8 <=? s R_R2 ⊖ 8 then 1 else 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC5: forall l, effinv true memset_arm invs exits ((Addr 60, s[R_R2 := s R_R2 ⊖ 16][R_CF := 1][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3]) :: l) = None)
    (VC6: forall l, effinv true memset_arm invs exits ((Addr 64, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 24][R_CF := if 8 <=? s R_R2 ⊖ 16 then 1 else 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC7: forall l, effinv true memset_arm invs exits ((Addr 68, s[R_R2 := s R_R2 ⊖ 24][R_CF := 1][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ]][R_R3 := 24 ⊕ s R_R3]) :: l) = None)
    (VC8: forall l, effinv true memset_arm invs exits ((Addr 72, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ]][R_R3 := 24 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 32][R_CF := if 8 <=? s R_R2 ⊖ 24 then 1 else 0][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC9: forall l, effinv true memset_arm invs exits ((Addr 76, s[R_R2 := s R_R2 ⊖ 32][R_CF := 1][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ] [Ⓓ24 + s R_R3 := s R_R1 ] [Ⓓ28 + s R_R3 := s R_R12 ]][R_R3 := 32 ⊕ s R_R3]) :: l) = None)
    (VC10: forall l, ((8 <=? s R_R2) = true) -> ((8 <=? s R_R2 ⊖ 8) = true) -> ((8 <=? s R_R2 ⊖ 16) = true) -> ((8 <=? s R_R2 ⊖ 24) = true) -> nextinv memset_arm invs exits true ((Addr 44, s[R_R2 := s R_R2 ⊖ 32][R_CF := 1][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ] [Ⓓ24 + s R_R3 := s R_R1 ] [Ⓓ28 + s R_R3 := s R_R12 ]][R_R3 := 32 ⊕ s R_R3]) :: l))
    (VC11: forall l, effinv true memset_arm invs exits ((Addr 76, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ]][R_R3 := 24 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 32][R_CF := 0][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 then 1 else 0]) :: l) = None)
    (VC12: forall l, effinv true memset_arm invs exits ((Addr 80, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ]][R_R3 := 24 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 32][R_CF := 0][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 then 1 else 0]) :: l) = None)
    (VC13: forall l, ((8 <=? s R_R2) = true) -> ((8 <=? s R_R2 ⊖ 8) = true) -> ((8 <=? s R_R2 ⊖ 16) = true) -> ((8 <=? s R_R2 ⊖ 24) = false) -> nextinv memset_arm invs exits true ((Addr 84, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ] [Ⓓ16 + s R_R3 := s R_R1 ] [Ⓓ20 + s R_R3 := s R_R12 ]][R_R3 := 24 ⊕ s R_R3][R_CF := 0][R_VF := ((s R_R2 ⊖ 24 .^ 8) .& (s R_R2 ⊖ 24 .^ s R_R2 ⊖ 32)) >> 31][R_NF := s R_R2 ⊖ 32 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 32 then 1 else 0][R_R2 := s R_R2 mod 8]) :: l))
    (VC14: forall l, effinv true memset_arm invs exits ((Addr 68, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 24][R_CF := 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0]) :: l) = None)
    (VC15: forall l, effinv true memset_arm invs exits ((Addr 72, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 24][R_CF := 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0]) :: l) = None)
    (VC16: forall l, effinv true memset_arm invs exits ((Addr 76, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 24][R_CF := 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0]) :: l) = None)
    (VC17: forall l, effinv true memset_arm invs exits ((Addr 80, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 24][R_CF := 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0]) :: l) = None)
    (VC18: forall l, ((8 <=? s R_R2) = true) -> ((8 <=? s R_R2 ⊖ 8) = true) -> ((8 <=? s R_R2 ⊖ 16) = false) -> nextinv memset_arm invs exits true ((Addr 84, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ] [Ⓓ8 + s R_R3 := s R_R1 ] [Ⓓ12 + s R_R3 := s R_R12 ]][R_R3 := 16 ⊕ s R_R3][R_CF := 0][R_VF := ((s R_R2 ⊖ 16 .^ 8) .& (s R_R2 ⊖ 16 .^ s R_R2 ⊖ 24)) >> 31][R_NF := s R_R2 ⊖ 24 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 24 then 1 else 0][R_R2 := s R_R2 mod 8]) :: l))
    (VC19: forall l, effinv true memset_arm invs exits ((Addr 60, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC20: forall l, effinv true memset_arm invs exits ((Addr 64, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC21: forall l, effinv true memset_arm invs exits ((Addr 68, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC22: forall l, effinv true memset_arm invs exits ((Addr 72, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC23: forall l, effinv true memset_arm invs exits ((Addr 76, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC24: forall l, effinv true memset_arm invs exits ((Addr 80, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 16][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0]) :: l) = None)
    (VC25: forall l, ((8 <=? s R_R2) = true) -> ((8 <=? s R_R2 ⊖ 8) = false) -> nextinv memset_arm invs exits true ((Addr 84, s[V_MEM32 := s V_MEM32 [Ⓓs R_R3 := s R_R1 ] [Ⓓ4 + s R_R3 := s R_R12 ]][R_R3 := 8 ⊕ s R_R3][R_CF := 0][R_VF := ((s R_R2 ⊖ 8 .^ 8) .& (s R_R2 ⊖ 8 .^ s R_R2 ⊖ 16)) >> 31][R_NF := s R_R2 ⊖ 16 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 16 then 1 else 0][R_R2 := s R_R2 mod 8]) :: l))
    (VC26: forall l, effinv true memset_arm invs exits ((Addr 52, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC27: forall l, effinv true memset_arm invs exits ((Addr 56, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC28: forall l, effinv true memset_arm invs exits ((Addr 60, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC29: forall l, effinv true memset_arm invs exits ((Addr 64, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC30: forall l, effinv true memset_arm invs exits ((Addr 68, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC31: forall l, effinv true memset_arm invs exits ((Addr 72, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC32: forall l, effinv true memset_arm invs exits ((Addr 76, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC33: forall l, effinv true memset_arm invs exits ((Addr 80, s[R_R2 := s R_R2 ⊖ 8][R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0]) :: l) = None)
    (VC34: forall l, ((8 <=? s R_R2) = false) -> nextinv memset_arm invs exits true ((Addr 84, s[R_CF := 0][R_VF := ((s R_R2 .^ 8) .& (s R_R2 .^ s R_R2 ⊖ 8)) >> 31][R_NF := s R_R2 ⊖ 8 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 8 then 1 else 0][R_R2 := s R_R2 mod 8]) :: l))
  ,
  nextinv memset_arm invs exits false ((Addr 44, s)::t).
Proof.
  intros; find_vcs (0::12::44::84::120::nil).
  Unshelve.
  all: match goal with H: _ |- _ =>
      solve [eapply H; first [eassumption | reflexivity]]
  end.
Qed.

Lemma memset_arm_stepfrom_84:
  forall invs exits s t
    (VC1: forall t0, effinv false memset_arm invs exits ((Addr 84, s) :: t0) = None)
    (VC2: forall l, effinv true memset_arm invs exits ((Addr 88, s[R_R2 := s R_R2 ⊖ 1][R_CF := if 1 <=? s R_R2 then 1 else 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC3: forall l, effinv true memset_arm invs exits ((Addr 92, s[R_R2 := s R_R2 ⊖ 1][R_CF := 1][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3]) :: l) = None)
    (VC4: forall l, effinv true memset_arm invs exits ((Addr 96, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := if 1 <=? s R_R2 ⊖ 1 then 1 else 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC5: forall l, effinv true memset_arm invs exits ((Addr 100, s[R_R2 := s R_R2 ⊖ 2][R_CF := 1][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3]) :: l) = None)
    (VC6: forall l, effinv true memset_arm invs exits ((Addr 104, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 3][R_CF := if 1 <=? s R_R2 ⊖ 2 then 1 else 0][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC7: forall l, effinv true memset_arm invs exits ((Addr 108, s[R_R2 := s R_R2 ⊖ 3][R_CF := 1][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ]][R_R3 := 3 ⊕ s R_R3]) :: l) = None)
    (VC8: forall l, effinv true memset_arm invs exits ((Addr 112, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ]][R_R3 := 3 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 4][R_CF := if 1 <=? s R_R2 ⊖ 3 then 1 else 0][R_VF := ((s R_R2 ⊖ 3 .^ 1) .& (s R_R2 ⊖ 3 .^ s R_R2 ⊖ 4)) >> 31][R_NF := s R_R2 ⊖ 4 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 4 mod 2 ^ 32 then 1 else 0]) :: l) = None)
    (VC9: forall l, effinv true memset_arm invs exits ((Addr 116, s[R_R2 := s R_R2 ⊖ 4][R_CF := 1][R_VF := ((s R_R2 ⊖ 3 .^ 1) .& (s R_R2 ⊖ 3 .^ s R_R2 ⊖ 4)) >> 31][R_NF := s R_R2 ⊖ 4 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 4 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ] [Ⓑ3 + s R_R3 := s R_R1 ]][R_R3 := 4 ⊕ s R_R3]) :: l) = None)
    (VC10: forall l, ((1 <=? s R_R2) = true) -> ((1 <=? s R_R2 ⊖ 1) = true) -> ((1 <=? s R_R2 ⊖ 2) = true) -> ((1 <=? s R_R2 ⊖ 3) = true) -> nextinv memset_arm invs exits true ((Addr 84, s[R_R2 := s R_R2 ⊖ 4][R_CF := 1][R_VF := ((s R_R2 ⊖ 3 .^ 1) .& (s R_R2 ⊖ 3 .^ s R_R2 ⊖ 4)) >> 31][R_NF := s R_R2 ⊖ 4 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 4 then 1 else 0][V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ] [Ⓑ3 + s R_R3 := s R_R1 ]][R_R3 := 4 ⊕ s R_R3]) :: l))
    (VC11: forall l, effinv true memset_arm invs exits ((Addr 116, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ]][R_R3 := 3 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 4][R_CF := 0][R_VF := ((s R_R2 ⊖ 3 .^ 1) .& (s R_R2 ⊖ 3 .^ s R_R2 ⊖ 4)) >> 31][R_NF := s R_R2 ⊖ 4 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 4 then 1 else 0]) :: l) = None)
    (VC12: forall l, ((1 <=? s R_R2) = true) -> ((1 <=? s R_R2 ⊖ 1) = true) -> ((1 <=? s R_R2 ⊖ 2) = true) -> ((1 <=? s R_R2 ⊖ 3) = false) -> nextinv memset_arm invs exits true ((Addr 120, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ] [Ⓑ2 + s R_R3 := s R_R1 ]][R_R3 := 3 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 4][R_CF := 0][R_VF := ((s R_R2 ⊖ 3 .^ 1) .& (s R_R2 ⊖ 3 .^ s R_R2 ⊖ 4)) >> 31][R_NF := s R_R2 ⊖ 4 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 4 then 1 else 0]) :: l))
    (VC13: forall l, effinv true memset_arm invs exits ((Addr 108, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 3][R_CF := 0][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 then 1 else 0]) :: l) = None)
    (VC14: forall l, effinv true memset_arm invs exits ((Addr 112, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 3][R_CF := 0][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 then 1 else 0]) :: l) = None)
    (VC15: forall l, effinv true memset_arm invs exits ((Addr 116, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 3][R_CF := 0][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 then 1 else 0]) :: l) = None)
    (VC16: forall l, ((1 <=? s R_R2) = true) -> ((1 <=? s R_R2 ⊖ 1) = true) -> ((1 <=? s R_R2 ⊖ 2) = false) -> nextinv memset_arm invs exits true ((Addr 120, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ] [Ⓑ1 + s R_R3 := s R_R1 ]][R_R3 := 2 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 3][R_CF := 0][R_VF := ((s R_R2 ⊖ 2 .^ 1) .& (s R_R2 ⊖ 2 .^ s R_R2 ⊖ 3)) >> 31][R_NF := s R_R2 ⊖ 3 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 3 then 1 else 0]) :: l))
    (VC17: forall l, effinv true memset_arm invs exits ((Addr 100, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l) = None)
    (VC18: forall l, effinv true memset_arm invs exits ((Addr 104, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l) = None)
    (VC19: forall l, effinv true memset_arm invs exits ((Addr 108, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l) = None)
    (VC20: forall l, effinv true memset_arm invs exits ((Addr 112, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l) = None)
    (VC21: forall l, effinv true memset_arm invs exits ((Addr 116, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l) = None)
    (VC22: forall l, ((1 <=? s R_R2) = true) -> ((1 <=? s R_R2 ⊖ 1) = false) -> nextinv memset_arm invs exits true ((Addr 120, s[V_MEM32 := s V_MEM32 [Ⓑs R_R3 := s R_R1 ]][R_R3 := 1 ⊕ s R_R3][R_R2 := s R_R2 ⊖ 2][R_CF := 0][R_VF := ((s R_R2 ⊖ 1 .^ 1) .& (s R_R2 ⊖ 1 .^ s R_R2 ⊖ 2)) >> 31][R_NF := s R_R2 ⊖ 2 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 2 then 1 else 0]) :: l))
    (VC23: forall l, effinv true memset_arm invs exits ((Addr 92, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC24: forall l, effinv true memset_arm invs exits ((Addr 96, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC25: forall l, effinv true memset_arm invs exits ((Addr 100, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC26: forall l, effinv true memset_arm invs exits ((Addr 104, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC27: forall l, effinv true memset_arm invs exits ((Addr 108, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC28: forall l, effinv true memset_arm invs exits ((Addr 112, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC29: forall l, effinv true memset_arm invs exits ((Addr 116, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l) = None)
    (VC30: forall l, ((1 <=? s R_R2) = false) -> nextinv memset_arm invs exits true ((Addr 120, s[R_R2 := s R_R2 ⊖ 1][R_CF := 0][R_VF := ((s R_R2 .^ 1) .& (s R_R2 .^ s R_R2 ⊖ 1)) >> 31][R_NF := s R_R2 ⊖ 1 >> 31][R_ZF := if s R_R2 mod 2 ^ 32 =? 1 then 1 else 0]) :: l))
  ,
  nextinv memset_arm invs exits false ((Addr 84, s)::t).
Proof.
  intros; find_vcs (0::12::44::84::120::nil).
  Unshelve.
  all: match goal with H: _ |- _ =>
      solve [eapply H; first [eassumption | reflexivity]]
  end.
Qed.

Ltac memset_arm_bigstep := first [ apply memset_arm_stepfrom_0 | apply memset_arm_stepfrom_12 | apply memset_arm_stepfrom_44 | apply memset_arm_stepfrom_84 ]; intros; (reflexivity || ISA_invhere).
(* END BIGSTEPS GENERATED LEMMAS *)
