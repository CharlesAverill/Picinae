Require Import Coq.Lists.List.

Import ListNotations.
Import RISCVNotations.

(* Definition list2bv' : list (N * N) -> N * N := *)
(*   fold_right *)
(*     (fun (kar kdr : N*N) => *)
(*        let (len,obj) := kar in let (tlen,tobj) := kdr in *)
(*        (len + tlen, obj << tlen .| tobj)) *)
(*     (0,0). *)

Fixpoint list2bv (l : list (N * N)) : N * N :=
  match l with
  | [] => (0,0)
  | (len,obj)::t =>
    let (tlen,tobj) := list2bv t in
    (len + tlen, (obj << tlen) .| tobj)
  end.

Theorem list2bv_len l :
  fst (list2bv l) = fold_right N.add 0 (map fst l).
  induction l; auto.
  simpl.
  destruct a,list2bv.
  simpl in *.
  subst.
  reflexivity.
Qed.

Definition bv_valid (bv : N * N) : Prop :=
  snd bv < 2^(fst bv).

Definition bvl_valid bvl : Prop :=
  Forall bv_valid bvl.

Theorem list2bv_num l :
  bvl_valid l -> bv_valid (list2bv l).
  unfold bvl_valid,bv_valid.
  induction l; simpl; [reflexivity|].
  intros.
  inversion H; subst.
  destruct a,list2bv.
  apply concat_bound; tauto.
Qed.

(*
  RV32I defines "base instruction formats" R, I, S and U as well as "immediate
  encoding variants" B and J. B is a variant of S and J is a variant of U.
  The U base instruction format is special in that it does not directly take an
  immediate but implicitly shifts the bits of the immediate by 12 so that they
  form the leading bits of a 32-bit immediate.
 *)
Definition rv_encodel_r (opcode funct rd rs1 rs2 : N) :=
  [(7,funct >> 3);(5,rs2);(5,rs1);(3,xbits funct 0 3);(5,rd);(7,opcode)].
Definition rv_encodel_i (opcode funct rd rs1 imm : N) :=
  [(12,imm);(5,rs1);(3,funct);(5,rd);(7,opcode)].
Definition rv_encodel_s (opcode funct rs1 rs2 imm : N) :=
  [(7,imm >> 5);(5,rs2);(5,rs1);(3,funct);(5,xbits imm 0 5);(7,opcode)].
Definition rv_encodel_u_raw (opcode rd immbits : N) :=
  [(20,immbits);(5,rd);(7,opcode)].
Definition rv_encodel_u_opt (opcode rd imm : N) :=
  if xbits imm 0 12 == 0
  then Some (rv_encodel_u_raw opcode rd (imm >> 12))
  else None.

(*
  The B instruction format variant sacrifices the least significant bit of the
  immediate in the S instruction format to encode 13-bit even immediates. These
  represent 2-byte-aligned (16-bit-aligned) instruction offsets.

  The variant looks unusual but is sensible when implemented in hardware: the
  MSB of the B immediate takes the place of the MSB of the S immediate. The
  positions of the middle bits of the S immediate remain the same, and the bit
  in the position that originally represented the LSB of the S immediate is
  replaced by its MSB in the B variant:

   S-immediate: 11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0
   B-immediate: 12,10, 9, 8, 7, 6, 5, 4, 3, 2, 1,11

  Keeping the MSBs in the same position simplifies sign-extension.
 *)
Definition rv_encode_bimm2simm bimm :=
  if xbits bimm 0 1 == 0
  then Some (list2bv [(1,bimm >> 12);(10,xbits bimm 1 11);(1,xbits bimm 11 12)])
  else None.
Definition rv_encodel_b_opt opcode funct rs1 rs2 imm :=
  match rv_encode_bimm2simm imm with
  | None => None
  | Some simm => Some (rv_encodel_s opcode funct rs1 rs2 (snd simm))
  end.

(*
  The J immediate variant is even weirder than the B immediate variant. It only
  makes sense when compared with the rest of the instruction formats/variants:

   R-immediate:
   I-immediate: 11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0
   S-immediate: 11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0
   B-immediate: 12,10, 9, 8, 7, 6, 5, 4, 3, 2, 1,11
   U-immediate: 31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12
   J-immediate: 20,10, 9, 8, 7, 6, 5, 4, 3, 2, 1,11,19,18,17,16,15,14,13,12

  The locations of bits 1-11 are borrowed from B (itself borrowing 1-10 from I
  and S). The locations of bits 12-19 are borrowed from U. Bit 20 is the MSB,
  which is the very first bit of any immediate format. Bits 21-31 are
  sign-extended and bit 0 is implicitly zero (same as with B immediates).
 *)
Definition rv_encodel_jimm jimm :=
  if xbits jimm 0 1 == 0
  then Some
         (list2bv
            [(1,jimm >> 20);(10,xbits jimm 1 11);(1,xbits jimm 11 2)
             ;(8,xbits jimm 12 20)])
  else None.
Definition rv_encodel_j_opt (opcode rd imm : N) :=
  match rv_encodel_jimm imm with
  | None => None
  | Some immbits => Some (rv_encodel_u_raw opcode rd (snd immbits))
  end.

Print rv_asm.
Search "decidable".

Definition bvl_valid_dec bvl : {bvl_valid bvl} + {~bvl_valid bvl}.
  apply Forall_dec.
  unfold bv_valid,N.lt.
  intros.
  destruct (_ ?= _); [|left;reflexivity|]; right; discriminate.
Qed.

Definition list2bv_opt bvl :=
  if bvl_valid_dec bvl then Some (list2bv bvl) else None.

Definition rv_encode_r opcode funct rd rs1 rs2 :=
  list2bv_opt (rv_encodel_r opcode funct rd rs1 rs2).
Definition rv_encode_i opcode funct rd rs1 imm :=
  list2bv_opt (rv_encodel_i opcode funct rd rs1 imm).
Definition rv_encode_s opcode funct rs1 rs2 imm :=
  list2bv_opt (rv_encodel_s opcode funct rs1 rs2 imm).

Fixpoint encode_le_bits (l : list N) :=
  match l with
  | x::xs => x + (encode_le_bits xs << 1)
  | [] => 0
  end.

Definition encode_be_bits l :=
  encode_le_bits (rev l).

Definition rv_encode_addi :=
  rv_encode_i (encode_be_bits [0;0;1;0;0;1;1]) (encode_be_bits [0;0;0]).

Search "rv" "decode".

Theorem ones_alt_decomp n : N.ones (N.succ n) = N.succ (N.double (N.ones n)).
  unfold N.ones.
  destruct n; auto.
  simpl.
  rewrite Pos.iter_succ.
  simpl.
  destruct p using Pos.peano_ind; auto.
  rewrite Pos.iter_succ.
  reflexivity.
Qed.

Theorem rv_shift_and_ones x shl one :
  one <= shl -> (x << shl) .& N.ones one = 0.
  rewrite N.land_ones.
  rewrite N.shiftl_mul_pow2.
  intros.
  rewrite <- (N.sub_add one shl) by assumption.
  rewrite N.pow_add_r.
  rewrite N.mul_assoc.
  rewrite N.mod_mul; auto.
  apply N.pow_nonzero.
  discriminate.
Qed.

Theorem Forall_dest A (P : A -> Prop) x xs :
  Forall P (x::xs) <-> P x /\ Forall P xs.
  split; intro H; inversion H; auto.
Qed.

Theorem rv_encode_addi_check rd rs1 imm :
  match rv_encode_addi rd rs1 imm with
  | None => True
  | Some (l,n) => l = 32 /\ rv_decode n = R5_Addi rd rs1 (scast 12 32 imm)
  end.
  unfold rv_encode_addi,rv_encode_i,rv_encodel_i,encode_be_bits,list2bv_opt.
  simpl.
  destruct bvl_valid_dec; auto.
  split; auto.
  unfold bvl_valid,bv_valid in b.
  repeat rewrite Forall_dest in b.
  simpl in b.
  intuition.
  unfold rv_decode.
  repeat rewrite N.land_lor_distr_l.
  repeat rewrite rv_shift_and_ones by discriminate; auto.
  repeat rewrite N.lor_0_l.
  simpl (19 .& _).
  unfold rv_decode_op,xbits.
  repeat rewrite N.shiftr_lor.
  repeat rewrite N.shiftr_shiftl_l by discriminate.
  repeat rewrite N.shiftr_shiftl_r by discriminate.
  repeat rewrite N.shiftr_div_pow2.
  repeat rewrite N.div_small by assumption.
  repeat rewrite N.land_lor_distr_l.
  repeat rewrite rv_shift_and_ones by discriminate.
  repeat rewrite <- N.shiftr_div_pow2.
  repeat rewrite N.land_0_l.
  rewrite N.lor_0_r.
  repeat rewrite N.shiftr_shiftl_l by discriminate.
  repeat rewrite N.shiftr_shiftl_r by discriminate.
  simpl (_ - _).
  repeat rewrite N.shiftl_0_r.
  repeat rewrite N.shiftr_0_r.
  repeat rewrite rv_shift_and_ones by discriminate.
  repeat rewrite N.shiftr_div_pow2.
  fold (2^5) (2^7) (2^12) in *.
  repeat rewrite N.div_small by
      (eapply N.lt_le_trans,N.pow_le_mono_r; eauto; discriminate).
  simpl.
  repeat rewrite N.lor_0_r,N.land_ones.
  repeat rewrite N.mod_small; auto.
Qed.
(* TODO: sign extension *)
(* scast 12 32 (imm mod 2^32) == imm *)

Definition rv_type :=
  | R5_Lb : N -> N -> N -> rv_asm
  | R5_Lh : N -> N -> N -> rv_asm
  | R5_Lw : N -> N -> N -> rv_asm
  | R5_Lbu : N -> N -> N -> rv_asm
  | R5_Lhu : N -> N -> N -> rv_asm
  | R5_Auipc : N -> N -> rv_asm
  | R5_Sb : N -> N -> Z -> rv_asm
  | R5_Sh : N -> N -> Z -> rv_asm
  | R5_Sw : N -> N -> Z -> rv_asm
  | R5_Add : N -> N -> N -> rv_asm
  | R5_Sub : N -> N -> N -> rv_asm
  | R5_Sll : N -> N -> N -> rv_asm
  | R5_Slt : N -> N -> N -> rv_asm
  | R5_Sltu : N -> N -> N -> rv_asm
  | R5_Xor : N -> N -> N -> rv_asm
  | R5_Srl : N -> N -> N -> rv_asm
  | R5_Sra : N -> N -> N -> rv_asm
  | R5_Or : N -> N -> N -> rv_asm
  | R5_And : N -> N -> N -> rv_asm
  | R5_Lui : N -> N -> rv_asm
  | R5_Beq : N -> N -> Z -> rv_asm
  | R5_Bne : N -> N -> Z -> rv_asm
  | R5_Blt : N -> N -> Z -> rv_asm
  | R5_Bge : N -> N -> Z -> rv_asm
  | R5_Bltu : N -> N -> Z -> rv_asm
  | R5_Bgeu : N -> N -> Z -> rv_asm
  | R5_Jalr : N -> N -> Z -> rv_asm
  | R5_Jal : N -> Z -> rv_asm
  | R5_Addi : N -> N -> N -> rv_asm
  | R5_Slli : N -> N -> N -> rv_asm
  | R5_Slti : N -> N -> N -> rv_asm
  | R5_Sltiu : N -> N -> N -> rv_asm
  | R5_Xori : N -> N -> N -> rv_asm
  | R5_Ori : N -> N -> N -> rv_asm
  | R5_Andi : N -> N -> N -> rv_asm
  | R5_Srli : N -> N -> N -> rv_asm
  | R5_Srai : N -> N -> N -> rv_asm
  | R5_Fence : N -> N -> rv_asm
  | R5_Fence_i : rv_asm
  | R5_InvalidI : rv_asm.

Definition rv_encode :=
