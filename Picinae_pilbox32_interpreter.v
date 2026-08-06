Require Export Picinae_pilbox32.

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.

Require Import NArith.
Require Import ZArith.

Require Import Program.Equality.
Require Import Structures.Equalities.

Require Export Lia.
Require Import FunctionalExtensionality.
Require Import String.
Require Import List.
Open Scope N.

Import PIL32Notations.

Inductive p32_asm :=
(* Arithmetic *)
| PIL_add (rd rs1 rs2:N)
| PIL_sub (rd rs1 rs2:N)
| PIL_addi (rd rs1:N) (i:N)
| PIL_subi (rd rs1:N) (i:N)
| PIL_li (rd:N) (i:N)
(* Logical *)
| PIL_and (rd rs1 rs2:N)
| PIL_or  (rd rs1 rs2:N)
| PIL_xor (rd rs1 rs2:N)
| PIL_not (rd rs1:N)
(* Control Flow *)
| PIL_beq (rs1 rs2:N) (si:Z)
| PIL_blt (rs1 rs2:N) (si:Z)
| PIL_bne (rs1 rs2:N) (si:Z)
| PIL_bl (si:Z)
| PIL_jl (i:N)
| PIL_jmp (i:N)
| PIL_jmpr (rs1:N)
(* Memory Access *)
(* address to store/load is *rd + i *)
| PIL_ld (rd rs:N) (i:N)
| PIL_st (rs rd:N) (i:N)
(* Invalid *)
| PIL_InvalidI.

Definition p32_decode_binop_reg op rd rs1 rs2 :=
  match op with
  | 1 => PIL_add rd rs1 rs2
  | 2 => PIL_sub rd rs1 rs2
  | 5 => PIL_and rd rs1 rs2
  | 6 => PIL_or  rd rs1 rs2
  | 7 => PIL_xor rd rs1 rs2
  | 8 => PIL_not rd rs1
  | _ => PIL_InvalidI
  end.

Definition p32_decode_binop_imm op rd rs1 i :=
  match op with
  | 3 => PIL_addi rd rs1 i
  | 4 => PIL_subi rd rs1 i
  | _ => PIL_InvalidI
  end.

Definition p32_decode_cf_simm op rs1 rs2 (si:Z) :=
  match op with
  | 9  => PIL_beq rs1 rs2 si
  | 10 => PIL_blt rs1 rs2 si
  | 11 => PIL_bne rs1 rs2 si
  | _ => PIL_InvalidI
  end.

Definition p32_decode_memacc op rs rd i :=
  match op with
  | 16 => PIL_ld rs rd i
  | 17 => PIL_st rs rd i
  | _ => PIL_InvalidI
  end.

Definition p32_decode_simm op si :=
  match op with
  | 12 => PIL_bl si
  | _ => PIL_InvalidI
  end.

Definition p32_decode_imm op i :=
  match op with
  | 13 => PIL_jl i
  | 14 => PIL_jmp i
  | _ => PIL_InvalidI
  end.

Definition p32_decode_reg op r :=
  match op with
  | 15 => PIL_jmpr r
  | _  => PIL_InvalidI
  end.


(* bit 0 - if set then load immediate; else the following
   bits 1-6 : opcode
   bits 7-9 : usually reg
   bits 10-12 : usually reg
   bits 13-15 : usually reg / imm
*)
Definition p32_decode_op op n : p32_asm:=
  if N.testbit op 0 then PIL_li (xnbits n 1 3) (xnbits n 4 28) else
  match op >> 1 with
  | 1 | 2 | 5 | 6 | 7 | 8 => p32_decode_binop_reg (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 3)
  | 3 | 4 => p32_decode_binop_imm (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 19)
  | 9 | 10 | 11 => p32_decode_cf_simm (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (toZ 19 (xnbits n 13 19))
  | 12 => p32_decode_simm (op >> 1) (toZ 25 (xnbits n 7 25))
  | 13 | 14 => p32_decode_imm (op >> 1) (xnbits n 7 25)
  | 15 => p32_decode_reg (op >> 1) (xnbits n 7 3)
  | 16 | 17 => p32_decode_memacc (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 19)
  | _ => PIL_InvalidI
  end.

Definition p32_decode n : p32_asm :=
  p32_decode_op (N.land n (N.ones 6)) n.

Definition p32_varid (n:N) :=
  match n with
  | 0 => R_R0 | 1 => R_R1 | 2 => R_R2 | 3 => R_R3
  | 4 => R_R4 | 5 => R_R5 | 6 => R_SP | 7 => R_LR
  (* What to do for this invalid case? *)
  | _ => R_PC
  end.

Definition p32var (n:N) := Var (p32_varid n).
Arguments p32var / !n.
Definition TRUE_EXP := Word 1 1.
Definition p32mov n e := Move (p32_varid n) e.
Definition p32branch e a (off:Z) :=
    If e (Jmp (Word ((Z.to_N (Z.of_N a + off)) mod 2^32) 32)) Nop.
(*  let new_pc_exp := (BinOp (match off with | Z.neg _ => OP_MINUS | _ => OP_PLUS end) (Word a 32) (Word (ofZ 32 (Z.abs off)) 32)) in
  If e (Jmp (BinOp OP_PLUS new_pc_exp (Word 4 32))) Nop.
*)

Definition p322il a p32i :=
  match p32i with
  | PIL_InvalidI => Exn 2

  (* Integer Computational Instructions *)
  | PIL_add rd rs1 rs2 => p32mov rd (BinOp OP_PLUS (p32var rs1) (p32var rs2))
  | PIL_sub rd rs1 rs2 => p32mov rd (BinOp OP_MINUS (p32var rs1) (p32var rs2))
  | PIL_addi rd rs1 imm => p32mov rd (BinOp OP_PLUS (p32var rs1) (Word imm 32))
  | PIL_subi rd rs1 imm => p32mov rd (BinOp OP_MINUS (p32var rs1) (Word imm 32))
  | PIL_li rd imm =>  p32mov rd (Word imm 32)
  | PIL_and rd rs1 rs2 => p32mov rd (BinOp OP_AND (p32var rs1) (p32var rs2))
  | PIL_or  rd rs1 rs2 => p32mov rd (BinOp OP_OR  (p32var rs1) (p32var rs2))
  | PIL_xor rd rs1 rs2 => p32mov rd (BinOp OP_XOR (p32var rs1) (p32var rs2))
  | PIL_not rd rs1 => p32mov rd (UnOp OP_NEG (p32var rs1))


  (* Conditional Transfer Instructions *)
  | PIL_beq rs1 rs2 simm => p32branch (BinOp OP_EQ  (p32var rs1) (p32var rs2)) a simm
  | PIL_blt rs1 rs2 simm => p32branch (BinOp OP_LT  (p32var rs1) (p32var rs2)) a simm
  | PIL_bne rs1 rs2 simm => p32branch (BinOp OP_NEQ (p32var rs1) (p32var rs2)) a simm

    (* Unconditional jumps *)
  | PIL_bl simm => Seq (Move R_LR (Word ((a+4) mod 2^32) 32)) (p32branch TRUE_EXP a simm)
  | PIL_jl imm => Seq (Move R_LR (Word ((a+4) mod 2^32) 32)) (Jmp (Word imm 32))
  | PIL_jmp imm => Jmp (Word imm 32)
  | PIL_jmpr rs => Jmp (p32var rs)

  (* Load and Store Instructions *)
  | PIL_ld rd rs imm => p32mov rd (Load (Var V_MEM32) (BinOp OP_PLUS (p32var rs) (Word imm 32)) LittleE 4)
  | PIL_st rs rd imm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (p32var rd) (Word imm 32)) (p32var rs) LittleE 4)

  end.


(* Here we enforce that all instruction fetches must start at a word
   aligned boundary. When we have a variable-length interpreter we
   will need to relax this constraint and introduce another layer of
   complexity.
*)
Definition p32_stmt m a :=
  p322il a match a mod 4 with 0 => p32_decode (getmem 32 LittleE 4 m a) | _ => PIL_InvalidI end.

Definition p32_prog : program :=
  fun s a => if N.testbit (s A_EXEC) a then
               Some (4, p32_stmt (s V_MEM32) a)
             else None.

Lemma hastyp_p32mov:
  forall c0 c n e (TS: hastyp_stmt c0 c (Move (p32_varid n) e) c),
  hastyp_stmt c0 c (p32mov n e) c.
Proof.
  intros. unfold p32mov, p32_varid in *. exact TS.
Qed.

Lemma hastyp_pthirtytwomov:
  forall n e (TE: hastyp_exp pil32typctx e (32)),
  hastyp_stmt pil32typctx pil32typctx (Move (p32_varid n) e) pil32typctx.
Proof.
  intros. erewrite store_upd_eq at 3.
    eapply TMove.
      right. destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
      exact TE.
      reflexivity.
    destruct n as [|n]. reflexivity. repeat first [ reflexivity | destruct n as [n|n|] ].
Qed.

Lemma hastyp_p32store:
  forall e (TE: hastyp_exp pil32typctx e (2^32*8)),
  hastyp_stmt pil32typctx pil32typctx (Move V_MEM32 e) pil32typctx.
Proof.
  intros. erewrite store_upd_eq at 3.
    eapply TMove.
      right. reflexivity.
      exact TE.
      reflexivity.
    reflexivity.
Qed.

Lemma p32varid_numt32:
  forall n, pil32typctx (p32_varid n) = Some ( 32).
Proof.
  intro. unfold p32_varid.
  destruct n as [|n]; try reflexivity. unfold pil32typctx.
  (* Why doesn't this work: repeat (reflexivity || destruct n as [n]). *)
  destruct n; try destruct n; try destruct n.
  all: reflexivity.
Qed.

Lemma hastyp_p32var:
  forall n, hastyp_exp pil32typctx (p32var n) ( 32).
Proof.
  intro. unfold p32var, p32_varid.
  apply TVar. destruct n as [|n]; try reflexivity. unfold pil32typctx.
  (* Why doesn't this work: repeat (reflexivity || destruct n as [n]). *)
  destruct n; try destruct n; try destruct n.
  all: reflexivity.
Qed.


Theorem varupdate_nop:
  forall n, pil32typctx[p32_varid n := Some ( 32)] = pil32typctx.
Proof.
  unfold update, pil32typctx; intros. extensionality a.
  assert (H: forall v n, v = p32_varid n -> v <> V_MEM32 /\ v <> A_READ /\ v <> A_WRITE /\ v <> A_EXEC).
    clear n a; unfold p32_varid; intros. subst. repeat split.
    1-4: destruct n as [|p];[
        intros; discriminate
      | repeat (intros;discriminate || destruct p as [p|p|])].
  destruct (a==p32_varid n).
    specialize (H a n e). destruct H as [H1 [H2 [H3 h4]]]. subst a. destruct (p32_varid n); easy.
    destruct a; try reflexivity.
Qed.

Theorem regupdate_nop:
  forall r, match r with
  | V_MEM32 | A_READ | A_WRITE | A_EXEC => True
  | _ => pil32typctx[r := Some ( 32)] = pil32typctx
  end.
Proof.
  intros; unfold update; destruct r; try apply I; extensionality a;
    destruct (a == _); subst; reflexivity.
Qed.

Theorem hastyp_varupdate:
  forall n, pil32typctx ⊆ pil32typctx[p32_varid n := Some ( 32)].
Proof.
  unfold pfsub, update. intros.
    destruct (x == p32_varid n); subst.
      now rewrite p32varid_numt32 in H.
      assumption.
Qed.


Theorem hastyp_word:
  forall c n pl pr, pl <= pr -> hastyp_exp c (Word (n mod 2 ^ pl) pr) ( pr).
Proof.
  intros. econstructor. apply N.lt_le_trans with (m:=2^pl).
    apply mp2_mod_lt.
    apply N.pow_le_mono_r; lia.
Qed.


Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Theorem welltyped_p322il:
  forall a n, hastyp_stmt pil32typctx pil32typctx (p322il a (p32_decode n)) pil32typctx.
Proof.
  intros.
  unfold p32_decode, p32_decode_op, p32_decode_binop_reg, p32_decode_binop_imm,
    p32_decode_cf_simm, p32_decode_memacc, p32_decode_simm, p32_decode_imm, p32_decode_reg.

  repeat match goal with |- context [ match ?x with _ => _ end ] =>
    let op := fresh "op" in
    generalize x; intro op;
    match type of op with
    | bool => destruct op
    | _ => first [ destruct op as [|op] | destruct op as [op|op|] ]
    end;
    try apply TExn
  end.


  all: try solve [ do 2 repeat first
  [ reflexivity
  | discriminate 1
  | apply hastyp_p32mov
  | apply hastyp_p32mov
  | apply hastyp_p32var
  | apply hastyp_p32store
  | apply TBinOp with (w:=32)
  | apply hastyp_varupdate
  | eapply N.lt_le_trans; [apply xnbits_bound + apply xbits_bound|]
  | apply ofZ_bound
  | apply N.mod_lt
  | econstructor ] ].

  Ltac destruct_var n b tac:=
    destruct (xnbits n b 3) as [|p]; repeat (tac || destruct p as [p|p|]).
  Ltac duh := try right; try ( (apply hastyp_word; lia) || (apply hastyp_varupdate) ); try now rewrite p32varid_numt32;
    try (apply TBinOp with (w:=32); apply hastyp_p32var || apply hastyp_word; try lia).
  Ltac econs_duh := econstructor; duh.
  all: econs_duh; repeat first
    [ apply TBinOp with (w:=32)
    | apply hastyp_p32var
    | apply hastyp_word
    | rewrite varupdate_nop
    |   match goal with
        | [|-context[update _ ?R (Some ( 32))]]
            => rewrite (regupdate_nop R)
        end
    | lia
    | solve apply pfsub_refl
    | econs_duh].
  all: try rewrite varupdate_nop; try apply pfsub_refl; try lia.
  1-2:eapply (hastyp_varupdate 7).
  unfold widthof_binop; lia.
  reflexivity.
  Unshelve. all: exact 3.
Qed.

Theorem welltyped_p32prog:
  welltyped_prog pil32typctx p32_prog.
Proof.
  intros s a. unfold p32_prog.
  destruct (N.testbit (s A_EXEC) a); try exact I.
  eexists.
  unfold p32_stmt; destruct (a mod 4);[
    apply welltyped_p322il
    | apply TExn; reflexivity
  ].
Qed.

(* Assembler section *)
Definition assemble_insn_op (insn:p32_asm) : N :=
  match insn with
  | PIL_add rd rs1 rs2 => 1 << 1
  | PIL_sub rd rs1 rs2 => 2 << 1
  | PIL_addi rd rs1 i => 3 << 1
  | PIL_subi rd rs1 i => 4 << 1
  | PIL_and rd rs1 rs2 => 5 << 1
  | PIL_or  rd rs1 rs2 => 6 << 1
  | PIL_xor rd rs1 rs2 => 7 << 1
  | PIL_not rd rs1 => 8 << 1
  | PIL_beq rs1 rs2 si => 9 << 1
  | PIL_blt rs1 rs2 si => 10 << 1
  | PIL_bne rs1 rs2 si => 11 << 1
  | PIL_bl si => 12 << 1
  | PIL_jl i => 13 << 1
  | PIL_jmp i => 14 << 1
  | PIL_jmpr rs1 => 15 << 1
  | PIL_ld rd rs i => 16 << 1
  | PIL_st rs rd i => 17 << 1
  | PIL_li rd i => 1
  | PIL_InvalidI => 0
  end.

(* Definition p32_varid (n:N) :=
  match n with
  | 0 => R_R0 | 1 => R_R1 | 2 => R_R2 | 3 => R_R3
  | 4 => R_R4 | 5 => R_R5 | 6 => R_SP | 7 => R_LR
  (* What to do for this invalid case? *)
  | _ => R_PC
  end.
Definition assemble_reg (r:p32var) : option N :=
  match r with
  | R_R0 => 0 *)

Definition p32_decode_op_cp op n : p32_asm:=
  if N.testbit op 0 then PIL_li (xnbits n 1 3) (xnbits n 4 28) else
  match op >> 1 with
  | 1 | 2 | 5 | 6 | 7 | 8 => p32_decode_binop_reg (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 3)
  | 3 | 4 => p32_decode_binop_imm (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 19)
  | 9 | 10 | 11 => p32_decode_cf_simm (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (toZ 19 (xnbits n 13 19))
  | 12 => p32_decode_simm (op >> 1) (toZ 25 (xnbits n 7 25))
  | 13 | 14 => p32_decode_imm (op >> 1) (xnbits n 7 25)
  | 15 => p32_decode_reg (op >> 1) (xnbits n 7 3)
  | 16 | 17 => p32_decode_memacc (op >> 1) (xnbits n 7 3) (xnbits n 10 3) (xnbits n 13 19)
  | _ => PIL_InvalidI
  end.

Definition assemble_insn (insn:p32_asm) : N :=
  match insn with
  | PIL_add rd rs1 rs2
  | PIL_sub rd rs1 rs2
  | PIL_and rd rs1 rs2
  | PIL_or  rd rs1 rs2
  | PIL_xor rd rs1 rs2
      => (assemble_insn_op insn) .| ( rd << 7) .| ( rs1 << 10) .| ( rs2 << 13)
  | PIL_addi rd rs1 i
  | PIL_subi rd rs1 i
      => (assemble_insn_op insn) .| ( rd << 7) .| ( rs1 << 10) .| (i  << 13)
  | PIL_not rd rs1
      => (assemble_insn_op insn) .| ( rd << 7) .| ( rs1 << 10)
  | PIL_beq rs1 rs2 si
  | PIL_blt rs1 rs2 si
  | PIL_bne rs1 rs2 si
      => (assemble_insn_op insn) .| ( rs1 << 7) .| ( rs2 << 10) .| ((ofZ (32-13) si) << 13)
  | PIL_bl si
        => (assemble_insn_op insn) .| ((ofZ (32-7) si) << 7)
  | PIL_jl i
  | PIL_jmp i
        => (assemble_insn_op insn) .| (i << 7)
  | PIL_jmpr rs1
        => (assemble_insn_op insn) .| ( rs1 << 7)
  | PIL_ld r1 r2 i
  | PIL_st r1 r2 i
        => (assemble_insn_op insn) .| ( r1 << 7) .| ( r2 << 10) .| (i << 13)
  | PIL_li rd i
        => (assemble_insn_op insn) .| ( rd << 1) .| (i << 4)
  | PIL_InvalidI => 0
  end.

Definition welltyped_p32_asm (insn:p32_asm) : Prop :=
  match insn with
  | PIL_add rd rs1 rs2
  | PIL_sub rd rs1 rs2
  | PIL_and rd rs1 rs2
  | PIL_or  rd rs1 rs2
  | PIL_xor rd rs1 rs2
      => rd < 8 /\ rs1 < 8 /\ rs2 < 8
  | PIL_addi rd rs1 i
  | PIL_subi rd rs1 i
      => rd < 8 /\ rs1 < 8 /\ i < 2^(32-13)
  | PIL_not rd rs1
      => rd < 8 /\ rs1 < 8
  | PIL_beq rs1 rs2 si
  | PIL_blt rs1 rs2 si
  | PIL_bne rs1 rs2 si
      => rs1 < 8 /\ rs2 < 8 /\ signed_range (32-13) si
  | PIL_bl si
        => signed_range (32-7) si
  | PIL_jl i
  | PIL_jmp i
        => i < 2 ^ (32-7)
  | PIL_jmpr rs1
        => rs1 < 8
  | PIL_ld r1 r2 i
  | PIL_st r1 r2 i
        => r1 < 8 /\ r2 < 8 /\ i < 2 ^ (32-13)
  | PIL_li rd i
        => rd < 8 /\ i < 2 ^ (32-4)
  | PIL_InvalidI => True
  end.

Create HintDb bitspec.

(* Print HintDb bitspec.
Set Debug Auto. *)
Hint Resolve N.bits_inj_0 : bitspec.
Hint Rewrite N.land_spec  : bitspec.
Hint Rewrite N.shiftl_spec_low using lia: bitspec.
Hint Rewrite N.ones_spec_high using lia: bitspec.
Hint Immediate Bool.andb_false_r : bitspec.
Hint Extern 1 =>
  match goal with
  | [H:?m <= ?n |- andb (N.testbit _ ?i) (N.testbit _ ?i)] => destruct (N.lt_ge_cases i m)
  end : bitspec.
Hint Extern 1 => match goal with | |- context[N.testbit (?a << ?n) _] => rewrite (N.shiftl_spec_low a n);[|lia] end : bitspec.
Hint Extern 1 => match goal with | |- context[N.testbit (N.ones ?n) ?m] => idtac n m; rewrite (N.ones_spec_high n m);[|lia] end : bitspec.



(* TODO: add to Picinae_theory or the coq standard lib *)
Lemma Nshiftr_land_ones_high:
  forall a n m, m <= n -> (a << n) .& (N.ones m) = 0.
Proof.
  intros a n m H.
  apply N.bits_inj_0; intro i; rewrite N.land_spec.
  (* Destruct attempt failing here... *)
  (* auto with bitspec. *)
  destruct (N.lt_ge_cases i m) as [Lt|Ge].
    (* i < m -> a << n has a 0 *)

    rewrite N.shiftl_spec_low; easy || lia.
    (* i >= m -> N.ones has a 0 *)
    rewrite N.ones_spec_high; easy || lia.
Qed.

Lemma Nshiftr_land_high_nop:
  forall a b n m, n > m -> (a .| b << n) .& (N.ones m) = a .& (N.ones m).
Proof.
  intros.
  apply N.bits_inj.
  unfold N.eqf. intro i.
  rewrite! N.land_spec, N.lor_spec.
  destruct (N.lt_ge_cases i m) as [Lt|Ge].
    (* i < m -> can safely ignore (b << n) *)
    rewrite N.shiftl_spec_low; try lia. rewrite Bool.orb_false_r; reflexivity.
    (* m <= i -> N.ones m is 0 *)
    rewrite N.ones_spec_high; try lia.
Qed.

Lemma Nland_low:
  forall a n, a < 2 ^ n -> a .& (N.ones n) = a.
Proof.
  intros a n H.
  rewrite N.land_ones, N.mod_small; easy.
Qed.

Lemma xbits_lor_low_l:
  forall n m i j, i <= j -> n < 2 ^ i -> xbits (n .| m) i j = xbits m i j.
Proof.
  intros n m i j H G.
  unfold xbits.
  rewrite N.shiftr_lor, shiftr_low_pow2; try lia.
  rewrite N.lor_0_l; reflexivity.
Qed.

Lemma xbits_lor_low_r:
  forall n m i j, i <= j -> n < 2 ^ i -> xbits (m .| n) i j = xbits m i j.
Proof.
  intros n m i j H G.
  rewrite N.lor_comm, xbits_lor_low_l; lia.
Qed.

Lemma xbits_lshift_0:
  forall n shift i j, i <= j -> j <= shift -> xbits (n << shift) i j = 0.
Proof.
  intros n shift i j IJ JShift.
  unfold xbits.
  rewrite  N.shiftr_shiftl_l; try lia.
  (* Another good use of N.bits_inj *)
  apply N.bits_inj_0; intro index.
  destruct (N.lt_ge_cases index (j-i)) as [Lt|Ge].
    rewrite N.mod_pow2_bits_low; try lia. rewrite N.shiftl_spec_low; lia.
    rewrite N.mod_pow2_bits_high; try lia.
Qed.

Lemma xbits_lor_high:
  forall n m shift i j, i <= j -> j <= shift -> xbits (n .| m << shift) i j = xbits n i j.
Proof.
  intros n m shift i j H G.
  rewrite xbits_lor, xbits_lshift_0, N.lor_0_r; lia.
Qed.

Lemma shiftl_0_or_high:
  forall x n m, m <= n -> x << n = 0 \/ x << n >= 2 ^ m.
Proof.
  intros. destruct x;[left;psimpl;lia | right].
  rewrite N.ge_le_iff.
  rewrite N.shiftl_mul_pow2.
  apply N.le_trans with (m:= N.pos p * 2 ^ m); try lia.
    rewrite <-(N.mul_1_l (2^m)) at 1. apply N.mul_le_mono_r; lia.
    apply N.mul_le_mono_l, N.pow_le_mono_r; lia.
Qed.

Lemma xbits_small:
  forall x w, x < 2 ^ w -> xbits x 0 w = x.
Proof.
  intros x w H.
  (*destruct x; [vm_compute; reflexivity|].*)
  unfold xbits; apply N.bits_inj. rewrite N.sub_0_r, N.shiftr_0_r.
  unfold N.eqf. intro i.
  destruct (N.lt_ge_cases i w) as [Lt|Ge].
    rewrite N.mod_pow2_bits_low; lia || reflexivity.
    rewrite N.mod_pow2_bits_high; try lia.
    rewrite bound_hibits_zero with (w:=w); try lia.
Qed.

Lemma xbits_lshift_eq:
  forall x n w, x < 2 ^ w -> xbits (x << n) n (w+n) = x.
Proof.
  intros x n w H.
  rewrite! xbits_shiftl, N.sub_diag, N.add_sub, N.shiftl_0_r.
  apply xbits_small; assumption.
Qed.

Lemma Nlor_rshift_low_l:
  forall x y shift, x < 2 ^ shift -> (x .| y) >> shift = y >> shift.
Proof.
  intros x y shift H.
  apply N.bits_inj; unfold N.eqf; intro i.
  rewrite! N.shiftr_spec', N.lor_spec, bound_hibits_zero with(w:=shift); try lia.
  rewrite Bool.orb_false_l; reflexivity.
Qed.

Lemma pow2_split_shift:
  forall p shift q, q = p+shift -> 2 ^ q = 2 ^ p << shift.
Proof.
  intros p shift q Eq.
  rewrite N.shiftl_mul_pow2, <-N.pow_add_r, Eq; reflexivity.
Qed.

Lemma Nshiftl_mono_pow2:
  forall x shift p q, x < 2 ^ p -> q = shift + p -> x << shift < 2 ^ q.
Proof.
  intros x shift p q BOUND Eq.
  rewrite pow2_split_shift with (shift:=shift) (p:=p); try lia.
  apply Nshiftl_mono_lt_iff; assumption.
Qed.

Lemma xbits_0_low:
  forall n j, n < 2 ^ j -> xbits n 0 j = n.
Proof.
  intros; rewrite xbits_0_i; now rewrite N.mod_small.
Qed.

Theorem decode_assemble_insn :
  forall (insn:p32_asm)
    (WT: welltyped_p32_asm insn),
  p32_decode (assemble_insn insn) = insn.
Proof.
  unfold welltyped_p32_asm, p32_decode, assemble_insn, p32_decode_op, assemble_insn_op;
    intros; destruct insn eqn:INSN;
  repeat match goal with
  | [H: _ /\ _ |- _] => destruct H
  end.
  all: rewrite N.land_spec, N.ones_spec_low, Bool.andb_true_r; try lia;
       repeat rewrite N.lor_spec; repeat rewrite N.shiftl_spec_low; try lia;
       repeat rewrite Bool.orb_false_l; unfold N.testbit, Pos.testbit; try rewrite Bool.orb_true_l.
  all: repeat rewrite Nshiftr_land_high_nop; try lia; simpl (_ << _ .& _); psimpl.
  all: unfold p32_decode_binop_reg, p32_decode_binop_imm, p32_decode_cf_simm, p32_decode_imm,
         p32_decode_reg, p32_decode_memacc, p32_decode_simm, xnbits.

  all: repeat
     match goal with
    (* Solvers *)
     | H:?x |- ?x => assumption
     | |- _ < _ => lia
     | |- _ <= _ => lia
     | |- _ = _ => lia
     | |- ?t = ?t => reflexivity
     | |- _ .| _ < _ => apply lor_bound
     | |- ofZ ?w _ < 2 ^ ?w => apply ofZ_bound
    (* Simple Simplifiers *)
     | [H:context[_-_] |- _] => simpl (_-_) in H
     | [|-context[_-_]] => simpl (_-_)
    (* Reducers *)
     | |- _ << ?S < 2 ^ ?p =>  apply (Nshiftl_mono_pow2 _ S (p-S));
         simpl (_-_)
     | [ |- context[xbits (?L .| ?R << ?i) ?i ?j]] =>
         rewrite (xbits_lor_low_l L _ i j); [|lia|try lia]
     | [ |- context[xbits (?L .| ?R << ?S) ?i ?j]] =>
         rewrite (xbits_lor_high L R S _ j)
     | |- context[xbits (?N << ?S) ?S (?w + ?S)] =>
         rewrite (xbits_lshift_eq N S w)
     | [H:context[_-_]|- context[xbits (?N << ?S) ?S (?S+?w)] ]=>
         rewrite (xbits_lshift_eq N S w)
     | |- context[toZ ?w (ofZ ?w _)] => rewrite toZ_ofZ
     end.
Qed.

(* TODO:
      1) define an operational semantics for PIL32_asm
      2) define an assembly program
      3) define small step operational semantics of the assembly program
      4) formalize a bisimilarity between the execution of an assembly program and
         a picinae program from a decoded assemble program given that the assembly
         is well typed
      5) prove it.
*)

Definition insn_length (insn:p32_asm) : N := 4.

(* Each assembly code is represented as

      * a base address (e.g. 0x00100000)
      * a list of labels (strings) and instructions (p32_asm)
*)
Inductive p32_assembly :=
  P32_ASSEMBLY (base_addr:N) (code:list (sum string p32_asm)).

Fixpoint label_loc (label:string) (base_addr:N) (code:list (sum string p32_asm)) : option N :=
  match code with
  | nil => None
  | inl label' :: t => if (label =? label')%string then Some base_addr
      else label_loc label base_addr t
  | inr insn :: t => label_loc label (base_addr + (insn_length insn)) t
  end.

Import ListNotations.
Open Scope string.

Definition p32_assemble_insn_bytes (insn:p32_asm) : list N :=
  (xnbits (assemble_insn insn) 0  8) ::
  (xnbits (assemble_insn insn) 8  8) ::
  (xnbits (assemble_insn insn) 16 8) ::
  (xnbits (assemble_insn insn) 24 8) :: nil.

Fixpoint p32_assemble' (base_addr:N) (mem:N) (code:list (p32_asm)) : N :=
  match code with
  | nil => mem
  | insn :: t => p32_assemble' (base_addr+4) (setmem 32 LittleE 4 mem base_addr (assemble_insn insn)) t
  end.

Require Import String.
Require Import Ascii.
Require Import Recdef.
Require Import Program.
Require Import Lia.

Open Scope string.
Open Scope nat.
Definition newline :string := String "010" EmptyString.

(* Serious performance issues converting 4+ digit numbers to a string.
   at 6 digits Coqide crashes. *)
Program Fixpoint nat2str (n:nat) (acc:string) {measure n}: string :=
  (match n with
    | O => String "0" acc
    | 1 => String "1" acc
    | 2 => String "2" acc
    | 3 => String "3" acc
    | 4 => String "4" acc
    | 5 => String "5" acc
    | 6 => String "6" acc
    | 7 => String "7" acc
    | 8 => String "8" acc
    | 9 => String "9" acc
    | _ => nat2str (n/10)
       (String (match n mod 10 with
         | O => "0"
         | 1 => "1"
         | 2 => "2"
         | 3 => "3"
         | 4 => "4"
         | 5 => "5"
         | 6 => "6"
         | 7 => "7"
         | 8 => "8"
         | 9 => "9"
         | _ => "!"
       end) acc)
  end)%nat .
Obligation 1.
  repeat split; intro; discriminate. Defined.
Next Obligation.
  enough (H': fst (Nat.divmod n 9 0 9) = (n / 10));[
  rewrite H'; apply Nat.div_lt; lia| now unfold Nat.divmod]. Defined.
Next Obligation.
  repeat split; intro; discriminate. Defined.
Close Scope nat.

Definition N2str n := nat2str (N.to_nat n) EmptyString.

Fixpoint p32_code_length (code:list p32_asm) : N:=
  match code with
  | nil => 0
  | h::t => (insn_length h) + (p32_code_length t)
  end.

Definition print_code_prop (code:list p32_asm) (base_addr:N) (name:string) :=
  ("Definition " ++ name ++ " (mem:N) : Prop :=" ++ newline ++
  " xbits mem " ++ (N2str (base_addr * 8)) ++ " " ++
  (N2str ((base_addr + (p32_code_length code)) * 8)) ++ " = " ++
  "XXXX" ++ "." ++ newline ++
  "Definition " ++ name ++ "_aexec (mem:N) : Prop :=" ++ newline ++
  "  xbits mem " ++ (N2str base_addr) ++ " " ++
  (N2str (base_addr + (p32_code_length code))) ++ " = " ++
  "XXXX" ++ "." ++ newline
  , (p32_assemble' 0 0 code)
  , N.ones (p32_code_length code) ).

(* Definition program' := [PIL_li 0 0; PIL_addi 1 1 1; PIL_subi 2 2 1; PIL_beq 0 2 (-12)%Z]. *)
(* Compute p32_assemble 0x00100000 program'. *)
(* Compute p32_code_length program'. *)
(* Compute p32_assemble' 0 0 program'. *)
(* Compute print_code_prop program' 0 "p". *)
Ltac get_exec :=
  repeat match goal with
  | [P: ?prop ?v |- _ ] => unfold prop in P
  | [H: xbits (_ ?m) _ _ = _ |- context[N.testbit (update ?s _ _ ?m) _]] =>
    rewrite (update_frame s _ _ m); try easy
  | [H: xbits ?v ?l ?h = ?mem |- context[N.testbit ?v ?i]] =>
    let HELP := fresh "H" in
    assert (HELP: l <= i /\ i <= h) by (split; lia); clear HELP;
    rewrite testbit_xbits, (xbits_split2 l i (N.succ i) h v mem);
    try lia
  end; vm_compute (N.odd _); psimpl.

(* These hooks are used in ISA_invseek to simplify the memory program
   instruction expression which, for an interpreted language like this
   one, is read as bytes from memory then decoded. *)
Ltac effinv_none_hook ::= unfold effinv, effinv', p32_prog; get_exec.
Ltac psa_some_hook ::=   unfold p32_prog, p32_stmt; get_exec;
  repeat match goal with
  | [ |- context[p32_decode (getmem ?w LittleE ?len ?mem ?a)]] =>
    rewrite (getmem_xbits w len mem a); try lia
  | [H: xbits ?mem ?i ?j = ?v
    |- context[xbits ?mem ?a ?b]] =>
    rewrite (xbits_split2 i a b j mem v); try lia; vm_compute (p32_decode _)
  | _ => reflexivity
  end.
