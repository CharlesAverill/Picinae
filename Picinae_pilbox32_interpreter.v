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
Require Import Lia.
Open Scope N.

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
Definition p32_decode_op op n :=
  if N.testbit op 0 then PIL_li (xbits n 1 3) (xbits n 4 28) else
  match op with
  | 1 | 2 | 5 | 6 | 7 | 8 => p32_decode_binop_reg op (xbits n 7 3) (xbits n 10 3) (xbits n 13 3)
  | 3 | 4 => p32_decode_binop_imm op (xbits n 7 3) (xbits n 10 3) (xbits n 13 19)
  | 9 | 10 | 11 => p32_decode_cf_simm op (xbits n 7 3) (xbits n 10 3) (toZ 19 (xbits n 13 19))
  | 12 => p32_decode_simm op (toZ 25 (xbits n 7 25))
  | 13 | 14 => p32_decode_imm op (xbits n 7 25)
  | 15 => p32_decode_reg op (xbits n 7 3)
  | 16 | 17 => p32_decode_memacc op (xbits n 7 3) (xbits n 10 3) (xbits n 13 19)
  | _ => PIL_InvalidI
  end.

Definition p32_decode n :=
  p32_decode_op (N.land n (N.ones 6)) n.

Definition p32_varid (n:N) :=
  match n with
  | 0 => R0 | 1 => R1 | 2 => R2 | 3 => R3
  | 4 => R4 | 5 => R5 | 6 => R_SP | 7 => R_LR 
  (* What to do for this invalid case? *)
  | _ => R_PC
  end.

Definition p32var (n:N) := Var (p32_varid n).
Definition TRUE_EXP := Word 1 1.
Definition p32mov n e := Move (p32_varid n) e.
Definition p32branch e a (off:Z) :=
  let new_pc_exp := (BinOp (match off with | Z.neg _ => OP_MINUS | _ => OP_PLUS end) (Word a 32) (Word (ofZ 32 (Z.abs off)) 32)) in
  If e (Jmp (BinOp OP_PLUS new_pc_exp (Word 4 32))) Nop.

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
  | PIL_bl simm => Seq (Move R_LR (BinOp OP_PLUS (Word a 32) (Word 4 32))) (p32branch TRUE_EXP a simm)
  | PIL_jl imm => Seq (Move R_LR (BinOp OP_PLUS (Word a 32) (Word 4 32))) (Jmp (Word imm 32))
  | PIL_jmp imm => Jmp (Word imm 32)
  | PIL_jmpr rs => Jmp (p32var rs)

  (* Load and Store Instructions *)
  | PIL_ld rd rs imm => p32mov rd (Load (Var V_MEM32) (BinOp OP_PLUS (p32var rs) (Word imm 32)) LittleE 4)
  | PIL_st rs rd imm => Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (p32var rd) (Word imm 32)) (p32var rs) LittleE 4)

  end.
  

Definition p32_stmt m a :=
  p322il a match a mod 4 with 0 => p32_decode (getmem 32 LittleE 4 m a) | _ => PIL_InvalidI end.

Definition p32_prog : program :=
  fun s a => match s V_MEM32, s A_EXEC with
             | VaM m _, VaM e _ => match e a with
                                   | N0 => None
                                   | _ => Some (4, p32_stmt m a)
                                   end
             | _, _ => None
             end.

Lemma hastyp_p32mov:
  forall c0 c n e (TS: hastyp_stmt c0 c (Move (p32_varid n) e) c),
  hastyp_stmt c0 c (p32mov n e) c.
Proof.
  intros. unfold p32mov, p32_varid in *. exact TS.
Qed.

Lemma hastyp_pthirtytwomov:
  forall n e (TE: hastyp_exp pil32typctx e (NumT 32)),
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
  forall e (TE: hastyp_exp pil32typctx e (MemT 32)),
  hastyp_stmt pil32typctx pil32typctx (Move V_MEM32 e) pil32typctx.
Proof.
  intros. erewrite store_upd_eq at 3.
    eapply TMove.
      right. reflexivity.
      exact TE.
      reflexivity.
    reflexivity.
Qed.

Lemma hastyp_p32var:
  forall n, hastyp_exp pil32typctx (p32var n) (NumT 32).
Proof.
  intro. unfold p32var, p32_varid.
  apply TVar. destruct n as [|n]; try reflexivity. unfold pil32typctx.
  (* Why doesn't this work: repeat (reflexivity || destruct n as [n]). *)
  destruct n; try destruct n; try destruct n.
  all: reflexivity.
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
    first [ destruct op as [|op] | destruct op as [op|op|] ];
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
  | eapply N.lt_le_trans; [apply xbits_bound|]
  | apply ofZ_bound
  | apply N.mod_lt
  | econstructor ] ].

  econstructor. 
    right. unfold pil32typctx, p32_varid. destruct (xbits _); 
      try destruct p as [p|p|]; try destruct p as [p|p|]; try destruct p; reflexivity.
    econstructor. unfold xbits. psimpl. apply N.lt_trans with (m:=2^24). apply mp2_mod_lt. lia.
    unfold pfsub, update. intros. (* Todo prove varid_dec: forall x:pil32var n:N, {p32_varid n = x}+{p32_varid n <> x} *)
      destruct (x == p32_varid (xbits n 1 3)). unfold p32_varid, pil32typctx in *.
        destruct (xbits n 1 3) as [|p]; repeat ((subst; assumption) || destruct p as [p|p|]).
        assumption.
  (* TODO: Continue here *)
Qed.

Theorem welltyped_p32prog:
  welltyped_prog pil32typctx p32_prog.
Proof.
  intros s a. unfold p32_prog.
  destruct (s V_MEM32), (s A_EXEC); try exact I.
  destruct (m0 a).
    exact I.
    exists p32typctx. unfold p32_stmt. destruct (a mod 4).
      apply welltyped_p322il.
      apply TExn. reflexivity.
Qed.


(* Create some automated machinery for simplifying symbolic expressions. *)

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.

