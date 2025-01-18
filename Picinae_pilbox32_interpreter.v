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

Lemma p32varid_numt32:
  forall n, pil32typctx (p32_varid n) = Some (NumT 32).
Proof.
  intro. unfold p32_varid.
  destruct n as [|n]; try reflexivity. unfold pil32typctx.
  (* Why doesn't this work: repeat (reflexivity || destruct n as [n]). *)
  destruct n; try destruct n; try destruct n.
  all: reflexivity.
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


Theorem varupdate_nop:
  forall n, pil32typctx[p32_varid n := Some (NumT 32)] = pil32typctx.
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
  | _ => pil32typctx[r := Some (NumT 32)] = pil32typctx
  end.
Proof.
  intros; unfold update; destruct r; try apply I; extensionality a;
    destruct (a == _); subst; reflexivity.
Qed.

Theorem hastyp_varupdate:
  forall n, pil32typctx ⊆ pil32typctx[p32_varid n := Some (NumT 32)].
Proof.
  unfold pfsub, update. intros.
    destruct (x == p32_varid n); subst.
      now rewrite p32varid_numt32 in H.
      assumption.
Qed.


Theorem hastyp_word:
  forall c n pl pr, pl <= pr -> hastyp_exp c (Word (n mod 2 ^ pl) pr) (NumT pr).
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
        | [|-context[update _ ?R (Some (NumT 32))]] 
            => rewrite (regupdate_nop R) 
        end
    | lia
    | solve apply pfsub_refl
    | econs_duh]. 
  all: try rewrite varupdate_nop; try apply pfsub_refl; try lia.
  Unshelve. all:exact 0.
Qed.

Theorem welltyped_p32prog:
  welltyped_prog pil32typctx p32_prog.
Proof.
  intros s a. unfold p32_prog.
  destruct (s V_MEM32), (s A_EXEC); try exact I.
  destruct (m0 a).
    exact I.
    exists pil32typctx. unfold p32_stmt. destruct (a mod 4).
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

(* Introduce automated machinery for verifying a RISC-V machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine.

   In order for this methodology to prove that a post-condition holds at
   subroutine exit, we must attach one of these invariants (the post-condition)
   to the return address of the subroutine.  This is a somewhat delicate
   process, since unlike most other code addresses, the exact value of the
   return address is an unknown (defined by the caller).  We therefore adopt
   the convention that subroutines "exit" whenever control flows to an address
   for which no IL code is defined at that address.  This allows proving
   correctness of a subroutine by lifting only the subroutine to IL code (or
   using the pmono theorems from Picinae_theory to isolate only the subroutine
   from a larger program), leaving the non-subroutine code undefined (None). *)

(* Simplify memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* Symbolically evaluate a RISC-V machine instruction for one step. *)
Ltac p32_step_and_simplify XS :=
  step_stmt XS;
  psimpl_vals_hyp XS;
  simpl_memaccs XS;
  destruct_memaccs XS.

(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).  This slow-down can
   be avoided by sequestering prevalent injections into lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Addr a. Proof eq_refl.
Remark exitof_some a x: exitof a (Some x) = x. Proof eq_refl.

(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac p32_invhere :=
  eapply nextinv_here; [ reflexivity | red; psimpl_vals_goal ].

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac p32_invseek :=
  eapply NIStep; [reflexivity|reflexivity|];
  let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros s x XS;
  p32_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             p32_step_and_simplify XS
         | exec_stmt _ (N.iter _ _ _) _ _ => fail
         | _ => p32_step_and_simplify XS
         end;
  try match goal with |- nextinv _ _ _ _ (_ :: ?xs :: ?t) =>
    let t' := fresh t in generalize (xs::t); intro t'; clear t; rename t' into t
  end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac p32_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ p32_invseek; try p32_invhere | p32_invhere ].


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

(* TODO: prove these helper lemmas and add them to Picinae_theory or the coq standard lib *)
Lemma Nshiftr_land_ones_high:
  forall a n m, n > m -> (a << n) .& (N.ones m) = 0.
Proof. Admitted.

Lemma Nshiftr_land_high_nop:
  forall a b n m, n > m -> (a .| b << n) .& (N.ones m) = a .& (N.ones m).
Proof. Admitted.

Lemma Nland_low:
  forall a n, a < 2 ^ n -> a .& (N.ones n) = a.
Proof. Admitted.

Lemma xbits_lor_low:
  forall n m i j, i <= j -> n < 2 ^ i -> xbits (n .| m) i j = xbits m i j.
Proof. Admitted.

Lemma xbits_lor_high:
  forall n m i j, i <= j -> m = 0 \/ m >= 2 ^ j -> xbits (n .| m) i j = xbits n i j.
Proof. Admitted.

Lemma shiftr_0_or_high:
  forall x n m, m <= n -> x << n = 0 \/ x << n >= 2 ^ m.
Proof.
  intros. destruct x;[left;psimpl;lia | right].
  (* TODO: we need the N.shiftl monotonicity theorem *)
Admitted.

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
  unfold welltyped_p32_asm, p32_decode, assemble_insn, p32_decode_op, assemble_insn_op
    ; intros; destruct insn eqn:INSN;
  repeat match goal with 
  | [H: _ /\ _ |- _] => destruct H
  end.
  all: rewrite N.land_spec, N.ones_spec_low, Bool.andb_true_r; try lia;
       repeat rewrite N.lor_spec; repeat rewrite N.shiftl_spec_low; try lia;
       repeat rewrite Bool.orb_false_l; unfold N.testbit, Pos.testbit; try rewrite Bool.orb_true_l.
  all: repeat rewrite Nshiftr_land_high_nop; try lia; simpl (_ << _ .& _); psimpl.
  all: unfold p32_decode_binop_reg, p32_decode_binop_imm, p32_decode_cf_simm, p32_decode_imm,
         p32_decode_reg, p32_decode_memacc, p32_decode_simm.
  
  (* TODO: add this xbits simplification to psimpl *)
  all: unfold xnbits; repeat match goal with
  | [ |- context[xbits (?N .| ?M) ?i ?j] ] => rewrite (xbits_lor_high N M i j);[
        | solve [lia] | solve [apply shiftr_0_or_high; lia] ]
  | [ |- context[xbits (?N .| ?M) ?i ?j] ] => rewrite (xbits_lor_low N M i j); try solve [ psimpl; lia]
  | [ |- _ .| _ .| ?M < 2 ^ ?w ] => rewrite (lor_bound w);[|solve [lia]]
  | [ |- _ .| ?M < 2 ^ ?w ] => apply lor_bound; try solve [psimpl ; lia]
  (* TODO: prove the following case using the shiftr monotonicity theorem, the
    assert by lia ensures that this case is provable and the admit is reasonable *)
  | [ |- _ << ?S < 2 ^ ?w ] => assert (S + 3 <= w) by lia; admit 
  end.
  19: reflexivity.
  5: { rewrite xbits_shiftl, xbits_shiftl; simpl (_-_) in *; psimpl;
       rewrite xbits_0_low, xbits_0_low; try lia; reflexivity. }
  (* TODO: psimpl does not simplify the following goal as desired:
     PIL_li (xbits rd (1 - 1) (3 + 1 - 1)) (xbits i (4 - 4) (28 + 4 - 4)) = PIL_li rd i
  *)
  all: repeat rewrite xbits_shiftl; simpl (_-_) in *; psimpl.
  all: repeat rewrite xbits_0_low; try first [ lia | reflexivity | apply ofZ_bound | now rewrite toZ_ofZ].
Admitted.

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
  
Fixpoint p32_assemble (base_addr:N) (code:list (p32_asm)) : list (addr * N) :=
  match code with
  | nil => nil
  | insn :: t => match p32_assemble_insn_bytes insn with
    | b0 :: b1 :: b2 :: b3 :: nil =>
      (0 + base_addr, b0) :: (1 + base_addr, b1) :: 
      (2 + base_addr, b2) :: (3 + base_addr, b3) :: 
      (p32_assemble (4+base_addr) t)
    | _ => nil
    end
  end.
  
(* Definition program' := [PIL_li 0 0; PIL_addi 1 1 1; PIL_subi 2 2 1; PIL_beq 0 2 (-12)%Z]. *)
(* Compute p32_assemble 0x00100000 program'. *)

Fixpoint p32_assemble' (base_addr:N) (mem:addr->N) (code:list (p32_asm)) : addr -> N :=
  match code with
  | nil => mem
  | insn :: t => p32_assemble' (base_addr+4) (setmem 32 LittleE 4 mem base_addr (assemble_insn insn)) t
  end.

(* Compute p32_assemble' 0x00100000 (fun _ => 0) program'. *)

(* `assoc_list` turns a list pairing addresses and bytes into a function.
   If the address is not set then the default byte value is 0.
   
   Example use:
        
        Definition program := [PIL_li 0 0; PIL_InvalidI].
        assoc_list (p32_assemble 0x1000 program)
   
   Needing to have a default byte value is a limitation of needing to provide
   a concrete, rather than existentially quantified, value. We can ameliorate
   this in proofs by quantifying over memory values that exactly match the
   behavior of the concrete memory for the addresses in which the program
   is written.
*)

Fixpoint assoc_list (memlist:list (addr * N)) : addr -> N :=
  match memlist with
  | nil => fun _ => 0
  | (addr, b) :: t => fun a => if a == addr then b else assoc_list t a
  end.

Definition p32_assemble'' (base_addr:N) (code:list p32_asm) : addr -> N :=
  assoc_list (p32_assemble base_addr code).
  

Require Import String.
Require Import Ascii.
Require Import Recdef.
Require Import Program.
Require Import Lia.

Open Scope string.
Open Scope nat.
Definition newline :string := String "010" EmptyString.

Program Fixpoint N2str (n:nat) {measure n}: string :=
  (match n with
    | O => "0"
    | _ => 
       (if (N2str (n/10) =? "0")%string then EmptyString else N2str (n/10))
         ++ 
       (match n mod 10 with
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
         | _ => "ERROR"
       end)
  end)%nat .
Obligation 1. 
  enough (H: fst (Nat.divmod n 9 0 9) = (n / 10));[
  rewrite H; apply Nat.div_lt; lia| now unfold Nat.divmod]. Defined.
Next Obligation.
  enough (H: fst (Nat.divmod n 9 0 9) = (n / 10));[
  rewrite H; apply Nat.div_lt; lia| now unfold Nat.divmod]. Defined.
Next Obligation.
  repeat (split || lia). Defined.
Close Scope nat.

Fixpoint bytematches (l:list (addr * N)) : string :=
  match l with
  | nil => EmptyString
  | (a,b)::t => "  | " ++ (N2str (N.to_nat a)) ++ " => " ++ (N2str (N.to_nat b)) ++ newline
                 ++ (bytematches t)
  end.

Definition print_code (l:list (addr * N)) (name:string) :=
  "Definition " ++ name ++ " : addr -> N :=" ++ newline ++
  "fun a => match a with" ++ newline ++ (bytematches l)
  ++ "  | _ => 0" ++ newline ++ "end."
.
