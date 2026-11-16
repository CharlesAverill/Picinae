(* System V AMD64 ABI helpers shared by the musl x86_64 proofs.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

(* Syntactic closers: never unfold (memory) terms. *)
Ltac sreflexivity := match goal with |- ?a = ?b => constr_eq a b; reflexivity end.
Ltac sassumption := match goal with H: ?T |- ?G => constr_eq T G; exact H end.

(* The callee-saved general-purpose registers of the SysV AMD64 ABI (RSP is
   handled separately by each contract). *)
Definition callee_saved_regs := [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15].

(* s agrees with s0 on every callee-saved register. *)
Definition callee_saved_eq (s0 s:store) :=
  s R_RBX = s0 R_RBX /\ s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\
  s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Lemma callee_saved_eq_refl: forall s, callee_saved_eq s s.
Proof. repeat split. Qed.

Lemma callee_saved_eq_In:
  forall s0 s, callee_saved_eq s0 s -> forall r, In r callee_saved_regs -> s r = s0 r.
Proof.
  intros s0 s (B & P & A & C & D & E) r IN.
  repeat destruct IN as [<-|IN]; assumption || destruct IN.
Qed.

(* A fully applied 8-bit broadcast: the eight bytes of b * 0x0101010101010101
   are all b, for every byte b. *)
Definition bcast8 (b:N) := b * 0x0101010101010101.

Lemma bcast8_bytes_check:
  List.forallb (fun b => List.forallb (fun k =>
      N.eqb (xbits (bcast8 (N.of_nat b)) (8 * N.of_nat k) (8 * N.of_nat k + 8)) (N.of_nat b))
    (seq 0 8)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bcast8_byte:
  forall b k, b < 256 -> k < 8 -> xbits (bcast8 b) (8*k) (8*k+8) = b.
Proof.
  intros b k B K.
  pose proof bcast8_bytes_check as C.
  rewrite List.forallb_forall in C.
  specialize (C (N.to_nat b)). rewrite List.in_seq in C.
  specialize (C ltac:(lia)). rewrite List.forallb_forall in C.
  specialize (C (N.to_nat k)). rewrite List.in_seq in C.
  specialize (C ltac:(lia)). rewrite !N2Nat.id in C. apply N.eqb_eq, C.
Qed.

Lemma bcast8_lt: forall b, b < 256 -> bcast8 b < 2^64.
Proof. unfold bcast8. intros. lia. Qed.

(* Every one of the L bytes of b * K is b, for all bytes b (checked by
   evaluation for one constant K and length L). *)
Definition rep_ok (K L:N) :=
  List.forallb (fun b => List.forallb (fun k =>
      N.eqb (xbits (N.of_nat b * K) (8 * N.of_nat k) (8 * N.of_nat k + 8)) (N.of_nat b))
    (seq 0 (N.to_nat L))) (seq 0 256).

Lemma rep_ok_xbits:
  forall K L, rep_ok K L = true ->
  forall b k, b < 256 -> k < L -> xbits (b * K) (8*k) (8*k+8) = b.
Proof.
  intros K L C b k B K'.
  unfold rep_ok in C. rewrite List.forallb_forall in C.
  specialize (C (N.to_nat b)). rewrite List.in_seq in C.
  specialize (C ltac:(lia)). rewrite List.forallb_forall in C.
  specialize (C (N.to_nat k)). rewrite List.in_seq in C.
  specialize (C ltac:(lia)). rewrite !N2Nat.id in C. apply N.eqb_eq, C.
Qed.

(* Callee-saved registers are untouched by updates of other registers. *)
Ltac callee_saved_tac :=
  lazymatch goal with CS: callee_saved_eq ?s0 ?s |- callee_saved_eq ?s0 _ =>
    let B := fresh in let P := fresh in let A := fresh in
    let C := fresh in let D := fresh in let E := fresh in
    destruct CS as (B & P & A & C & D & E);
    repeat split; rewrite ?update_frame by discriminate; sassumption
  end.

Lemma lnot_1_1: N.lnot 1 1 = 0. Proof. reflexivity. Qed.
Lemma lnot_0_1: N.lnot 0 1 = 1. Proof. reflexivity. Qed.

(* Normalize branch conditions in the (memory-free) hypotheses: case on every
   boolean test, discarding contradictory branches at once (so the number of
   goals does not explode), then turn the tests into propositions. *)
Ltac bc_norm :=
  repeat match goal with
  | H: ?T |- _ =>
      lazymatch T with context [V_MEM64] => fail | context [setmem] => fail | _ =>
      match T with context [if ?b then _ else _] =>
        lazymatch type of b with bool =>
        lazymatch b with true => fail | false => fail | _ =>
        let E := fresh "BC" in let bb := fresh "bb" in
        remember b as bb eqn:E in H; destruct bb; symmetry in E;
        cbn [N.lor N.land N.lxor Pos.lor Pos.land Pos.lxor] in H;
        rewrite ?lnot_1_1, ?lnot_0_1 in H;
        try discriminate H
        end end end end
  end;
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

(* A variant of Picinae's ISA_symbolic_interp that also case-splits an If
   nested inside a Seq (as the lifter emits for REP-prefixed string
   instructions: Seq (Seq (If ..) ..) (Jmp self)). *)
Ltac x64_symbolic_interp :=
  let c := fresh "c" in let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros c s x XS;
  ISA_step_and_simplify XS;
  repeat lazymatch type of XS with
         | reset_temps _ s = _ /\ x = _ =>
             try clear c; destruct XS as [XS ?]; subst x;
             try (let rt := fresh in set (rt := reset_temps _ _) at 1;
                  psimpl_hyp rt; subst rt;
                  rewrite XS; clear XS; try clear s)
         | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (Seq (if ?c then _ else _) _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (Seq (Seq (if ?c then _ else _) _) _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
         | _ => ISA_step_and_simplify XS
         end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  repeat match goal with [ x:N |- _ ] => clear x end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

Ltac x64_step' :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ eapply NIStep; [reflexivity|reflexivity|]; x64_symbolic_interp; try ISA_invhere
        | ISA_invhere ].

(* Split a conjunction, closing callee-saved conjuncts with callee_saved_tac
   and the others by reflexivity or assumption; leaves the rest. *)
Ltac conj_tac :=
  repeat match goal with
  | |- callee_saved_eq _ _ => callee_saved_tac
  | |- _ /\ _ => split
  end;
  try (first [sreflexivity | sassumption]).

Lemma callee_saved_eq_trans:
  forall a b c, callee_saved_eq a b -> callee_saved_eq b c -> callee_saved_eq a c.
Proof.
  intros a b c (B1&P1&A1&C1&D1&E1) (B2&P2&A2&C2&D2&E2).
  repeat split; congruence.
Qed.

(* Clear every hypothesis that mentions memory or other non-arithmetic
   structure, so that lia never sees (and unfolds) a memory term. *)
Ltac arith_only :=
  repeat match goal with H: ?T |- _ =>
    lazymatch T with
    | context [setmem] => clear H | context [getmem] => clear H
    | context [V_MEM64] => clear H | context [models] => clear H
    | context [overlap] => clear H | context [exec_prog] => clear H
    | context [startof] => clear H
    end end.

Ltac mlia64 := arith_only; unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
