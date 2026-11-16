From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ldiv_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Theorem ldiv_welltyped: welltyped_prog arm8typctx ldiv_armv8.
Proof. Picinae_typecheck. Qed.

(* Quotient and remainder as the machine computes them (sdiv gives 0 for a
   zero divisor; msub). *)
Definition ldiv_q (a b:N) : N := if b =? 0 then 0 else sbop2 Z.quot 64 a b.
Definition ldiv_r (a b:N) : N := msub 64 a (ldiv_q a b * b).

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15d394 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15d3a0 => Post 0 (s R_X0 = ldiv_q c d /\ s R_X1 = ldiv_r c d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ldiv_exits := make_exits 0 ldiv_armv8 invs.
  Definition ldiv_invs := make_invs 0 ldiv_armv8 invs.
End Invariants.

Theorem ldiv_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: ldiv_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15d394, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (ldiv_invs sp mem raddr c d) (ldiv_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ldiv_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ldiv_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ldiv_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: unfold ldiv_r, ldiv_q; rewrite BC; splits; try reflexivity; try assumption.
  pose proof (MDL1 R_X0 64 eq_refl) as C64. rewrite X0 in C64.
  rewrite N.mul_0_l, msub_0_r. symmetry. apply N.mod_small. exact C64.
Qed.

