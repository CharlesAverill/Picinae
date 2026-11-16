From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import rand_r_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.

Theorem rand_r_welltyped: welltyped_prog arm8typctx rand_r_armv8.
Proof. Picinae_typecheck. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x147f38 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x147f78 => Post 0 (s R_X0 = 0 /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition rand_r_exits := make_exits 0 rand_r_armv8 invs.
  Definition rand_r_invs := make_invs 0 rand_r_armv8 invs.
End Invariants.

Theorem rand_r_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: rand_r_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x147f38, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (rand_r_invs sp mem raddr c d) (rand_r_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=rand_r_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold rand_r_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply rand_r_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: dump_ctx. all: admit.
Admitted.
