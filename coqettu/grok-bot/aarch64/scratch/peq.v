From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import pthread_equal_armv8 sigismember_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokSig.
Import ARM8Notations.
Open Scope N.

Theorem pthread_equal_welltyped: welltyped_prog arm8typctx pthread_equal_armv8.
Proof. Picinae_typecheck. Qed.
Theorem sigismember_welltyped: welltyped_prog arm8typctx sigismember_armv8.
Proof. Picinae_typecheck. Qed.

Definition sigismember_spec (mem p sig : N) : N :=
  let s := msub 32 sig 1 in if s <? 64 then N.land (N.shiftr (getmem 64 LittleE 8 mem p) s) 1 else 0.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x162f00 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x162f08 => Post 0 (s R_X0 = (if c =? d then 1 else 0) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition peq_exits := make_exits 0 pthread_equal_armv8 invs.
  Definition peq_invs := make_invs 0 pthread_equal_armv8 invs.
  Definition sinvs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x152330 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x152348 => Post 0 (s R_X0 = sigismember_spec mem c d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition sim_exits := make_exits 0 sigismember_armv8 sinvs.
  Definition sim_invs := make_invs 0 sigismember_armv8 sinvs.
End Invariants.

Theorem pthread_equal_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: pthread_equal_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x162f00, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (peq_invs sp mem raddr c d) (peq_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=pthread_equal_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold peq_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply pthread_equal_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
Qed.

Theorem sigismember_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: sigismember_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x152330, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (sim_invs sp mem raddr c d) (sim_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=sigismember_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold sim_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigismember_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: unfold sigismember_spec; pose proof (msub32_1 d) as M.
  - assert (S: msub 32 d 1 < 64).
    { destruct (N.eqb_spec (d mod 2^32) 64) as [E|E].
      - rewrite M, E. cbn. lia.
      - destruct (N.leb_spec 63 (msub 32 d 1)) as [L|L]; [discriminate BC | lia]. }
    rewrite (proj2 (N.ltb_lt _ _) S), msub6_32, (N.mod_small _ (2^6)) by exact S.
    change (N.land (N.shiftr ?x ?y) 1) with (N.land (N.shiftr x y) (N.ones 1)).
    rewrite N.land_ones. reflexivity.
  - destruct (N.eqb_spec (d mod 2^32) 64) as [E|E]; [discriminate BC|].
    destruct (N.leb_spec 63 (msub 32 d 1)) as [L|L]; [|discriminate BC].
    assert (S: 64 <= msub 32 d 1).
    { destruct (N.eqb_spec (d mod 2^32) 0) as [Z|Z]; rewrite M in *; lia. }
    rewrite (proj2 (N.ltb_ge _ _) S). reflexivity.
Qed.
