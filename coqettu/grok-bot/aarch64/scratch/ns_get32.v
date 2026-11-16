From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ns_get32_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.

Theorem ns_get32_welltyped: welltyped_prog arm8typctx ns_get32_armv8.
Proof. Picinae_typecheck. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x143f5c => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x143f64 => Post 0 (s R_X0 = getmem 64 BigE 4 mem c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ns_get32_exits := make_exits 0 ns_get32_armv8 invs.
  Definition ns_get32_invs := make_invs 0 ns_get32_armv8 invs.
End Invariants.

Theorem ns_get32_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: ns_get32_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x143f5c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (ns_get32_invs sp mem raddr c d) (ns_get32_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ns_get32_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ns_get32_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ns_get32_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: rewrite (getmem_revbytes 64 BigE LittleE) by discriminate.
  replace (getmem 64 LittleE 1 mem c) with (getmem 64 LittleE 4 mem c mod 2^(1*8)) by (rewrite getmem_mod; reflexivity).
  replace (getmem 64 LittleE 2 mem c) with (getmem 64 LittleE 4 mem c mod 2^(2*8)) by (rewrite getmem_mod; reflexivity).
  replace (getmem 64 LittleE 3 mem c) with (getmem 64 LittleE 4 mem c mod 2^(3*8)) by (rewrite getmem_mod; reflexivity).
  pose proof (getmem_bound 64 LittleE 4 mem c) as YB.
  apply N.bits_inj; intro i. destruct (N.lt_ge_cases i (4*8)) as [LT|GE].
  - rev_low (getmem 64 LittleE 4 mem c) 4.
  - rewrite revbytes_high by assumption.
    match goal with |- N.testbit ?t i = _ =>
      let e := reify_bx (getmem 64 LittleE 4 mem c) t in change t with (bden (getmem 64 LittleE 4 mem c) e);
      apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; cbn in GE; lia]
    end.
Qed.
