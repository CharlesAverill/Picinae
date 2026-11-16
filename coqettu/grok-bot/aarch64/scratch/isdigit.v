From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import isdigit_armv8.
From Grok.lib Require Import GrokCommon GrokCtype.
Import ARM8Notations.
Open Scope N.

Theorem isdigit_welltyped: welltyped_prog arm8typctx isdigit_armv8.
Proof. Picinae_typecheck. Qed.

Definition isdigit_spec (c:N) : N :=
  let c32 := c mod 2^32 in if (48 <=? c32) && (c32 <=? 57) then 1 else 0.

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11ee64 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11ee70 => Post 0 (s R_X0 = isdigit_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition isdigit_exits := make_exits 0 isdigit_armv8 invs.
  Definition isdigit_invs := make_invs 0 isdigit_armv8 invs.
End Invariants.

Theorem isdigit_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PROG: isdigit_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee64, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (isdigit_invs sp mem raddr c) (isdigit_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=isdigit_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold isdigit_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isdigit_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  split; [|repeat split; assumption].
  apply (ls_test c 48 9); reflexivity.
Qed.
