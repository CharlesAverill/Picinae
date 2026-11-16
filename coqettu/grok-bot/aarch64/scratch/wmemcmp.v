From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemcmp_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* The first k wide characters at p and q are equal. *)
Definition wmem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] = m Ⓓ[q + 4*i].

Lemma wmem_eq_0: ∀ m p q, wmem_eq m p q 0.
Proof. unfold wmem_eq. intros. lia. Qed.

Lemma wmem_eq_succ: ∀ m p q k, wmem_eq m p q k -> m Ⓓ[p + 4*k] = m Ⓓ[q + 4*k] -> wmem_eq m p q (k+1).
Proof.
  unfold wmem_eq. intros m p q k E B i I.
  destruct (N.lt_ge_cases i k). apply E; assumption. replace i with k by lia. exact B.
Qed.

(* wchar_t is unsigned int on aarch64: -1 (as a 32-bit int) if a < b, else 1. *)
Definition wcmp_result (a b:N) : N := if a <? b then 2^32 - 1 else 1.

Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x1601f8 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X1 = q ⊕ 4*k /\
                         s R_X2 = n - k /\ wmem_eq mem p q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160228 => Post 0 ((s R_X0 = 0 /\ wmem_eq mem p q n \/
                          (∃ k, k < n /\ wmem_eq mem p q k /\ mem Ⓓ[p + 4*k] ≠ mem Ⓓ[q + 4*k] /\
                                s R_X0 = wcmp_result (mem Ⓓ[p + 4*k]) (mem Ⓓ[q + 4*k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 wmemcmp_armv8 invs.
  Definition invs0 := make_invs 0 wmemcmp_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx wmemcmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemcmp_correct:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: wmemcmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1601f8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (invs0 sp mem raddr p q n) (exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemcmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step.
    pose proof (MDL R_X0 64 eq_refl) as P64. pose proof (MDL R_X1 64 eq_refl) as Q64.
    pose proof (MDL R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X1 in Q64. rewrite X2 in N64. simpl in P64, Q64, N64.
    exists 0. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r, !N.mod_small by assumption.
    repeat split; try assumption; try lia. apply wmem_eq_0.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply welltyped'. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (k & N64 & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
  repeat arm8_step.
  - apply N.eqb_eq in BC. split; [|repeat split; assumption].
    left. split. reflexivity. replace n with k by lia. exact EQ.
  - apply N.eqb_eq in BC0. apply N.eqb_neq in BC. exists (k+1).
    repeat split; try assumption; try lia.
    all: first [ (f_equal; lia) | (rewrite msub_small by lia; lia) | (apply wmem_eq_succ; assumption) ].
  - apply N.eqb_neq in BC0, BC. apply N.leb_le in BC1. split; [|repeat split; assumption].
    right. exists k. repeat split; try assumption; try lia.
    unfold wcmp_result. rewrite (proj2 (N.ltb_ge _ _)) by lia. reflexivity.
  - apply N.eqb_neq in BC0, BC. apply N.leb_gt in BC1. split; [|repeat split; assumption].
    right. exists k. repeat split; try assumption; try lia.
    unfold wcmp_result. rewrite (proj2 (N.ltb_lt _ _)) by lia. reflexivity.
Qed.
