From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemchr_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* No wide character among the first k at p equals c. *)
Definition wnomatch (m:memory) (p:addr) (c:N) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ c.

Lemma wnomatch_0: ∀ m p c, wnomatch m p c 0.
Proof. unfold wnomatch. intros. lia. Qed.

Lemma wnomatch_succ: ∀ m p c k, wnomatch m p c k -> m Ⓓ[p + 4*k] ≠ c -> wnomatch m p c (k+1).
Proof.
  unfold wnomatch. intros m p c k NM B i I.
  destruct (N.lt_ge_cases i k). apply NM; assumption. replace i with k by lia. exact B.
Qed.

Section Invariants.
  Variables (sp mem raddr p c n : N).
  Definition c32 := c mod 2^32.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x1601d0 => Inv 0 (s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1601d8 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X2 = n - k /\ s R_X1 = c /\
                         wnomatch mem p c32 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1601f4 => Post 0 (((∃ k, k < n /\ s R_X0 = p ⊕ 4*k /\ wnomatch mem p c32 k /\ mem Ⓓ[p + 4*k] = c32) \/
                           (s R_X0 = 0 /\ wnomatch mem p c32 n)) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 wmemchr_armv8 invs.
  Definition invs0 := make_invs 0 wmemchr_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx wmemchr_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemchr_correct:
  ∀ prog s sp mem raddr p c n t xs'
    (PROG: wmemchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1601d0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X2: s R_X2 = n),
  satisfies_all prog (invs0 sp mem raddr p c n) (exits sp mem raddr p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemchr_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply welltyped'. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X2 in N64. simpl in P64, N64.
    repeat arm8_step.
    exists 0.
    repeat split; try assumption; try lia. apply wnomatch_0.
  - destruct PRE as (k & N64 & KLE & X0 & X2 & X1 & NM & MEM & SP & X30).
    pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
    repeat arm8_step.
    + apply N.eqb_eq in BC. split; [|repeat split; assumption].
      right. split. reflexivity. replace n with k by lia. exact NM.
    + apply N.eqb_eq in BC0. apply N.eqb_neq in BC. split; [|repeat split; assumption].
      left. exists k. repeat split; try assumption; try exact BC0; lia.
    + apply N.eqb_neq in BC0, BC. exists (k+1).
      repeat split; try assumption; try lia.
      all: first [ (f_equal; lia) | (rewrite msub_small by lia; lia) | (apply wnomatch_succ; assumption) ].
Qed.
