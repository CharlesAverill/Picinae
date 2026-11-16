From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wcsncmp_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

(* The first k wide characters at p and q are equal and non-zero. *)
Definition wmem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] = m Ⓓ[q + 4*i] /\ m Ⓓ[p + 4*i] ≠ 0.

Lemma wmem_eq_0: ∀ m p q, wmem_eq m p q 0.
Proof. unfold wmem_eq. intros. lia. Qed.

Lemma wmem_eq_succ: ∀ m p q k, wmem_eq m p q k -> m Ⓓ[p + 4*k] = m Ⓓ[q + 4*k] -> m Ⓓ[p + 4*k] ≠ 0 -> wmem_eq m p q (k+1).
Proof.
  unfold wmem_eq. intros m p q k E B Z i I.
  destruct (N.lt_ge_cases i k). apply E; assumption. replace i with k by lia. split; assumption.
all: dump_ctx. all: admit. Admitted.

(* wchar_t is unsigned int on aarch64: -1 (as a 32-bit int) if a < b, else 1. *)
Definition wcmp_result (a b:N) : N := if a <? b then 2^32 - 1 else if b <? a then 1 else 0.


Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15fd34 => Inv 0 (∃ k, n < 2^64 /\ k <= n /\ s R_X0 = p ⊕ 4*k /\ s R_X1 = q ⊕ 4*k /\
                         s R_X2 = n - k /\ wmem_eq mem p q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fd64 => Post 0 ((s R_X0 = 0 /\ wmem_eq mem p q n \/
                          (∃ k, k < n /\ wmem_eq mem p q k /\ (mem Ⓓ[p + 4*k] ≠ mem Ⓓ[q + 4*k] \/ mem Ⓓ[p + 4*k] = 0) /\
                                s R_X0 = wcmp_result (mem Ⓓ[p + 4*k]) (mem Ⓓ[q + 4*k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 wcsncmp_armv8 invs.
  Definition invs0 := make_invs 0 wcsncmp_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx wcsncmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wcsncmp_correct:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: wcsncmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fd34, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (invs0 sp mem raddr p q n) (exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcsncmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step.
    pose proof (MDL R_X0 64 eq_refl) as P64. pose proof (MDL R_X1 64 eq_refl) as Q64.
    pose proof (MDL R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X1 in Q64. rewrite X2 in N64. simpl in P64, Q64, N64.
    exists 0. rewrite N.mul_0_r, !N.add_0_r, N.sub_0_r, !N.mod_small by assumption.
    repeat split; try assumption; try lia. all: try apply wmem_eq_0.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply welltyped'. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (k & N64 & KLE & X0 & X1 & X2 & EQ & MEM & SP & X30).
  repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    | H: (_ <=? _) = true |- _ => apply N.leb_le in H
    | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
    end.
  1: { split; [|repeat split; assumption]. left. split. reflexivity. replace n with k by lia. exact EQ. }
  all: first
    [ exists (k+1); splits; try reflexivity; try assumption; try lia;
      first [ (f_equal; lia) | (rewrite msub_small by lia; lia)
            | (apply wmem_eq_succ; [assumption | lia | assumption]) ]
    | split; [|repeat split; assumption]; right; exists k; splits; try assumption; try lia;
      first [ (right; assumption) | (left; lia) |
        (unfold wcmp_result;
         repeat match goal with |- context [?a <? ?b] => destruct (a <? b) eqn:?
                              | |- context [?a =? ?b] => destruct (a =? b) eqn:? end;
         rewrite ?N.ltb_lt, ?N.ltb_ge, ?N.eqb_eq, ?N.eqb_neq in *; lia) ] ].
Qed.
