From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import strncmp_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Section Invariants.
  Variables (sp mem raddr p q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f110 => Inv 0 (s R_X0 = p /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f11c => Inv 0 (∃ k, n < 2^64 /\ 0 < n /\ k < n /\ s R_X0 = p /\ s R_X1 = q /\
                         s R_X2 = n - 1 /\ s R_X3 = k /\
                         mem_eq mem p q k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f140 => Post 0 ((s R_X0 = 0 /\ n = 0 \/
                          (∃ k, k < n /\ mem_eq mem p q k /\ nilfree mem p k /\
                                (mem Ⓑ[p + k] ≠ mem Ⓑ[q + k] \/ mem Ⓑ[p + k] = 0 \/ k = n - 1) /\
                                s R_X0 = msub 32 (mem Ⓑ[p + k]) (mem Ⓑ[q + k]))) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 strncmp_armv8 invs.
  Definition invs0 := make_invs 0 strncmp_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx strncmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem strncmp_correct:
  ∀ prog s sp mem raddr p q n t xs'
    (PROG: strncmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f110, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (invs0 sp mem raddr p q n) (exits sp mem raddr p q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strncmp_armv8). exact PROG.
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
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    end.
    + split; [|splits; assumption]. left. split; [reflexivity|assumption].
    + exists 0. splits; try assumption; try reflexivity; try lia.
      all: first [ (rewrite msub_small by lia; reflexivity) | apply mem_eq_0 | apply nilfree_0 ].
  - destruct PRE as (k & N64 & NPOS & KLT & X0 & X1 & X2 & X3 & EQ & NF & MEM & SP & X30).
    repeat grok_step.
  all: repeat match goal with
    | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
    | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
    end.
    all: first
      [ exists (k+1); splits; try reflexivity; try assumption; try lia;
        first [ (rewrite N.mod_small by lia; lia) | (apply mem_eq_succ; assumption)
              | (apply nilfree_succ; assumption) ]
      | split; [|splits; reflexivity || assumption]; right; exists k;
        splits; try assumption; try reflexivity; try lia ].
Qed.

(* The returned int is the difference of the two unsigned chars at k. *)
Theorem strncmp_result_value:
  ∀ m a b, toZ 32 (msub 32 (m Ⓑ[a]) (m Ⓑ[b])) = (Z.of_N (m Ⓑ[a]) - Z.of_N (m Ⓑ[b]))%Z.
Proof. intros. apply msub32_bytes_toZ; apply byte_lt8. Qed.
