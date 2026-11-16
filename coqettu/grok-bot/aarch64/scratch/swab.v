From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import swab_armv8.
From Grok.lib Require Import GrokCommon GrokSigned.
Import ARM8Notations.
Open Scope N.

Theorem swab_welltyped: welltyped_prog arm8typctx swab_armv8.
Proof. Picinae_typecheck. Qed.

Theorem swab_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates swab_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem swab_preserves_x30:
  forall_endstates swab_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* swb m q d k: memory after k iterations of the swab loop: for i < k,
   dest[2i] := src[2i+1] and dest[2i+1] := src[2i], both bytes of a pair
   read before either is written (as the binary does); addresses are
   taken mod 2^64 by getmem/setmem. *)
Fixpoint swb (m:memory) (q d:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := swb m q d k' in let i := N.of_nat k' in
            m' [Ⓑ d + 2*i := m' Ⓑ[1 + q + 2*i]] [Ⓑ 1 + d + 2*i := m' Ⓑ[q + 2*i]]
  end.

Lemma toZ_sub2k: ∀ n k, n < 2^64 -> (k = 0 \/ Z.le (2 * Z.of_N k) (toZ 64 n)) ->
  toZ 64 (n ⊖ 2*k) = Z.sub (toZ 64 n) (2 * Z.of_N k).
Proof.
  intros n k N K. destruct K as [K|K].
  - subst k. rewrite N.mul_0_r, msub_0_r, N.mod_small by assumption. lia.
  - rewrite toZ64 in K by assumption. destruct (N.ltb_spec n (2^63)); [|lia].
    rewrite msub_small by lia. rewrite !toZ64 by lia.
    destruct (N.ltb_spec n (2^63)), (N.ltb_spec (n - 2*k) (2^63)); lia.
Qed.

Section Invariants.
  Variables (sp mem raddr q d n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f9d8 => Inv 0 (s R_X0 = q /\ s R_X1 = d /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f9f4 => Inv 0 (∃ k, n < 2^64 /\ (k = 0 \/ Z.le (2 * Z.of_N k) (toZ 64 n)) /\
                         s R_X0 = q ⊕ 2*k /\ s R_X1 = d ⊕ 2*k /\ s R_X2 = q ⊕ n /\
                         s V_MEM64 = swb mem q d (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fa00 => Post 0 (s V_MEM64 = swb mem q d (Z.to_nat (Z.div (toZ 64 n) 2)) /\
                          s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition swab_exits := make_exits 0 swab_armv8 invs.
  Definition swab_invs := make_invs 0 swab_armv8 invs.
End Invariants.

Theorem swab_partial_correctness:
  ∀ prog s sp mem raddr q d n t xs'
    (PROG: swab_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f9d8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = q) (X1: s R_X1 = d) (X2: s R_X2 = n),
  satisfies_all prog (swab_invs sp mem raddr q d n) (swab_exits sp mem raddr q d n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=swab_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold swab_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply swab_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as Q64. rewrite X0 in Q64. simpl in Q64.
    pose proof (MDL1 R_X1 64 eq_refl) as D64. rewrite X1 in D64. simpl in D64.
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    exists 0. repeat split; try assumption; try (left; reflexivity).
    all: try rewrite X1; rewrite N.mul_0_r, N.add_0_r; symmetry; apply N.mod_small; assumption.
  - destruct PRE as (k & N64 & KB & X0 & X1 & X2 & MEM & SP & X30).
    repeat arm8_step.
    all: assert (XB: n ⊖ 2*k < 2^64) by (unfold msub; apply N.mod_upper_bound; discriminate).
    all: pose proof (toZ_sub2k n k N64 KB) as TS.
    + apply (gt1_test _ XB) in BC. rewrite TS in BC.
      assert (E: Z.to_nat (Z.div (toZ 64 n) 2) = N.to_nat k) by (Z.div_mod_to_equations; lia).
      rewrite E. repeat split; assumption.
    + assert (GT: ~ Z.le (toZ 64 (n ⊖ 2*k)) 1) by (rewrite <- (gt1_test _ XB), BC; discriminate).
      rewrite TS in GT. exists (k+1). repeat split.
      all: first
        [ assumption | reflexivity
        | right; lia
        | f_equal; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [swb]; rewrite ?N2Nat.id; reflexivity ].
Qed.
