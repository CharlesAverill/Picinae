From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memccpy_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr.
Import ARM8Notations.
Open Scope N.

Theorem memccpy_welltyped: welltyped_prog arm8typctx memccpy_armv8.
Proof. Picinae_typecheck. Qed.

(* the i-th source byte, as read by the copy, differs from c for all i < k *)
Definition bnc (m d s c:N) (k:N) := ∀ i, i < k -> getmem 64 LittleE 1 (bcp m d s (N.to_nat i)) (s + i) ≠ c.

Lemma bnc_succ: ∀ m d s c k, bnc m d s c k -> getmem 64 LittleE 1 (bcp m d s (N.to_nat k)) (s + k) ≠ c -> bnc m d s c (k+1).
Proof.
  unfold bnc. intros m d s c k NZ B i I.
  destruct (N.lt_ge_cases i k). apply NZ; assumption. replace i with k by lia. exact B.
Qed.

Lemma bnc_word: ∀ m d q c k w, msub 64 q d mod 8 = 0 ->
  getmem 64 LittleE 8 (bcp m d q (N.to_nat k)) (q + k) = w ->
  (∀ i, i < 8 -> byte w i ≠ c) -> bnc m d q c k -> bnc m d q c (k+8).
Proof.
  intros m d q c k w AL W B NZ i I. destruct (N.lt_ge_cases i k) as [L|G]. apply NZ, L.
  replace i with (k + (i-k)) by lia. replace (N.to_nat (k + (i-k))) with (N.to_nat k + N.to_nat (i-k))%nat by lia.
  replace (q + (k + (i-k))) with (q + N.of_nat (N.to_nat k + N.to_nat (i-k))) by lia.
  rewrite (bcp_word_read m d q w (N.to_nat k)) by (rewrite ?N2Nat.id; assumption || lia).
  rewrite N2Nat.id. apply B. lia.
Qed.

Lemma lxor_lt: ∀ a b n, a < 2^n -> b < 2^n -> N.lxor a b < 2^n.
Proof.
  intros a b n A B. enough (E: (N.lxor a b) mod 2^n = N.lxor a b) by (rewrite <- E; apply N.mod_lt; apply N.pow_nonzero; discriminate).
  apply N.bits_inj. intro i. destruct (N.lt_ge_cases i n) as [L|G].
  - apply N.mod_pow2_bits_low. exact L.
  - rewrite N.mod_pow2_bits_high, N.lxor_spec, (testbit_ge_bound a n i A G), (testbit_ge_bound b n i B G) by exact G. reflexivity.
Qed.

Lemma hasbyte_none: ∀ w c, w < 2^64 -> c < 2^8 ->
  N.land (N.land ((N.lxor w (c * 0x0101010101010101) + K8) mod 2^64)
                 (N.lxor (N.lxor w (c * 0x0101010101010101)) 18446744073709551615)) H8 = 0 ->
  ∀ i, i < 8 -> byte w i ≠ c.
Proof.
  intros w c W C T i I E.
  assert (X: N.lxor w (c * 0x0101010101010101) < 2^64).
  { apply lxor_lt. exact W. change (2^8) with 256 in C. lia. }
  change (N.lxor (N.lxor w (c * 0x0101010101010101)) 18446744073709551615) with
         (N.lnot (N.lxor w (c * 0x0101010101010101)) 64) in T.
  pose proof (haszero_none _ T i I) as H. apply H.
  change (byte (N.lxor w (c * 72340172838076673)) i) with (byte_of (N.lxor w (c * 72340172838076673)) i).
  rewrite byte_of_xor, byte_of_splat by assumption.
  change (byte_of w i) with (byte w i). rewrite E. apply N.lxor_nilpotent.
Qed.

Lemma land_mask8: ∀ x, x < 2^64 -> N.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x X. assert (E: x - x mod 8 = N.shiftl (N.shiftr x 3) 3).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^3) with 8.
    pose proof (N.div_mod x 8 ltac:(discriminate)). lia. }
  rewrite E. apply N.bits_inj. intro i. rewrite N.land_spec.
  destruct (N.lt_ge_cases i 3) as [L|G].
  - rewrite N.shiftl_spec_low by exact L.
    replace i with (N.of_nat (N.to_nat i)) by lia.
    assert (N.to_nat i < 3)%nat by lia.
    destruct (N.to_nat i) as [|[|[|]]]; try lia; apply Bool.andb_false_r.
  - rewrite N.shiftl_spec_high' by exact G. rewrite N.shiftr_spec'. replace (i - 3 + 3) with i by lia.
    destruct (N.lt_ge_cases i 64) as [L2|G2].
    + replace (N.testbit 18446744073709551608 i) with true. apply Bool.andb_true_r.
      symmetry. change 18446744073709551608 with (N.lxor (N.ones 64) 7).
      rewrite N.lxor_spec, N.ones_spec_low by lia.
      rewrite (testbit_ge_bound 7 3 i) by (reflexivity || lia). reflexivity.
    + rewrite (testbit_ge_bound x 64 i X G2). reflexivity.
Qed.

Lemma add_mod_inj: ∀ q k K, k < 2^64 -> K < 2^64 -> (q + k) mod 2^64 = (q + K) mod 2^64 -> k = K.
Proof.
  intros q k K Hk HK E.
  pose proof (N.div_mod (q+k) (2^64) ltac:(discriminate)) as A.
  pose proof (N.div_mod (q+K) (2^64) ltac:(discriminate)) as B.
  rewrite E in A. set (r := (q + K) mod 2^64) in *.
  set (a := (q+k)/2^64) in *. set (b := (q+K)/2^64) in *. change (2^64) with 18446744073709551616 in *. nia.
Qed.

Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Section Invariants.
  Variables (sp mem raddr d q c n : N).
  Definition c8 := c mod 2^8.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e128 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = c /\ s R_X3 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e140 => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X2 = c8 /\ s R_X3 = n - k /\ k <= n /\ n < 2^64 /\ d < 2^64 /\ q < 2^64 /\ s R_X0 = d ⊕ k /\ s R_X1 = q ⊕ k /\ bnc mem d q c8 k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e194 => Inv 0 (∃ k k0, msub 64 q d mod 8 = 0 /\ k0 <= k /\ (k - k0) mod 8 = 0 /\
                         k <= k0 + N.land (n - k0) 18446744073709551608 /\
                         s R_X2 = c8 /\ s R_X7 = q ⊕ (k0 + N.land (n - k0) 18446744073709551608) /\
                         s R_X9 = q ⊕ n /\ s R_X8 = c8 * 0x0101010101010101 /\ s R_X10 = K8 /\ k <= n /\ n < 2^64 /\ d < 2^64 /\ q < 2^64 /\ s R_X0 = d ⊕ k /\ s R_X1 = q ⊕ k /\ bnc mem d q c8 k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e1c0 => Inv 0 (∃ k, s R_X2 = c8 /\ s R_X3 = n - k /\ k <= n /\ n < 2^64 /\ d < 2^64 /\ q < 2^64 /\ s R_X0 = d ⊕ k /\ s R_X1 = q ⊕ k /\ bnc mem d q c8 k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e1e0 => Post 0 (∃ k, k <= n /\ bnc mem d q c8 k /\ s R_SP = sp /\ s R_X30 = raddr /\
                   ((k < n /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = c8 /\
                     s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\ s R_X0 = d ⊕ (k+1)) \/
                    (k = n /\ s V_MEM64 = bcp mem d q (N.to_nat n) /\ s R_X0 = 0)))
    | _ => NoInv
    end.
  Definition memccpy_exits := make_exits 0 memccpy_armv8 invs.
  Definition memccpy_invs := make_invs 0 memccpy_armv8 invs.
End Invariants.

Theorem memccpy_partial_correctness:
  ∀ prog s sp mem raddr d q c n t xs'
    (PROG: memccpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e128, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = c) (X3: s R_X3 = n),
  satisfies_all prog (memccpy_invs sp mem raddr d q c n) (memccpy_exits sp mem raddr d q c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memccpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memccpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X3 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memccpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  assert (C8: c8 c < 2^8) by (apply N.mod_lt; discriminate).
  assert (C32: c8 c < 2^32) by (eapply N.lt_le_trans; [exact C8 | discriminate]).
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & X3 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as D64. pose proof (MDL1 R_X1 64 eq_refl) as Q64.
    pose proof (MDL1 R_X3 64 eq_refl) as N64.
    rewrite X0 in D64. rewrite X1 in Q64. rewrite X3 in N64. simpl in D64, Q64, N64.
    repeat grok_step.
    + exists 0. apply N.eqb_eq in BC. split.
      { transitivity (msub 64 q d mod 2^3). rewrite msub_mod_pow2. reflexivity. apply xor_mod8. exact BC. }
      fold (c8 c). splits; rewrite ?N.add_0_r, ?N.sub_0_r, ?N.mod_small by assumption; try assumption; try reflexivity; try lia.
      intros i I. lia.
    + exists 0. fold (c8 c).
      splits; rewrite ?N.add_0_r, ?N.sub_0_r, ?N.mod_small by assumption; try assumption; try reflexivity; try lia.
      intros i I. lia.
  - destruct PRE as (k & AL & X2 & X3 & KN & N64 & D64 & Q64 & X0 & X1 & NC & MEM & SP & X30).
    repeat grok_step.
    all: repeat match goal with H: (_ =? _) = true |- _ => apply N.eqb_eq in H
                              | H: (_ =? _) = false |- _ => apply N.eqb_neq in H end.
    all: rewrite ?(N.mod_small (c8 c)) in * by exact C32.
    + (* aligned: enter word loop *)
      exists k, k. splits; try assumption; try reflexivity; try lia.
      all: first
        [ (transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL])
        | (rewrite N.sub_diag; reflexivity)
        | (rewrite ?N.shiftr_0_r, ?(N.mod_small (c8 c)), scast_small32 by (eapply N.lt_le_trans; [exact C8 | discriminate]);
           apply N.mod_small; change (2^8) with 256 in C8; lia)
        | modeq ].
    + (* n - k = 0: return NULL *)
      exists k. splits; try assumption; try lia. right. splits; try reflexivity; try lia.
      rewrite MEM. replace n with k by lia. reflexivity.
    + (* byte = c: return d+k+1 *)
      exists k. splits; try assumption; try lia. left. splits; try assumption; try lia.
      all: first [ (rewrite bcp_succ; reflexivity) | modeq ].
    + (* copy one byte, continue *)
      exists (k+1). splits; try assumption; try lia.
      all: first
        [ (transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL])
        | (rewrite msub_small by lia; lia)
        | (apply bnc_succ; assumption)
        | (rewrite bcp_succ; reflexivity)
        | modeq ].
  - destruct PRE as (k & k0 & AL & K0 & KM & KB & X2 & X7 & X9 & X8 & X10 & KN & N64 & D64 & Q64 & X0 & X1 & NC & MEM & SP & X30).
    repeat grok_step.
    all: repeat match goal with H: (_ =? _) = true |- _ => apply N.eqb_eq in H
                              | H: (_ =? _) = false |- _ => apply N.eqb_neq in H end.
    + (* end of whole words: byte loop *)
      exists k. splits; try assumption; try lia. rewrite msub_small by lia. reflexivity.
    + (* no byte = c in the word: copy it *)
      set (K := k0 + N.land (n - k0) 18446744073709551608) in *.
      assert (KK: K = k0 + ((n - k0) - (n - k0) mod 8)) by (unfold K; rewrite land_mask8 by (eapply N.le_lt_trans; [apply N.le_sub_l | exact N64]); reflexivity).
      assert (KNE: k ≠ K).
      { intro E. apply BC. idtac "KNE goal"; dump_ctx.
        assert (MS: ∀ x y, y <= x -> x < 2^64 -> x ⊖ y = x - y) by (intros; apply msub_small; assumption).
        transitivity (k - k0). { apply msub_small; first [exact K0 | eapply N.le_lt_trans; [exact KN | exact N64]]. }
        unfold K in E. clear - E. lia. }
      assert (K8': k + 8 <= K).
      { clear - KK KNE KB K0 KM KN.
        pose proof (N.div_mod (k - k0) 8 ltac:(discriminate)) as A1.
        pose proof (N.div_mod (n - k0) 8 ltac:(discriminate)) as A2.
        pose proof (N.mod_lt (n - k0) 8 ltac:(discriminate)).
        rewrite KM in A1. lia. }
      exists (k+8), k0. splits; try assumption; try reflexivity; try lia.
      all: first
        [ (transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL])
        | (replace (k + 8 - k0) with ((k - k0) + 1*8) by lia; rewrite N.Div0.mod_add; exact KM)
        | (apply (bnc_word mem d q (c8 c) k _ AL eq_refl); [|exact NC];
           apply hasbyte_none; [apply getmem_bound | exact C8 | exact BC0])
        | (rewrite bcp_word8 by exact AL; reflexivity)
        | modeq
        | idtac "UNSOLVED"; dump_ctx; admit ].
    + (* some byte = c: finish in the byte loop *)
      exists k. splits; try assumption; try lia. rewrite msub_small by lia. reflexivity.
  - destruct PRE as (k & X2 & X3 & KN & N64 & D64 & Q64 & X0 & X1 & NC & MEM & SP & X30).
    repeat grok_step.
    all: repeat match goal with H: (_ =? _) = true |- _ => apply N.eqb_eq in H
                              | H: (_ =? _) = false |- _ => apply N.eqb_neq in H end.
    all: rewrite ?(N.mod_small (c8 c)) in * by exact C32.
    + exists k. splits; try assumption; try lia. right. splits; try reflexivity; try lia.
      rewrite MEM. replace n with k by lia. reflexivity.
    + exists k. splits; try assumption; try lia. left. splits; try assumption; try lia.
      all: first [ (rewrite bcp_succ; reflexivity) | modeq ].
    + exists (k+1). splits; try assumption; try lia.
      all: first
        [ (rewrite msub_small by lia; lia)
        | (apply bnc_succ; assumption)
        | (rewrite bcp_succ; reflexivity)
        | modeq ].
Qed.
