From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcsncpy_armv8 wmemset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame.
From Grok.proofs Require Import wcslen_proof wcscpy_proof wmemset_proof.
From Grok.proofs Require wcsncat_proof.
Import ARM8Notations.
Open Scope N.

Definition wcsncpy_prog : program := updateall2 wcsncpy_armv8.wcsncpy_armv8 wmemset_armv8.wmemset_armv8.

Theorem wcsncpy_prog_welltyped: welltyped_prog arm8typctx wcsncpy_prog.
Proof.
  intros s a. unfold wcsncpy_prog, updateall2, updateall.
  destruct (wmemset_armv8.wmemset_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (wmemset_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply wcsncpy_armv8.welltyped.
Qed.

Lemma wcsncpy_prog_mono: ∀ prog, wcsncpy_armv8.wcsncpy_armv8 ⊆2 prog -> wmemset_armv8.wmemset_armv8 ⊆2 prog -> wcsncpy_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold wcsncpy_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* reads above the words written by wset are unaffected *)
Lemma wset_read_above: ∀ m e v k len a, e + 4 * N.of_nat k <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (wset m e v k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H0 H2. reflexivity.
  cbn [wset]. rewrite N.shiftl_mul_pow2. change (2^2) with 4.
  change (2^64) with 18446744073709551616 in *.
  rewrite getmem_setmem_below by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Definition ncpy_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp - 32 := x29] [Ⓠ sp - 24 := raddr] [Ⓠ sp - 16 := x19].

Definition wcsncpy_pre (sp mem d q n K : N) :=
  K <= n /\ n < 2^64 /\ wcs_nilfree mem q K /\ (K = n \/ mem Ⓓ[q + 4*K] = 0) /\
  32 <= sp /\ sp < 2^64 /\ d + 4*n <= sp - 32 /\ q + 4*K + 4 <= sp - 32 /\
  (q + 4*K + 4 <= d \/ d + 4*K <= q).

Definition wcsncpy_post (sp mem raddr d q n x19 x29 K : N) (s:store) :=
  s V_MEM64 = wset (wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat K)) (d + 4*K) 0 (N.to_nat (n - K)) /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x29 K : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* wcsncpy *)
    | 0x15fd70 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x15fd8c => Inv 1 (∃ k, k <= K /\ s R_X0 = d + 4*k /\ s R_X1 = q + 4*k /\ s R_X2 = n - k /\ s R_X19 = d /\
                         s V_MEM64 = wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat k) /\
                         s R_SP = sp - 32 /\ s R_X29 = sp - 32)
    | 0x15fd9c => Inv 1 (s R_X0 = d + 4*K /\ s R_X2 = n - K /\ s R_X19 = d /\
                         s V_MEM64 = wcpy (ncpy_frame sp mem raddr x19 x29) d q (N.to_nat K) /\
                         s R_SP = sp - 32 /\ s R_X29 = sp - 32)
    | 0x15fdb0 => Post 1 (wcsncpy_post sp mem raddr d q n x19 x29 K s)
    (* wmemset callee: X0 = d, X1 = q (fill value), X2 = n (count) *)
    | 0x160294 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x1602a4 => Inv 0 (∃ k, k <= n /\ s R_X3 = k /\ s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = wset mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x1602ac => Post 0 (s R_X0 = d /\ s V_MEM64 = wset mem d q (N.to_nat n) /\ s R_SP = sp /\ s R_X30 = raddr /\
                          s R_X19 = x19 /\ s R_X29 = x29)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 wcsncpy_prog invs.
  Definition invs0 := make_invs 0 wcsncpy_prog invs.
  Definition exits1 := make_exits 1 wcsncpy_prog invs.
  Definition invs1 := make_invs 1 wcsncpy_prog invs.
End Invariants.

Theorem wmemset_correct_in_wcsncpy:
  ∀ prog s t xs'
    (P: wcsncpy_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x160294, s))
    (MDL: models arm8typctx s),
  ∀ K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X29) K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X29) K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (c := s R_X1). set (n := s R_X2). set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X1: s R_X1 = c) by reflexivity. assert (X2: s R_X2 = n) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p c n x29 x19.
  eapply satisfies_all_pmono with (p1:=wcsncpy_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
    repeat arm8_step.
    exists 0. repeat split; try assumption; try lia.
  - destruct PRE as (k & KLE & X3 & X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    all: destruct (n =? k) eqn:E; try discriminate.
    + apply N.eqb_eq in E. rewrite <- E in MEM. repeat split; assumption.
    + apply N.eqb_neq in E. exists (k+1). repeat split; try assumption; try lia.
      all: first
        [ rewrite N.add_comm; apply N.mod_small; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wset];
          rewrite N2Nat.id, (N.add_comm p); reflexivity ].
Qed.
