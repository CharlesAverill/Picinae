From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemmove_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Theorem wmemmove_welltyped: welltyped_prog arm8typctx wmemmove_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemmove_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wmemmove_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wmemmove_preserves_x30:
  forall_endstates wmemmove_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* Forward copy: words 0..k-1, in increasing order, each read from the
   current memory (addresses mod 2^64 via getmem/setmem). *)
Fixpoint wcpy (m:memory) (d q:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := wcpy m d q k' in m' [Ⓓ d + (N.of_nat k' << 2) := m' Ⓓ[q + (N.of_nat k' << 2)]]
  end.

(* Backward copy of an n-word array: after k steps, words n-1, ..., n-k
   have been copied (in that order), each read from the current memory. *)
Fixpoint bcpy (m:memory) (d q n:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := bcpy m d q n k' in let i := n - N.of_nat k' - 1 in
            m' [Ⓓ d + (i << 2) := m' Ⓓ[q + (i << 2)]]
  end.

Definition wmemmove_spec (m:memory) (d q n:N) : memory :=
  if d =? q then m
  else if msub 64 d q <? (n << 2) mod 2^64 then bcpy m d q n (N.to_nat n)
  else wcpy m d q (N.to_nat n).

Lemma addr_shl2_mod: ∀ x a, (x + ((a mod 2^62) << 2)) mod 2^64 = (x + (a << 2)) mod 2^64.
Proof.
  intros. rewrite !N.shiftl_mul_pow2.
  set (h := a / 2^62). set (r := a mod 2^62).
  assert (A: a = 2^62 * h + r) by (apply N.div_mod; discriminate).
  rewrite A. replace (x + (2^62 * h + r) * 2^2) with ((x + r * 2^2) + h * 2^64) by lia.
  rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma msub62_1: ∀ j, 1 <= j -> msub 62 j 1 = (j - 1) mod 2^62.
Proof.
  intros j J. unfold msub. rewrite (N.mod_small 1) by reflexivity.
  replace (j + (2^62 - 1)) with ((j - 1) + 1 * 2^62) by lia. apply N.Div0.mod_add.
Qed.

Lemma bk_addr: ∀ x j, 1 <= j -> (x + (msub 62 j 1 << 2)) mod 2^64 = (x + ((j - 1) << 2)) mod 2^64.
Proof. intros. rewrite msub62_1 by assumption. apply addr_shl2_mod. Qed.

Section Invariants.
  Variables (sp mem raddr d q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x16024c => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160274 => Inv 0 (∃ j, j <= n /\ n < 2^64 /\ d ≠ q /\ msub 64 d q < (n << 2) mod 2^64 /\
                         s R_X0 = d /\ s R_X1 = q /\ s R_X2 = j /\
                         s V_MEM64 = bcpy mem d q n (N.to_nat (n - j)) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160288 => Inv 0 (∃ k, k <= n /\ n < 2^64 /\ d ≠ q /\ (n << 2) mod 2^64 <= msub 64 d q /\
                         s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s R_X3 = k /\
                         s V_MEM64 = wcpy mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160278 => Post 0 (s R_X0 = d /\ s V_MEM64 = wmemmove_spec mem d q n /\
                          s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wmemmove_exits := make_exits 0 wmemmove_armv8 invs.
  Definition wmemmove_invs := make_invs 0 wmemmove_armv8 invs.
End Invariants.

Theorem wmemmove_partial_correctness:
  ∀ prog s sp mem raddr d q n t xs'
    (PROG: wmemmove_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x16024c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (wmemmove_invs sp mem raddr d q n) (wmemmove_exits sp mem raddr d q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemmove_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wmemmove_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemmove_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    + repeat split; try assumption; try reflexivity.
      unfold wmemmove_spec. rewrite BC. assumption.
    + apply N.eqb_neq in BC. apply N.leb_le in BC0. exists 0.
      repeat split; try assumption; try lia.
    + apply N.eqb_neq in BC. apply N.leb_gt in BC0. exists n.
      repeat split; try assumption; try lia.
      rewrite N.sub_diag. assumption.
  - destruct PRE as (j & JLE & N64 & DQ & BW & X0 & X1 & X2 & MEM & SP & X30).
    repeat arm8_step.
    + apply Bool.negb_true_iff, N.eqb_neq in BC.
      exists (j - 1). repeat split; try assumption; try lia.
      all: first
        [ apply msub_small; lia
        | replace (N.to_nat (n - (j - 1))) with (S (N.to_nat (n - j))) by lia; cbn [bcpy];
          rewrite N2Nat.id; replace (n - (n - j) - 1) with (j - 1) by lia;
          rewrite <- (setmem_mod_l 64 LittleE 4 _ (d + (msub 62 j 1 << 2))),
                  <- (getmem_mod_l 64 LittleE 4 _ (q + (msub 62 j 1 << 2))),
                  !bk_addr, getmem_mod_l, setmem_mod_l by lia;
          reflexivity ].
    + apply Bool.negb_false_iff, N.eqb_eq in BC. rewrite BC, N.sub_0_r in MEM. repeat split; try assumption.
      unfold wmemmove_spec. rewrite (proj2 (N.eqb_neq d q) DQ), (proj2 (N.ltb_lt _ _) BW).
      assumption.
  - destruct PRE as (k & KLE & N64 & DQ & FW & X0 & X1 & X2 & X3 & MEM & SP & X30).
    repeat arm8_step.
    all: destruct (n =? k) eqn:E; try discriminate.
    + apply N.eqb_eq in E. rewrite <- E in MEM. repeat split; try assumption.
      unfold wmemmove_spec. rewrite (proj2 (N.eqb_neq d q) DQ), (proj2 (N.ltb_ge _ _) FW).
      assumption.
    + apply N.eqb_neq in E. exists (k+1). repeat split; try assumption; try lia.
      all: first
        [ rewrite N.add_comm; apply N.mod_small; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy];
          rewrite N2Nat.id; first [ reflexivity | rewrite (N.add_comm d), (N.add_comm q); reflexivity ] ].
Qed.
