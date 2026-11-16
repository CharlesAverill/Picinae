From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemset_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Theorem wmemset_welltyped: welltyped_prog arm8typctx wmemset_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemset_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wmemset_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wmemset_preserves_x30:
  forall_endstates wmemset_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* wset m p v k: m with the low 32 bits of v stored (4-byte little-endian)
   at p, p+4, ..., p+4(k-1), in increasing order.  Addresses are taken
   mod 2^64 by Picinae's setmem. *)
Fixpoint wset (m:memory) (p v:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => (wset m p v k') [Ⓓ p + (N.of_nat k' << 2) := v]
  end.

Section Invariants.
  Variables (sp mem raddr p c n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x160294 => Inv 0 (s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1602a4 => Inv 0 (∃ k, k <= n /\ s R_X3 = k /\ s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\
                         s V_MEM64 = wset mem p c (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1602ac => Post 0 (s R_X0 = p /\ s V_MEM64 = wset mem p c (N.to_nat n) /\
                          s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wmemset_exits := make_exits 0 wmemset_armv8 invs.
  Definition wmemset_invs := make_invs 0 wmemset_armv8 invs.
End Invariants.

Theorem wmemset_partial_correctness:
  ∀ prog s sp mem raddr p c n t xs'
    (PROG: wmemset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x160294, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X2: s R_X2 = n),
  satisfies_all prog (wmemset_invs sp mem raddr p c n) (wmemset_exits sp mem raddr p c n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemset_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wmemset_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    repeat arm8_step.
    exists 0. repeat split; try assumption; try lia.
  - destruct PRE as (k & KLE & X3 & X0 & X1 & X2 & MEM & SP & X30).
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
