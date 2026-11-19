(* Grok Bot (agent coqettu): weakening a proved invariant set pointwise.
   If I2 has an invariant exactly where I1 does and each I1 invariant implies
   the I2 one, any satisfies_all proof for I1 is one for I2.  Used to place a
   callee (e.g. wcschr inside wcsspn and inside wcscspn) at an address whose
   invariant in the caller's family is a disjunction over call sites. *)
From Stdlib Require Import Utf8 NArith.
Require Import Picinae_armv8.
Open Scope N.

Section Weaken.
  Variables (p: program) (I1 I2: trace -> option Prop) (xp: trace -> bool).
  Hypothesis WN: ∀ t, I1 t = None -> I2 t = None.
  Hypothesis WS: ∀ t P1, I1 t = Some P1 -> ∃ P2, I2 t = Some P2 /\ (P1 -> P2).

  Theorem nextinv'_weaken: ∀ b t, nextinv' p I1 xp b t -> nextinv' p I2 xp b t.
  Proof.
    cofix IH. intros b t NI. inversion NI; subst.
    - apply NIHere'. unfold effinv in *. destruct (I1 t) as [P1|] eqn:E1.
      + destruct (WS _ _ E1) as (P2 & E2 & IMP). rewrite E2.
        destruct (orb _ _); simpl in *; [exact (IMP TRU) | exact TRU].
      + rewrite (WN _ E1). exact TRU.
    - eapply NIStep'; [|exact IL|].
      + unfold effinv in *. destruct (I1 _) as [P1|] eqn:E1.
        * destruct (WS _ _ E1) as (P2 & E2 & _). rewrite E2.
          destruct (orb _ _); [discriminate | reflexivity].
        * rewrite (WN _ E1). exact NOI.
      + intros. apply IH. eapply STEP. eassumption.
  Qed.

  Theorem satisfies_all_weaken: ∀ t, satisfies_all p I1 xp t -> satisfies_all p I2 xp t.
  Proof. intros t SA XP UT b. apply nextinv'_weaken, SA; assumption. Qed.
End Weaken.
