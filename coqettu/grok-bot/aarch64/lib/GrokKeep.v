(* Grok Bot (agent coqettu): strengthening a proved invariant family with
   "register v still holds val" when the program never assigns v.  Used to
   carry a caller's callee-saved register (e.g. X19 in strcspn) through a
   transferred callee proof (e.g. __strchrnul) whose invariants omit it. *)
From Stdlib Require Import Utf8 NArith List.
Require Import Picinae_armv8.
Open Scope N.

Definition keep_head (v: var) (val: N) (t: trace) : Prop :=
  match t with (_, s)::_ => s v = val | nil => True end.

Definition keep_invs (I: trace -> option Prop) (v: var) (val: N) (t: trace) : option Prop :=
  match I t with Some P => Some (P /\ keep_head v val t) | None => None end.

Section Keep.
  Variables (p: program) (I: trace -> option Prop) (xp: trace -> bool) (v: var) (val: N).
  Hypothesis NA: prog_noassign v p.

  Theorem nextinv'_keep: ∀ b t, nextinv' p I xp b t -> keep_head v val t ->
    nextinv' p (keep_invs I v val) xp b t.
  Proof.
    cofix IH. intros b t NI KH. inversion NI; subst.
    - apply NIHere'. unfold effinv, keep_invs in *.
      destruct (I t); [|exact TRU].
      destruct (b || effexit p xp t); [split; assumption|exact TRU].
    - eapply NIStep'; [|exact IL|].
      + unfold effinv, keep_invs in *. destruct (I _); [|exact NOI].
        destruct (b || effexit p xp _); [discriminate|reflexivity].
      + intros c1 s1 x1 XS. apply IH; [eapply STEP; exact XS|].
        simpl in KH |- *. specialize (NA s a). rewrite IL in NA.
        assert (EQ := noassign_stmt_same _ _ NA _ _ _ _ _ XS).
        inversion EQ as [[E1 E2]]. unfold reset_temps, reset_vars.
        destruct (archtyps v); congruence.
  Qed.

  Theorem satisfies_all_keep: ∀ xs t,
    snd (startof t xs) v = val ->
    (∀ xs' t', startof t' xs' = startof t xs -> satisfies_all p I xp (xs'::t')) ->
    (∀ xs' t', startof t' xs' = startof t xs -> satisfies_all p (keep_invs I v val) xp (xs'::t')).
  Proof.
    intros xs t V0 SA xs' t' ST XP UT b. apply nextinv'_keep.
    - apply SA; assumption.
    - destruct xs' as [x' s']. simpl.
      destruct (startof t xs) as [x0 s0] eqn:E0. simpl in V0.
      rewrite <- V0. symmetry.
      exact (noassign_prog_same v p NA t' x0 s0 x' s' XP ST).
  Qed.
End Keep.

(* Several registers at once: keepl_st l s says s v = x for every (v,x) in l. *)
Definition keepl_st (l: list (var * N)) (s: store) : Prop :=
  fold_right (fun vx Q => s (fst vx) = snd vx /\ Q) True l.

Definition keepl_head (l: list (var * N)) (t: trace) : Prop :=
  match t with (_, s)::_ => keepl_st l s | nil => True end.

Definition keepl_invs (I: trace -> option Prop) (l: list (var * N)) (t: trace) : option Prop :=
  match I t with Some P => Some (P /\ keepl_head l t) | None => None end.

Lemma keepl_st_same: ∀ l (s s': store), (∀ vx, In vx l -> s' (fst vx) = s (fst vx)) ->
  keepl_st l s -> keepl_st l s'.
Proof.
  induction l as [|vx l IH]; intros s s' EQ K; [exact I|].
  destruct K as [K1 K2]. split.
  - rewrite EQ by (left; reflexivity). exact K1.
  - apply (IH s s'); [intros vx' H; apply EQ; right; exact H | exact K2].
Qed.

Section KeepL.
  Variables (p: program) (I: trace -> option Prop) (xp: trace -> bool) (l: list (var * N)).
  Hypothesis NA: ∀ vx, In vx l -> prog_noassign (fst vx) p.

  Theorem nextinv'_keepl: ∀ b t, nextinv' p I xp b t -> keepl_head l t ->
    nextinv' p (keepl_invs I l) xp b t.
  Proof.
    cofix IH. intros b t NI KH. inversion NI; subst.
    - apply NIHere'. unfold effinv, keepl_invs in *.
      destruct (I t); [|exact TRU].
      destruct (b || effexit p xp t); [split; assumption|exact TRU].
    - eapply NIStep'; [|exact IL|].
      + unfold effinv, keepl_invs in *. destruct (I _); [|exact NOI].
        destruct (b || effexit p xp _); [discriminate|reflexivity].
      + intros c1 s1 x1 XS. apply IH; [eapply STEP; exact XS|].
        simpl in KH |- *. revert KH. apply keepl_st_same. intros vx IN.
        specialize (NA vx IN s a). rewrite IL in NA.
        assert (EQ := noassign_stmt_same _ _ NA _ _ _ _ _ XS).
        inversion EQ as [[E1 E2]]. unfold reset_temps, reset_vars.
        destruct (archtyps (fst vx)); congruence.
  Qed.

  Theorem satisfies_all_keepl: ∀ xs t,
    keepl_st l (snd (startof t xs)) ->
    (∀ xs' t', startof t' xs' = startof t xs -> satisfies_all p I xp (xs'::t')) ->
    (∀ xs' t', startof t' xs' = startof t xs -> satisfies_all p (keepl_invs I l) xp (xs'::t')).
  Proof.
    intros xs t V0 SA xs' t' ST XP UT b. apply nextinv'_keepl.
    - apply SA; assumption.
    - destruct xs' as [x' s']. simpl.
      destruct (startof t xs) as [x0 s0] eqn:E0. simpl in V0.
      revert V0. apply keepl_st_same. intros vx IN. symmetry.
      exact (noassign_prog_same (fst vx) p (NA vx IN) t' x0 s0 x' s' XP ST).
  Qed.
End KeepL.
