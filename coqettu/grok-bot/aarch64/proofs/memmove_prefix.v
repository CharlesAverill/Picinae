(* memmove, disjoint case: the straight-line prefix 0x15e708 .. 0x15e72c is
   stepped one instruction at a time to the tail call `b memcpy` (0x15e750),
   for any invariant family that has no invariant/exit on those addresses.
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memmove_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokTail GrokCov GrokPrefix.
From Grok.proofs Require Import memmove_lib memmove_defs.
Import ARM8Notations.
Open Scope N.

Section Prefix.
  Variables (prog: program) (Invs: trace -> option Prop) (xp: trace -> bool) (mem d src n sp raddr: N).
  Hypothesis P1: memmove_armv8 ⊆2 prog.
  Hypothesis HI : ∀ x t1 t2, Invs (x::t1) = Invs (x::t2).
  Hypothesis HX : ∀ x t1 t2, xp (x::t1) = xp (x::t2).
  Hypothesis XNIL : xp nil = false.
  Definition mvb_addrs := 0x15e708 :: 0x15e70c :: 0x15e710 :: 0x15e714 :: 0x15e718 :: 0x15e71c :: 0x15e720 ::
                          0x15e724 :: 0x15e728 :: 0x15e72c :: 0x15e750 :: nil.
  Hypothesis NOI : ∀ a s t, In a mvb_addrs -> Invs ((Addr a, s)::t) = None.
  Hypothesis NOX : ∀ a s t, In a mvb_addrs -> xp ((Addr a, s)::t) = false.

  Definition Pb (s:store) :=
    models archtyps s /\ s R_X0 = d /\ s R_X1 = src /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\
    s R_X30 = raddr /\ d + n < 2^64 /\ src + n < 2^64 /\ n < 2^62 /\ 0 < n /\ (src + n <= d \/ d + n <= src).

  Hypothesis TGT : ∀ s t xs', startof t xs' = (Addr 0x118270, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).

  Ltac inaddr := cbn; repeat (first [left; reflexivity | right]).

  Ltac pstep a0' a1' P' Q' NEXT :=
    let s0 := fresh "s0" in let t0 := fresh "t0" in let xs0 := fresh "xs0" in
    let START := fresh "START" in let HP := fresh "HP" in
    intros s0 t0 xs0 START HP;
    eapply (step_satisfies_all prog Invs xp HI HX XNIL a0' a1' 4) with (P := P') (Q := Q');
    [ intros; apply NOI; inaddr
    | intros; apply NOX; inaddr
    | intro; apply P1; reflexivity
    | clear START HP
    | exact NEXT
    | exact START
    | exact HP ].

  Ltac pb_close := unfold Pb in *; upd_simpl;
    repeat match goal with H: _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia].

  Ltac mstep :=
    let s := fresh "s" in let c1 := fresh "c1" in let s1 := fresh "s1" in let x1 := fresh "x1" in
    let HP := fresh "HP" in let XS := fresh "XS" in let MR := fresh "MR" in
    let RT := fresh "RT" in let EX := fresh "EX" in
    intros s c1 s1 x1 HP XS;
    match goal with |- exitof (?a + _) _ = _ /\ _ =>
      assert (MR: models archtyps (reset_temps s s1))
        by (eapply (step_models memmove_armv8 s a 4);
            [ exact memmove_welltyped | reflexivity | unfold Pb in HP; tauto | exact XS ])
    end;
    step_stmt XS; destruct XS as [[RT EX] _]; subst x1; split; [reflexivity|]; rewrite RT in MR |- *.

  Lemma r750: ∀ s t xs', startof t xs' = (Addr 0x15e750, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof.
    apply (tailcall_satisfies_all prog Invs xp HI HX XNIL 0x15e750 0x118270).
    - intros; apply NOI; inaddr.
    - intros; apply NOX; inaddr.
    - intro s; apply P1; reflexivity.
    - intros s s' EQ HP. unfold Pb in *. destruct HP as (M & HP). split.
      + intros v w CV. rewrite <- EQ. exact (M v w CV).
      + rewrite <- !EQ. exact HP.
    - exact TGT.
  Qed.

  Lemma r72c: ∀ s t xs', startof t xs' = (Addr 0x15e72c, s) -> (Pb s /\ (s R_CY = 0 \/ s R_ZR = 1)) ->
    satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e72c 0x15e750 (fun s => Pb s /\ (s R_CY = 0 \/ s R_ZR = 1)) Pb r750.
    intros s c1 s1 x1 [HP CZ] XS.
    assert (MR: models archtyps (reset_temps s s1))
      by (eapply (step_models memmove_armv8 s 0x15e72c 4); [exact memmove_welltyped | reflexivity | apply HP | exact XS]).
    destruct CZ as [CZ|CZ]; step_stmt XS; destruct XS as [XS _];
    (match type of XS with context [(N.lor ?a ?b) mod 2^1] =>
       rewrite (lor_odd a b) in XS by (first [left; reflexivity | right; reflexivity]) end);
    cbv beta iota in XS; inversion XS; subst; inversion E; subst;
    (split; [reflexivity|]);
    unfold Pb in *; rewrite !reset_reg by (cbn; discriminate); upd_simpl; tauto.
  Qed.

  Lemma r728: ∀ s t xs', startof t xs' = (Addr 0x15e728, s) ->
    (Pb s /\ s R_X6 = msub 64 (msub 64 src n) d /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64)) ->
    satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e728 0x15e72c (fun s => Pb s /\ s R_X6 = msub 64 (msub 64 src n) d /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64))
          (fun s => Pb s /\ (s R_CY = 0 \/ s R_ZR = 1)) r72c.
    mstep. destruct HP as [HP [H6 H7]]. split; [pb_close|]. upd_simpl. rewrite H6, H7.
    assert (DJ := HP). unfold Pb in DJ.
    assert (L: msub 64 (msub 64 src n) d <= msub 64 0 (N.shiftl n 1 mod 2^64)) by (apply mvb_disj; tauto).
    destruct (N.leb_spec (msub 64 0 (N.shiftl n 1 mod 2^64)) (msub 64 (msub 64 src n) d)).
    - right. replace (msub 64 (msub 64 src n) d) with (msub 64 0 (N.shiftl n 1 mod 2^64)) by lia.
      rewrite msub_self. reflexivity.
    - left. reflexivity.
  Qed.

  Lemma r724: ∀ s t xs', startof t xs' = (Addr 0x15e724, s) ->
    (Pb s /\ s R_X6 = msub 64 src n /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64)) ->
    satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e724 0x15e728 (fun s => Pb s /\ s R_X6 = msub 64 src n /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64))
          (fun s => Pb s /\ s R_X6 = msub 64 (msub 64 src n) d /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64)) r728.
    mstep. destruct HP as [HP [H6 H7]]. split; [pb_close|]. upd_simpl. unfold Pb in HP.
    split; [|assumption]. rewrite H6. f_equal. tauto.
  Qed.

  Lemma r720: ∀ s t xs', startof t xs' = (Addr 0x15e720, s) -> (Pb s /\ s R_X6 = msub 64 src n) ->
    satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e720 0x15e724 (fun s => Pb s /\ s R_X6 = msub 64 src n)
          (fun s => Pb s /\ s R_X6 = msub 64 src n /\ s R_X7 = msub 64 0 (N.shiftl n 1 mod 2^64)) r724.
    mstep. destruct HP as [HP H6]. split; [pb_close|]. upd_simpl. unfold Pb in HP.
    split; [assumption|]. replace (s R_X2) with n by (symmetry; tauto). reflexivity.
  Qed.

  Lemma r71c: ∀ s t xs', startof t xs' = (Addr 0x15e71c, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e71c 0x15e720 Pb (fun s => Pb s /\ s R_X6 = msub 64 src n) r720.
    mstep. split; [pb_close|]. upd_simpl. unfold Pb in HP.
    replace (s R_X1) with src by (symmetry; tauto). replace (s R_X2) with n by (symmetry; tauto). reflexivity.
  Qed.

  Lemma r718: ∀ s t xs', startof t xs' = (Addr 0x15e718, s) -> (Pb s /\ s R_ZR = 0) ->
    satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e718 0x15e71c (fun s => Pb s /\ s R_ZR = 0) Pb r71c.
    intros s c1 s1 x1 [HP HZ] XS.
    assert (MR: models archtyps (reset_temps s s1))
      by (eapply (step_models memmove_armv8 s 0x15e718 4); [exact memmove_welltyped | reflexivity | apply HP | exact XS]).
    step_stmt XS.
    first
      [ destruct XS as [[RT EX] _]; subst x1; split; [reflexivity|]; rewrite RT in MR |- *; pb_close
      | destruct XS as [XS _]; cbv beta iota in XS; inversion XS; subst; (split; [reflexivity|]);
        unfold Pb in *; rewrite !reset_reg by (cbn; discriminate); upd_simpl; tauto ].
  Qed.

  Lemma r714: ∀ s t xs', startof t xs' = (Addr 0x15e714, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof.
    pstep 0x15e714 0x15e718 Pb (fun s => Pb s /\ s R_ZR = 0) r718.
    mstep. split; [pb_close|]. upd_simpl. unfold Pb in HP.
    destruct (N.eqb_spec (msub 64 (s R_X0) (s R_X1)) 0) as [E|E]; [|reflexivity].
    exfalso. unfold msub in E. replace (s R_X0) with d in E by (symmetry; tauto). replace (s R_X1) with src in E by (symmetry; tauto).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & D & S & _ & P & O).
    change (2^64) with 18446744073709551616 in *.
    rewrite (N.mod_small src) in E by lia.
    pose proof (N.div_mod (d + (18446744073709551616 - src)) 18446744073709551616 ltac:(discriminate)).
    pose proof (N.mod_lt (d + (18446744073709551616 - src)) 18446744073709551616 ltac:(discriminate)).
    lia.
  Qed.

  Lemma r710: ∀ s t xs', startof t xs' = (Addr 0x15e710, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof. pstep 0x15e710 0x15e714 Pb Pb r714. mstep. pb_close. Qed.

  Lemma r70c: ∀ s t xs', startof t xs' = (Addr 0x15e70c, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof. pstep 0x15e70c 0x15e710 Pb Pb r710. mstep. pb_close. Qed.

  Lemma r708: ∀ s t xs', startof t xs' = (Addr 0x15e708, s) -> Pb s -> satisfies_all prog Invs xp (xs'::t).
  Proof. pstep 0x15e708 0x15e70c Pb Pb r70c. mstep. pb_close. Qed.
End Prefix.

