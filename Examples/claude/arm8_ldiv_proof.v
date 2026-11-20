(* ldiv (AArch64) -- signed long quotient and remainder.

   C specification: ldiv_t ldiv(long numerator, long denominator), where
   ldiv_t has signed-long fields quot and rem. Division truncates toward zero;
   quot * denominator + rem = numerator.

   INHERITED PROVENANCE (not independently validated by this proof):
   /lib/aarch64-linux-gnu/libc.so.6, Ubuntu glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Symbol ldiv at 0x13d860, rebased entry 0; Ghidra 11.4.2 + pcode2coq.
   Generated ldiv_arm8.v is unchanged. Binary revalidation belongs to e02.
   Author/model: OpenAI GPT-6 Astra, implementation unit a-ldiv.
   Mathematical range helpers ported from amd64_common.v (Claude Opus 5.5);
   no AMD64 theory is imported.

   AAPCS64 contract as exhibited by this lift: X0/X1 initially hold n/d as
   64-bit two's-complement longs. X0/X1 return quot/rem respectively (the two
   64-bit fields of ldiv_t). Require d <> 0 and exclude LONG_MIN / -1.
   The RET at offset 12 jumps to X30, preserves SP and all result registers.
   All memory, X19-X29, X30, SP, and modeled SIMD registers Z8-Z15 are preserved.
   This is IL partial correctness, not termination or a lifter-soundness proof.
   No buffer, overlap, size, CPU feature, or tunable hypotheses are needed;
   entry stores must model arm8typctx. No callee contracts are assumed.
 *)

Require Import Picinae_armv8.
Require Import ldiv_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem ldiv_nwc: forall s2 s1, ldiv_arm8 s1 = ldiv_arm8 s2.
Proof. reflexivity. Qed.
Theorem ldiv_welltyped: welltyped_prog arm8typctx ldiv_arm8.
Proof. Picinae_typecheck. Qed.
Theorem ldiv_preserves_memory:
  forall_endstates ldiv_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition ldiv_saved :=
  [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25; R_X26; R_X27;
   R_X28; R_X29; R_X30; R_SP; R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13;
   R_Z14; R_Z15].
Theorem ldiv_preserves_callee_saved:
  forall v, In v ldiv_saved ->
  forall_endstates ldiv_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same. unfold ldiv_saved in IN.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Lemma quot_range:
  forall (n d m:Z), (0 < m)%Z -> (-m <= n < m)%Z -> (-m <= d < m)%Z -> d <> 0%Z ->
  ~ (n = -m /\ d = -1)%Z -> (-m <= Z.quot n d < m)%Z.
Proof.
  intros n d m M RN RD DNZ NOVF.
  destruct (Z.eq_dec d 1) as [->|D1]. rewrite Z.quot_1_r. lia.
  destruct (Z.eq_dec d (-1)) as [->|D2].
    pose proof (Z.quot_opp_r n 1 ltac:(lia)) as Q. simpl (Z.opp 1) in Q. rewrite Q, Z.quot_1_r. lia.
  assert (A: (Z.abs (Z.quot n d) <= Z.abs n / 2)%Z).
    rewrite <- Z.quot_abs, Z.quot_div_nonneg by lia.
    apply Z.div_le_compat_l; lia.
  assert (B: (Z.abs n / 2 <= m / 2)%Z) by (apply Z.div_le_mono; lia).
  assert (C: (m / 2 < m)%Z) by (apply Z.div_lt; lia).
  lia.
Qed.

Lemma rem_range:
  forall (n d m:Z), (-m <= d < m)%Z -> d <> 0%Z -> (-m <= Z.rem n d < m)%Z.
Proof.
  intros. pose proof (Z.rem_bound_abs n d H0). lia.
Qed.


Lemma ldiv_quot_range: forall n d,
  signed_range 64 n -> signed_range 64 d -> d <> 0%Z ->
  ~ (n = (-2^63)%Z /\ d = (-1)%Z) -> signed_range 64 (Z.quot n d).
Proof. unfold signed_range; intros. apply (quot_range n d (2^63)); assumption || reflexivity. Qed.
Lemma ldiv_rem_range: forall n d,
  signed_range 64 d -> d <> 0%Z -> signed_range 64 (Z.rem n d).
Proof. unfold signed_range; intros. apply (rem_range n d (2^63)); assumption. Qed.

Definition ldiv_exit (t:trace) :=
  match t with (Addr 12,_)::_ => true | _ => false end.
Definition postcondition (n d:Z) (sp ra:N) (s:store) :=
  toZ 64 (s R_X0) = Z.quot n d /\
  toZ 64 (s R_X1) = Z.rem n d /\ s R_SP = sp /\ s R_X30 = ra.
Definition ldiv_invs (n d:Z) (sp ra:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 64 (s R_X0) = n /\ toZ 64 (s R_X1) = d /\
               s R_SP = sp /\ s R_X30 = ra)
  | 12 => Some (postcondition n d sp ra s)
  | _ => None
  end | _ => None end.

Theorem ldiv_correct:
  forall s t s' x' n d sp ra
    (ENTRY: startof t (x',s') = (Addr 0,s))
    (MDL: models arm8typctx s)
    (HN: toZ 64 (s R_X0) = n) (HD: toZ 64 (s R_X1) = d)
    (SP: s R_SP = sp) (RA: s R_X30 = ra)
    (DNZ: d <> 0%Z) (NOVF: ~ (n = (-2^63)%Z /\ d = (-1)%Z)),
  satisfies_all ldiv_arm8 (ldiv_invs n d sp ra) ldiv_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ldiv_welltyped. intro MDL1.
  clear - PRE MDL1 DNZ NOVF. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [HN [HD [SP RA]]].
  repeat arm8_step.
  all: unfold postcondition.
  - exfalso. apply DNZ. rewrite <- HD.
    destruct (N.eqb_spec (s1 R_X1) 0) as [E|E].
    + rewrite E. apply toZ_0_r.
    + cbn in BC. discriminate.
  - assert (RN: signed_range 64 n) by (rewrite <- HN; apply toZ_bounds).
    assert (RD: signed_range 64 d) by (rewrite <- HD; apply toZ_bounds).
    assert (RQ: signed_range 64 (Z.quot n d)) by
      (apply ldiv_quot_range; assumption).
    unfold sbop2. rewrite HN, HD.
    rewrite (toZ_ofZ 64 (Z.quot n d) RQ).
    rewrite msub_sbop, toZ_mul, canonicalZ_sub_r.
    rewrite (toZ_ofZ 64 (Z.quot n d) RQ), HN, HD.
    replace (n - Z.quot n d * d)%Z with (Z.rem n d) by
      (pose proof (Z.quot_rem' n d); lia).
    rewrite toZ_ofZ by (apply ldiv_rem_range; assumption).
    repeat split; assumption.
Qed.

Theorem ldiv_identity: forall n d sp ra s,
  postcondition n d sp ra s ->
  (toZ 64%N (s R_X0) * d + toZ 64%N (s R_X1) = n)%Z.
Proof.
  intros n d sp ra s [Q [R _]]. rewrite Q, R, Z.mul_comm.
  symmetry. apply Z.quot_rem'.
Qed.

(* Execute the actual RET statement, including its jump and exact store. *)
Theorem ldiv_return: forall s c' s' x,
  exec_stmt arm8typctx s (Move R_PC (Var R_X30) $; Jmp (Var R_PC)) c' s' x ->
  x = Some (Addr (s R_X30)) /\ reset_temps s s' = update s R_PC (s R_X30).
Proof.
  intros s c' s' x XS. step_stmt XS.
  destruct XS as [[-> ->] _]. split; reflexivity.
Qed.


Theorem ldiv_return_step: forall s sf x,
  can_step ldiv_arm8 ((x,sf),(Addr 12,s)) ->
  x = Addr (s R_X30) /\ sf = update s R_PC (s R_X30).
Proof.
  intros s sf x CS. inversion CS; subst.
  cbn [ldiv_arm8] in LU. injection LU as <- <-.
  apply ldiv_return in XS. destruct XS as [-> ->]. split; reflexivity.
Qed.

(* Every signed input pair has a modeled ABI store; the C exclusions do not
   require any property of outputs. In particular 7 / 3 is a legal input. *)
Definition ldiv_input_store (n d:Z) : store :=
  update (update (fun _ => 0) R_X0 (ofZ 64 n)) R_X1 (ofZ 64 d).
Theorem ldiv_inputs_satisfiable: forall n d,
  signed_range 64 n -> signed_range 64 d ->
  models arm8typctx (ldiv_input_store n d) /\
  toZ 64 (ldiv_input_store n d R_X0) = n /\
  toZ 64 (ldiv_input_store n d R_X1) = d.
Proof.
  intros n d RN RD. split.
  - unfold ldiv_input_store. apply models_update; [apply ofZ_bound|].
    apply models_update; [apply ofZ_bound|].
    intros v w CV. apply N.neq_0_lt_0, pow2_nonzero.
  - cbn [ldiv_input_store update]. split; apply toZ_ofZ; assumption.
Qed.
Example ldiv_defined_example:
  signed_range 64 7 /\ signed_range 64 3 /\
  3%Z <> 0%Z /\ ~ (7%Z = (-2^63)%Z /\ 3%Z = (-1)%Z).
Proof. unfold signed_range; cbn; lia. Qed.

(* A caller-facing consequence: any valid execution reaching this RET, then
   taking it, has the specified returned values, target, and frame. *)
Theorem ldiv_returns_correct:
  forall s t sr sf x n d sp ra
    (ENTRY: startof t (Addr 12,sr) = (Addr 0,s))
    (MDL: models arm8typctx s)
    (HN: toZ 64 (s R_X0) = n) (HD: toZ 64 (s R_X1) = d)
    (SP: s R_SP = sp) (RA: s R_X30 = ra)
    (DNZ: d <> 0%Z) (NOVF: ~ (n = (-2^63)%Z /\ d = (-1)%Z))
    (XP: exec_prog ldiv_arm8 ((Addr 12,sr)::t))
    (UT: unterminated ldiv_exit t)
    (RET: can_step ldiv_arm8 ((x,sf),(Addr 12,sr))),
  x = Addr ra /\ postcondition n d sp ra sf /\
  (toZ 64%N (sf R_X0) * d + toZ 64%N (sf R_X1) = n)%Z /\
  s V_MEM64 = sf V_MEM64 /\
  (forall v, In v ldiv_saved -> s v = sf v).
Proof.
  intros.
  pose proof (ldiv_correct s t sr (Addr 12) n d sp ra
    ENTRY MDL HN HD SP RA DNZ NOVF) as SA.
  pose proof (satall_trueif_inv _ _ _ _ SA XP UT) as POST.
  change (postcondition n d sp ra sr) in POST.
  assert (FULL: exec_prog ldiv_arm8 ((x,sf)::(Addr 12,sr)::t)) by
    (apply exec_prog_step; assumption).
  assert (START: startof ((Addr 12,sr)::t) (x,sf) = (Addr 0,s)) by
    (rewrite startof_cons; exact ENTRY).
  pose proof (ldiv_preserves_memory _ _ _ _ _ FULL START) as MEM.
  assert (SAVED: forall v, In v ldiv_saved -> s v = sf v).
  { intros v IN. exact (ldiv_preserves_callee_saved v IN _ _ _ _ _ FULL START). }
  destruct (ldiv_return_step _ _ _ RET) as [TARGET STORE].
  assert (FINAL: postcondition n d sp ra sf).
  { rewrite STORE. exact POST. }
  split. rewrite TARGET. destruct POST as [_ [_ [_ R]]]. rewrite R. reflexivity.
  split. exact FINAL.
  split. eapply ldiv_identity; exact FINAL.
  split; assumption.
Qed.
