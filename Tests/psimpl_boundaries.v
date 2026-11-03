(* Dispatch and boundary regressions for the native simplifier and its
   independent Classic implementation. Compile after the library with:
   picinae-env rocq compile -R . Picinae Picinae_simplifier_v0.v
   picinae-env rocq compile -R . Picinae Tests/psimpl_boundaries.v *)
From Stdlib Require Import NArith.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Require Import Picinae_i386 Picinae_amd64 Picinae_armv7 Picinae_armv8 Picinae_riscv.
Require Import Picinae_simplifier_v0.
Open Scope N_scope.

Ltac2 check_context_size (expected : int) :=
  if Int.equal (List.length (Control.hyps ())) expected then () else
    Control.zero (Tactic_failure (Some (Message.of_string
      "Simplifier left temporary hypotheses"))).

(* Using a signature parameter exercises the same substitution as Picinae_ISA.
   The i386 instances below poison the opposite backend's entry points. *)
Module CheckForms (IL : PICINAE_IL) (B : PSIMPL_BASE IL).
Import IL B.

Ltac check :=
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n)) by
    (intros; psimpl; ltac2:(check_context_size 1); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; psimpl in H; ltac2:(check_context_size 2); exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n)) by
    (intros; psimpl (N.add _ 0); ltac2:(check_context_size 1); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; psimpl (N.add _ 0) in H;
     ltac2:(check_context_size 2); exact H); clear checked;
  (* A wildcard selects the requested expression without simplifying the
     neighboring addition. *)
  let checked := fresh "checked" in
  assert (checked : (forall n m:N, n = m + 0 -> n + 0 = m + 0)) by
    (intros n m H; psimpl (N.add n _); exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n m:N, n + 0 = m + 0 -> n = m + 0)) by
    (intros n m H; psimpl (N.add n _) in H; exact H); clear checked;
  (* Classic sequencing can hand the native adapter several goals or no goals.
     Its context-sensitive operations must be focused on each goal separately. *)
  let checked := fresh "checked" in
  assert (checked : (forall n:N, (n + 0 = n) /\ (n + 0 = n))) by
    (intros; split; psimpl; reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> (n = n) /\ (n = n))) by
    (intros n H; split; psimpl in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, (n + 0 = n) /\ (n + 0 = n))) by
    (intros; split; psimpl (N.add _ 0); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> (n = n) /\ (n = n))) by
    (intros n H; split; psimpl (N.add _ 0) in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (0%N = 0%N)) by
    (reflexivity; psimpl; psimpl (N.add _ 0)); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall b:bool, (if b then b else b) = b)) by
    (intros; psimpl; reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall b:bool, (if b then b else b) = b -> b = b)) by
    (intros b H; psimpl in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall b:bool, (if b then b else b) = b)) by
    (intros b; psimpl (if b then _ else _); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall b:bool, (if b then b else b) = b -> b = b)) by
    (intros b H; psimpl (if b then _ else _) in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) v n, update s v (n + 0) = update s v n)) by
    (intros; psimpl; reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) v n, update s v (n + 0) = s -> update s v n = s)) by
    (intros s v n H; psimpl in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) v n, update s v (n + 0) = update s v n)) by
    (intros; psimpl (update _ _ (N.add _ 0)); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) v n, update s v (n + 0) = s -> update s v n = s)) by
    (intros s v n H; psimpl (update _ _ (N.add _ 0)) in H; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n = n)) by
    (intros n; pose (local := n + 0);
     psimpl in local;
     let value := eval unfold local in local in constr_eq value n;
     ltac2:(check_context_size 2); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n = n)) by
    (intros n; pose (local := n + 0);
     psimpl (N.add _ 0) in local;
     let value := eval unfold local in local in constr_eq value n;
     ltac2:(check_context_size 2); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n = n)) by
    (intros n; pose (local := n + 0);
     let h := constr:(local) in psimpl_hyp h;
     let value := eval unfold local in local in constr_eq value n;
     ltac2:(check_context_size 2); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) (v:var) (n:N), n = n)) by
    (intros s v n; pose (local := update s v (n + 0));
     psimpl in local;
     let value := eval unfold local in local in constr_eq value (update s v n);
     ltac2:(check_context_size 4); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall (s:store) (v:var) (n:N), n = n)) by
    (intros s v n; pose (local := update s v (n + 0));
     psimpl (update _ _ (N.add _ 0)) in local;
     let value := eval unfold local in local in constr_eq value (update s v n);
     ltac2:(check_context_size 4); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; let h := constr:(H) in psimpl_hyp h; exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; let h := constr:(H) in psimpl_exp_hyp uconstr:(N.add _ 0) h;
     exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; psimpl_hyp ipattern:(H); exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; psimpl_exp_hyp uconstr:(N.add _ 0) ipattern:(H);
     exact H); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n < 2^8 -> n mod 2^8 = n)) by
    (intros n H; psimpl; reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n sast x Heq:N,
      (n + 0) + sast + x + Heq = n + sast + x + Heq)) by
    (intros n sast x Heq; psimpl (N.add n 0);
     ltac2:(check_context_size 4); reflexivity); clear checked;
  (* Unsupported expression types retain the original universal-AST fallback. *)
  let checked := fresh "checked" in
  assert (checked : (forall n:nat, n = n)) by
    (intros n; psimpl n; ltac2:(check_context_size 1); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n)) by
    (intros n; assert_fails (psimpl (N.mul _ 0));
     ltac2:(check_context_size 1);
     psimpl (N.add _ 0); reflexivity); clear checked;
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n = n)) by
    (intros n H; assert_fails (psimpl (N.mul _ 0) in H);
     ltac2:(check_context_size 2);
     psimpl (N.add _ 0) in H; exact H); clear checked;
  (* The original local-definition fallback cannot clear a definition that is
     referenced by a later definition. Failure must restore the entire state. *)
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n = n)) by
    (intros n; pose (local := n + 0); pose (dependent := local + 0);
     assert_fails (psimpl in local);
     let value := eval unfold local in local in constr_eq value (n + 0);
     ltac2:(check_context_size 3); reflexivity); clear checked.
End CheckForms.

Module Native := Picinae_Simplifier_Base IL_i386.
Ltac Native.PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.
Ltac Native.psimpl_goal_ltac1 ::= fail "Legacy goal selected".
Ltac Native.psimpl_hyp_ltac1 h ::= fail "Legacy hypothesis selected".
Ltac Native.psimpl_exp_goal_ltac1 e ::= fail "Legacy expression goal selected".
Ltac Native.psimpl_exp_hyp_ltac1 e h ::= fail "Legacy expression hypothesis selected".
Ltac Native.psimpl_vals_goal ::= fail "Legacy goal AST lifecycle selected".
Ltac Native.psimpl_vals_hyp h ::= fail "Legacy hypothesis AST lifecycle selected".
Ltac Native._psimpl_exp_hyp x h ::= fail "Legacy expression dispatcher selected".
Module NativeForms := CheckForms IL_i386 Native.
Goal True. Proof. NativeForms.check. exact I. Qed.

Module NativeISA := Picinae_ISA IL_i386 Native Theory_i386 Statics_i386 FInterp_i386.
Ltac NativeISA.simpl_memaccs h ::= idtac.
Goal forall n:N,
  Theory_i386.nextinv (fun _ _ => None) (fun _ => Some (n + 0 = n))
    (fun _ => true) true nil.
Proof. intros n. NativeISA.ISA_invhere. reflexivity. Qed.
Goal forall c s c' s' x, IL_i386.exec_stmt c s IL_i386.Nop c' s' x -> True.
Proof. intros c s c' s' x XS. NativeISA.ISA_step_and_simplify XS. exact I. Qed.

(* Replacing the public Classic adapters cannot affect the legacy graph. *)
Module Legacy := Picinae_Simplifier_Base IL_i386.
Ltac Legacy.PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.
Ltac Legacy.psimpl_goal ::= fail "Native goal selected".
Ltac Legacy.psimpl_hyp h ::= fail "Native hypothesis selected".
Ltac Legacy.psimpl_exp_goal e ::= fail "Native expression goal selected".
Ltac Legacy.psimpl_exp_hyp e h ::= fail "Native expression hypothesis selected".
Module LegacyInterface <: PSIMPL_BASE IL_i386.
Include Legacy.
Ltac psimpl_goal ::= Legacy.psimpl_goal_ltac1.
Ltac psimpl_hyp h ::= Legacy.psimpl_hyp_ltac1 h.
Ltac psimpl_exp_goal e ::= Legacy.psimpl_exp_goal_ltac1 e.
Ltac psimpl_exp_hyp e h ::= Legacy.psimpl_exp_hyp_ltac1 e h.
End LegacyInterface.
Module LegacyForms := CheckForms IL_i386 LegacyInterface.
Goal True. Proof. LegacyForms.check. exact I. Qed.

(* Third-party implementations can still use the signature's Classic defaults. *)
Module ThirdParty : PSIMPL_BASE IL_i386.
Include PSIMPL_BASE IL_i386.
End ThirdParty.
Ltac ThirdParty.PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.
Module ThirdPartyForms := CheckForms IL_i386 ThirdParty.
Goal True. Proof. ThirdPartyForms.check. exact I. Qed.

(* Other architectures must substitute their own store and variable types into
   the native dispatch, even with all five architectures loaded together. *)
Module Amd64Forms := CheckForms IL_amd64 PSimpl_amd64.
Goal True. Proof. Amd64Forms.check. exact I. Qed.
Module Arm7Forms := CheckForms IL_arm7 PSimpl_arm7.
Goal True. Proof. Arm7Forms.check. exact I. Qed.
Module Arm8Forms := CheckForms IL_arm8 PSimpl_arm8.
Goal True. Proof. Arm8Forms.check. exact I. Qed.
Module RISCVForms := CheckForms IL_RISCV PSimpl_RISCV.
Goal True. Proof. RISCVForms.check. exact I. Qed.

(* User replacement of PSimplifier must be observed after functor application.
   Version zero leaves every selected expression untouched. *)
Module Off := Picinae_Simplifier_v0 IL_i386 Theory_i386 Statics_i386 FInterp_i386.
Ltac Native.PSimplifier ::= Off.PSimplifier.
Module CheckDisabled (B : PSIMPL_BASE IL_i386).
Import B.
Ltac check :=
  let checked := fresh "checked" in
  assert (checked : (forall n:N, n + 0 = n -> n + 0 = n)) by
    (intros n H; psimpl; psimpl (N.add _ 0) in H;
     psimpl (N.add _ 0); psimpl in H;
     lazymatch goal with |- n + 0 = n => idtac | _ => fail "Goal changed" end;
     lazymatch type of H with n + 0 = n => idtac | _ => fail "Hypothesis changed" end;
     ltac2:(check_context_size 2); exact H); clear checked.
End CheckDisabled.
Module NativeDisabled := CheckDisabled Native.
Goal True. Proof. NativeDisabled.check. exact I. Qed.

(* Fail after the AST has been created, to check rollback of markers, AST
   definitions, remembered expressions, and local-definition fallback. *)
Ltac reject_hyp ast h := fail "Injected simplifier failure".
Ltac reject_goal ast := fail "Injected simplifier failure".
Ltac Native.PSimplifier tac ::=
  lazymatch tac with
  | PSIMPL_U_GOAL => reject_goal
  | PSIMPL_U_HYP => reject_hyp
  | PSIMPL_N_HYP => reject_hyp
  | _ => PSimpl_i386_v1_1.PSimplifier tac
  end.
Goal forall n:N, n + 0 = n -> n = n.
Proof.
  intros n H.
  Fail Native.psimpl_goal.
  Fail Native.psimpl_hyp H.
  Fail Native.psimpl_exp_goal uconstr:(N.add _ 0).
  Fail Native.psimpl_exp_hyp uconstr:(N.add _ 0) H.
  Fail Native.psimpl_hyp constr:(0%N).
  lazymatch type of H with n + 0 = n => idtac end.
  pose (local := n + 0).
  Fail Native.psimpl_hyp local.
  Fail Native.psimpl_exp_hyp uconstr:(N.add _ 0) local.
  let value := eval unfold local in local in constr_eq value (n + 0).
  ltac2:(check_context_size 3). reflexivity.
Qed.
Ltac Native.PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.
Goal True. Proof. NativeForms.check. exact I. Qed.
