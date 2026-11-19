From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  FUN_0003046e_armv7 FUN_000306fc_armv7 div_armv7 ldiv_armv7.
Import ARM7Notations.
Open Scope N.

Definition division_program : program :=
  updateall2 (updateall2 (updateall2 FUN_0003046e_armv7 FUN_000306fc_armv7)
    div_armv7) ldiv_armv7.

Lemma division_program_contains_signed : FUN_0003046e_armv7 ⊆2 division_program.
Proof.
  intros s a insn H. unfold division_program, updateall2, updateall,
    ldiv_armv7, div_armv7, FUN_000306fc_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma division_program_contains_divmod : FUN_000306fc_armv7 ⊆2 division_program.
Proof.
  intros s a insn H. unfold division_program, updateall2, updateall,
    ldiv_armv7, div_armv7, FUN_000306fc_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma division_program_contains_div : div_armv7 ⊆2 division_program.
Proof.
  intros s a insn H. unfold division_program, updateall2, updateall,
    ldiv_armv7, div_armv7.
  repeat first
    [ exact H | discriminate H
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma division_program_contains_ldiv : ldiv_armv7 ⊆2 division_program.
Proof. apply subset_updateall2. Qed.

Theorem division_program_welltyped : welltyped_prog arm7typctx division_program.
Proof.
  intros s a. unfold division_program, updateall2, updateall.
  destruct (ldiv_armv7 s a) as [[sz q]|] eqn:H.
  - pose proof (ldiv_armv7.welltyped s a) as WT. rewrite H in WT. exact WT.
  - destruct (div_armv7 s a) as [[sz q]|] eqn:HD.
    + pose proof (div_armv7.welltyped s a) as WT. rewrite HD in WT. exact WT.
    + destruct (FUN_000306fc_armv7 s a) as [[sz q]|] eqn:HM.
      * pose proof (FUN_000306fc_armv7.welltyped s a) as WT. rewrite HM in WT. exact WT.
      * apply FUN_0003046e_armv7.welltyped.
Qed.
