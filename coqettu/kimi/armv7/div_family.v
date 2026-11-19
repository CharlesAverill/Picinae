From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  div_armv7 division_program signed_div_spec signed_div_family divmod_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition div_program : program := division_program.
Definition div_family (cs ps : store) : invariant_set := signed_div_family cs ps.

Lemma div_program_contains_divmod : divmod_program ⊆2 div_program.
Proof. intros s a insn H. exact H. Qed.

Lemma div_program_contains_div : div_armv7 ⊆2 div_program.
Proof. exact division_program_contains_div. Qed.

Theorem div_program_welltyped : welltyped_prog arm7typctx div_program.
Proof. exact division_program_welltyped. Qed.
