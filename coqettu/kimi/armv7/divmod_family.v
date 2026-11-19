From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  FUN_0003046e_armv7 FUN_000306fc_armv7 division_program signed_div_spec signed_div_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition divmod_program : program := division_program.
Definition divmod_family (cs ps : store) : invariant_set := signed_div_family cs ps.

Lemma divmod_program_contains_signed : FUN_0003046e_armv7 ⊆2 divmod_program.
Proof. exact division_program_contains_signed. Qed.

Lemma divmod_program_contains_divmod : FUN_000306fc_armv7 ⊆2 divmod_program.
Proof. exact division_program_contains_divmod. Qed.

Theorem divmod_program_welltyped : welltyped_prog arm7typctx divmod_program.
Proof. exact division_program_welltyped. Qed.
