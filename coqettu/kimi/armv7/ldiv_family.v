From Stdlib Require Import NArith Lia.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  ldiv_armv7 division_program signed_div_spec signed_div_family divmod_family.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition ldiv_program : program := division_program.
Definition ldiv_family (cs ps : store) : invariant_set := signed_div_family cs ps.

Lemma ldiv_program_contains_divmod : divmod_program ⊆2 ldiv_program.
Proof. intros s a insn H. exact H. Qed.

Lemma ldiv_program_contains_ldiv : ldiv_armv7 ⊆2 ldiv_program.
Proof. exact division_program_contains_ldiv. Qed.

Theorem ldiv_program_welltyped : welltyped_prog arm7typctx ldiv_program.
Proof. exact division_program_welltyped. Qed.
