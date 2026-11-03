(* Compile separately after both proof modules to audit their final assumptions. *)
From Stdlib Require Import NArith Utf8.
Require Import Picinae_armv7.
Require Import arm7_memset_proof arm7_strlen_proof.
Import ARM7Notations.
Open Scope N_scope.

Check memset_total_correctness.
Print Assumptions memset_total_correctness.
Check strlen_total_correctness.
Print Assumptions strlen_total_correctness.
