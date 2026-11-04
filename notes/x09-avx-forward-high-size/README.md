# x09 AVX forward high-size author checkpoint

Initial author model: gpt-6-astra. Assigned reasoning effort xhigh,
service tier default. No subagents, no dependency installation, no remote
writes. Prepared worktree: /home/charles/.t3/worktrees/Picinae/t3-4842e322.
Assigned local branch: llm-proofs/x09-avx-forward-high-size.

State: **PARTIAL — hand off to a NEW gpt-6.1-sol xhigh/default fixer.**
The single full Dune target exited 1 at initial source line 146, characters
6–19, `exists (a0 d)`: `Not an inductive goal with 1 constructor.`
The dispatch case still had a non-existential obligation when the proof
tried to establish the ordinary-loop invariant. Exact remaining context
was not printed; guard normalization/branch discharge is a candidate
cause, not a verified diagnosis. No Astra repair or second build was run.
This was a proof failure, not a resource-cap failure. All prerequisite
modules, including accepted x03, produced full .vo files within 3000000 KiB.

The seven prefix Qed commands were processed before the error and remain
unchanged. The failed main and three later proofs are Abort in the active
source; all original proof bodies are in initial-attempt.v.txt. Every
statement and definition is unchanged. No x09 .vo was produced; no new
main theorem is exported or certified, and no final proof model is claimed.
The post-failure Abort packaging was not recompiled under the one-shot rule.

## Scope and statements

The initial source and exact theorem statements are archived verbatim in
initial-attempt.v.txt. The generated lift and accepted x03 source remain
unchanged. Root dune adds only the new proof module; its imports reuse the
accepted x03 dependency closure.

- high_no_unsigned_backward: real forward overlap and nonwrapping source
  endpoint imply n <= (d-s) mod 2^64, excluding JC at 318.
- high_sign_classification: for n>=2^63 the XOR sign test is exactly the
  comparison of d+n-s with 2^63; there is no arbitrary n<2^63 premise.
- high_zero_dispatch_example: a concrete high-size, nonwrapping forward
  overlap with zero sign test and zero page-offset heuristic.
- high_encoded_zero_branch: the unchanged map's exact JZ at 357 targets 501.
  This map equation alone is not an execution theorem.
- memmove_avx_correct_forward_high_size: proposed satisfies_all theorem for
  high-size forward overlap when the actual dispatch expression is nonzero
  and n is below both initial-memory REP/NT thresholds.
- memmove_avx_forward_high_size_at_ret: proposed original-byte copy,
  destination-exterior memory frame, RAX=d, RSP=rsp BEFORE RET 493 and
  RBX/RBP/R12-R15 preservation, for executions in that same exact domain.
- high_entry_satisfiable: proposed typed initial-memory/ABI witness at
  d=4096,s=4097,n=2^63, with thresholds=n, not an execution witness.
- high_welltyped/high_nwc/high_preserves_callee_saved and
  high_witness_thresholds supply typing, code independence, frame, and
  memory-witness support.

The exact high_path predicate states 2^63<=n, d<s<d+n, s+n<=2^64,
n<=m[0x31a3f8], n<=m[0x3215a8], and the actual 32-bit sum at 357 !=0.
The invariant/copy predicates are aliases of x03's unchanged definitions;
no guessed callee/kernel contracts and no result assumption are added.
DF and ISA feature bits are not tested/required on this IL path. The model
uses 64-bit AMD64 pointers and the System V ABI. No AArch64 ABI is used.

This is not all-high-size closure: the zero-dispatch region reaches the
backward path. dispatch-analysis.md records a candidate 33-row corruption
sequence and precisely what still needs an encoded-IL proof. Do not report
an execution counterexample based only on the arithmetic or map equation.
Even successful partial-correctness proofs would not establish termination,
executed RET, accessible execution, canonical hardware addresses, or
independent lifting/binary soundness. Provenance is inherited from x03.

## Evidence and policy

00-ancestry-before.log records the prepared e00 head; the workspace was
clean before the first notes were created (the log itself creates the
untracked notes directory seen by its embedded status command). The exact
assigned prerequisite 14ea393f2227bc8bde692b1e70badc61dce80304 contains e00,
x03's Astra checkpoint, and its accepted Sol completion only. Import used
ff-only. The remote-name check succeeded with empty output before renaming
only the prepared branch. Initial sandbox DNS/Git-metadata write failures
were retried with the required access; no branch collision or unexpected
history was ignored.

07-full-vo-initial.log records the single full target invocation, raw
stdout/stderr, resource gate, and real exit. Cap 3000000 KiB, stack 65536,
-j1, cache disabled, one compiler. Queue delays do not count as failures.
The shared wrapper and scheduler are used without edits or installation.
06-source-audit-initial.log and 08-source-audit-all.log show no new
Admitted/admit/Axiom/Parameter. Baseline unrelated admissions are disclosed
by the global lexical audit and are not selected as new dependencies.

check-assumptions.sh is the required all-exported-theorems query, to run
through the resource gate only after success. A source audit is not a
transitive assumptions certificate. Accepted x03 reports inherited
Stdlib FunctionalExtensionality.functional_extensionality_dep; this unit
must not silently claim a closed trust base from that prerequisite report.

## Final handoff obligations

No successful x09 target command exists. The successful operations are the
source audits, exact arithmetic diagnostic, prerequisite compiles within
the failed full-target command, and ancestry/source-retention checks.
Raw compiler stdout/stderr and exit 1 are in 07-full-vo-initial.log.

Print Assumptions output for x09: **unavailable**, because there is no
successful full module. tools/print-assumptions.sh was not invoked after
failure because it would rebuild the failed target, violating immediate
Astra-to-Sol handoff. check-assumptions.sh lists all 11 intended queries.
No transitive-assumptions completion claim is made. The known prerequisite
baseline uses FunctionalExtensionality.functional_extensionality_dep; its
existing raw report is notes/x03-avx-overlap-forward-fix/12-assumptions.log.

The Sol fixer must retain the statements unless genuinely wrong and explain
every statement change. Restore the four Abort proofs from the exact
archive, discharge dispatch, complete row/return and nonvacuity proofs,
run the full target and all assumptions queries through the 3000000-KiB
resource gate. Resolve the zero-dispatch region with an actual encoded-IL
counterexample or an exact-domain result before claiming x09 complete.
The conditional nonzero-branch result alone is not the full assigned unit.
Do not strengthen to n<2^63 or assume the desired copy result.

Only the assigned prerequisite forest plus this unit's local scoped commit
is allowed. Final SHA, clean status, merge-base, full above-origin log, and
diff stat are recorded after commit in the unit's permitted external
evidence directory. No publication, push, PR, or remote write occurred.
