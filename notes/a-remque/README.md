# a-remque: PARTIAL Astra handoff

Status: PARTIAL. The single gated full target command exited 1 after the author
interrupted only this unit's verified compiler, following over ten minutes of
inconclusive checking. The interruption was a discretionary runtime cutoff,
not an assigned time limit, a memory-cap failure, or an ordinary tactic error.
No full target `.vo` was produced. No second Astra build or repair was run.

Author: gpt-6-astra, xhigh. Assigned service tier: default. Final proof
producer: none (unfinished). No subagents, dependency installations, pushes,
PRs, or remote writes were performed. The only remote operation was the
required read-only branch collision check (exit 0, no matching head).

Worktree: /home/charles/.t3/worktrees/Picinae/t3-7d6e98da
Branch: llm-proofs/a-remque

The prepared branch started clean at e00
71470bffba65392adf1873a3df9f0cf0ca4f1ac9. Its parent and the pinned origin base
are 49956416928e5b6bb3928b54ae33e3b81091f006. It was fast-forwarded to the
explicitly authorized e08 checkpoint 9ae8e6800fa044797efd98372857e6ac89b18e1b,
then only the prepared branch was renamed. The allowed pre-unit forest is
exactly origin..e08, including the reviewed e02/e11 merge ancestry. No fork
branch was used as a base. `ancestry-before.log` includes untracked unit notes
created to hold the log; the preceding initial `git status --short` was empty.
`prepare.log` and `prerequisite-ancestry.log` preserve full ancestry and stats.

The generated map is unchanged, SHA256
f5e9a68f3f18417286f28d58b38014aa62646bf6ed237a8113c47bdc1a01c13a.
Only the new proof module and its exact Dune alias were added to the inherited
explicit module selection; no unrelated module was newly selected.

The initial attempt is preserved byte-for-byte in `initial-attempt.v.txt`,
SHA256 18b7fa70349834a758a6f45f018dd98da6f0f196812664ead382de997ebf38e2.
The target is Examples/claude/arm8_remque_proof.vo, full `(mode vo)`.
`run-build.sh` contains the exact shared gate invocation, memory cap 1750000
KiB, stack 65536 KiB, `-j1`, and disabled cache. `initial-build.log` captures
compiler stdout/stderr and the real exit code through record-command.sh.
Gate waiting is not a build failure. No second Astra build is authorized.

Attempted statements:

- remque_exact: all four defined IL paths from 0x1e4600 to the pre-RET boundary
  0x1e4614, original-memory links, ordered conditional writes, unchanged SP/X30.
- remque_correct: the same with readable nonwrapping 16-byte elem and the
  conditional writable nonwrapping 8-byte fields. No disjointness, CPU,
  tunable, alignment, or callee-contract hypotheses.
- remque_byte_frame / remque_post_byte_frame: every byte outside the two
  original-link conditional write intervals is unchanged.
- remque_preserves_callee_saved: X18-X30, SP, full modeled Z8-Z15, all traces.
- remque_ret_exec: execution witness for the actual map's RET statement,
  assigning PC from X30 and jumping to X30.
- remque_path_empty / next_only / prev_only / both: exact memory path formulas.
- remque_witness_fields / typed / arbitrary_witness and concrete empty,
  singleton, shared-sentinel, nonempty, next-only and prev-only witnesses.

The witnesses establish local node/link shapes and permissions, not a global
finite circular-list representation. The exact contract permits neighbour
and node aliases. It does not assert that elem remains unchanged if its own
bytes are written via aliases. The whole function contract is partial
correctness at the return boundary, not a termination or hardware/binary
refinement theorem. Provenance remains the accepted e08 scalar replacement.

Source audits against the pinned origin base are in initial-source-audit.log
and full-source-audit.log; both returned 0 with no NEW tokens. Existing
unrelated baseline admissions are inventoried, not imported by this module.
The generated lift's own raw Print Assumptions is part of initial-build.log:
FunctionalExtensionality.functional_extensionality_dep is inherited. This
alone does not certify the new theorems' transitive assumptions.
`run-assumptions.sh` lists every intended query using tools/print-assumptions.sh
inside the same resource gate. It may run only after a successful initial
build; it must NOT trigger an unauthorized second build after an Astra failure.

## Exact failure and handoff

The final compiler diagnostic was:

```
Goal at < 1984000 >
Goal at < 1984020 >
Goal at < 1984020 >
Goal at < 1984020 >
Goal at < 1984020 >
File "./Examples/claude/arm8_remque_proof.v", line 223, characters 27-192:
Error: User interrupt.
```

This is the tactic sentence in `remque_witness_typed`, not the main execution
proof. Earlier Qed commands were processed before this location, including
remque_exact, remque_correct, the memory/register frames, actual RET execution,
path identities and remque_witness_fields. There is still NO successful full
proof-module build, NO reusable proof-module .vo, and NO transitive assumptions
certificate for any of these new results. No completed-unit claim is made.

The exact unchanged attempt remains in initial-attempt.v.txt. The active proof
file retains the processed prefix, and changes the eight proofs from
remque_witness_typed onward to Abort. ALL statements/definitions are retained;
only unfinished proof bodies are removed from the active source. This is WIP
packaging, not a repair attempt. No build was run on that packaging. A source
comparison verifies the identical statements and the unchanged attempt hash.

The coordinator must launch a NEW gpt-6.1-sol xhigh/default fixer. Restore the
archived initial attempt to work from the original proof bodies; retain the
statements unless genuinely wrong and explain every statement change. The
first diagnostic locus involves witness-store typing and giant symbolic
memory/permission bounds. Investigate reduction there; this is a clue, not a
verified fix. Complete every witness, the full .vo build and transitive
Print Assumptions with the same gate/cap. No subdelegate was launched here.

No tools/print-assumptions.sh query was executed for the new proof module:
it would attempt another build after the one-shot failure. The prepared
run-assumptions.sh is for the succeeding fixer after a successful full build.
generated-assumptions-raw.txt is copied VERBATIM from the generated lift's
own successful build query. It reports only the inherited
FunctionalExtensionality.functional_extensionality_dep. It is not an audit of
the new proof prefix or any aborted statement. Main-theorem assumptions remain
unavailable. Full completion, witness certification, all transitive audits,
and any termination/global-list/binary-refinement result remain outstanding.

The first staged whitespace check returned 2 solely for a trailing space in
interrupt-build.log's verbatim `/proc/PID/cmdline` rendering. The raw log is
intentionally preserved. The scoped source/documentation whitespace check
returned 0; this packaging check did not run any proof compiler.
