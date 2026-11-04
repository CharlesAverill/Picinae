# r06-task-count — PARTIAL Astra handoff

Initial author model: `gpt-6-astra`, xhigh. Final proof model: **none**.
The required single full target build failed. No second Astra proof build,
repair cycle, or delegation was performed. A new `gpt-6.1-sol` xhigh/priority
fixer is required. Nothing was installed, pushed, or published.

Branch: `llm-proofs/r06-task-count`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-9eb1e5fb`.
Reviewed prerequisite HEAD: `95da7ab7cee78f09a528aed86c1dfaf29520a9a8`.
Pinned origin/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Result and exact failure

`initial-build.log` contains the full command, compiler stdout/stderr, and
actual exit code **1**. The command was:

```bash
env PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536 \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_uxTaskGetNumberOfTasks_proof.vo'
```

```text
File "./Examples/FreeRTOS/armv6m_uxTaskGetNumberOfTasks_proof.v", line 99, characters 17-18:
Error: Stack overflow.
```

This is in `task_count_witness_models`, at the tactic alternative
`first [exact B | apply ones_bound | apply task_count_zero_bound | reflexivity]`.
No diagnosis has been tested. Avoid conversion of the enormous concrete
memory-width power while fixing this helper; retain abstract-width bounds.
The resource cap was not raised.

The core dependency closure, ARMv6-M ISA and unchanged generated getter
compiled during this build. The proof module did **not** produce a successful
full `.vo`. There are **no successful proof-target commands** to report.
The compiler passed the earlier Qed commands for `task_count_nwc`,
`task_count_welltyped`, `task_count_preserves_memory`, and
`task_count_zero_bound`, but that is not a module completion certificate.

`initial-attempt.v.txt` preserves the entire initial proof verbatim; SHA256
`1e53620c5784c7a203b34298032bcb926246b27b07a97de513318d9c8b1bb197`.
The active `.v` retains the prefix and replaces the failed helper and all
subsequent unchecked proofs with `Abort`. All eleven statements are preserved
verbatim, verified in `statement-audit.log`. The aborted statements declare
no theorem constants. This packaging edit was not rebuilt under the one-shot
policy. Restore the initial attempt when continuing; do not weaken statements
without documenting a genuine specification error.

## Intended specification, not a completed result

- `task_count_correct`: `satisfies_all` partial correctness of the actual finite
  generated `uxTaskGetNumberOfTasks_armv6m_prog`, entry `0x59c`, first BX LR at
  `0x5a0`, with a modeled ARMv6-M entry store.
- `task_count_post_at_bx`: R0 equals the **initial** memory's four-byte
  little-endian word at `0x20000030`; all variables except R0/R3 are unchanged.
  Requires an actual execution trace with no earlier designated exit.
- `task_count_preserves_callee_saved`: R4–R11, SP and LR frame at BX LR.
- `task_count_entry_satisfiable`: for every well-sized memory value, a modeled
  readable entry store with that memory and odd LR. Its supporting model
  witness was the first failed proof, so nonvacuity is still unvalidated.
- `task_count_return_step` and `task_count_caller_result`: ordinary modeled
  odd-LR branch, destination `LR & (2^32-2)`, state unchanged by BX LR.

There is no arbitrary count, nonzero, size, overlap, path-length, CPU-feature
or tunable restriction. Read permissions arise from actual execution premises;
the intended witness provides all address permissions. Literal folding remains
a trusted immutable-code assumption. The proof does not assert that the global
equals task-object cardinality, ISR atomicity, termination, hardware refinement,
or EXC_RETURN behavior. The broad IL branch lemma must not be advertised as an
exception-return theorem.

## Audits and assumptions

`final-source-audit.log` records the required whole-tree source audit against
the pinned base: exit **0**, `NEW totals: {}`. Baseline unrelated files still
contain seven `Admitted`, one `admit`, and 89 module-interface `Parameter`
tokens. `final-unit-source-audit.log` is also exit **0**, with no such tokens
in this unit. Lexical audits do not certify transitive assumptions.

**Print Assumptions was not run:** the initial full proof build failed and the
main statements are aborted. Invoking `tools/print-assumptions.sh` would run a
second build and query nonexistent constants. There is no raw assumptions
output or transitive-assumption completion claim for this unit. The inherited
baseline `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`
is documented in e00; the initial return attempt also explicitly uses
extensionality. A fixer must query every completed main theorem and inspect
actual dependencies, rejecting imported admissions.

## History and unchanged artifacts

`fork-check.log`: exact remote branch-name collision check succeeded, exit 0,
with no matching ref, before renaming this worktree's prepared branch.
The initial sandbox network check could not resolve github.com; the successful
read-only retry used approved network access. Git metadata was read-only in
the sandbox, so the authorized rename and fast-forward used approved access.
No other local branch or remote ref was changed.

`ancestry-prepared.log` records clean e00 HEAD, its base, log and diff stat.
`ancestry-prerequisites.log` records the reviewed fast-forward and full diff
stat; its only untracked item is this unit's newly created evidence directory.
`ancestry-check.log` verifies the exact eight prerequisite commits:

```text
71470bffba65392adf1873a3df9f0cf0ca4f1ac9 e00
59f696d32a5623cdfbceb9a1e0f91e2cc7c054c1 e03
dac36c0a03088a90bb6e6385f82cb355d27cc204 e03/e00 merge
5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b e03 validation
abe7eda601a63d47eb70e765f4ae2c4ca235cca4 e04
8c01958e73ec7fe959c60b29444505afbb599d13 e05 prerequisite merge
075f59aca328e60e6376e2af01fa49925ab10e9d e05 artifacts
95da7ab7cee78f09a528aed86c1dfaf29520a9a8 e05 evidence
```

The accepted external `e05-accepted-leaf-artifacts.json` gate and this getter's
manifest were read: no call closures or critical/IRQ prerequisites. Full e05
remains partial. Generated getter SHA256 is unchanged:
`d237568eb2e532018e17575cf35830200626e9a48ea6f0004f81e6139f51b63e`.
No generated lift, ISA, frontend, fixture, or r00 list model was edited.
The root Dune addition is one explicit handwritten module outside the e05
generated block. Only this unit's local commit follows the reviewed checkpoint.
