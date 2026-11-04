# r07-current-task-fix

State: **DONE** for the 13 exact sequential IL statements below. The full
`.vo` target, all 13 transitive assumptions queries and all audits succeeded.

author_model=gpt-6-astra
final_proof_model=gpt-6.1-sol
Reasoning effort: xhigh. Requested service tier: default.
Branch: `llm-proofs/r07-current-task-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-02095182`.
Exact author checkpoint: `393e57f7973bbc0ea29e56902816e1ceb92cb20f`.
Pinned origin: `49956416928e5b6bb3928b54ae33e3b81091f006`.

The original Astra attempt, failure stdout/stderr, source hashes and statements
remain unchanged under `notes/r07-current-task/`. The prepared clean worktree
started at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole parent is
the pinned origin. After the successful empty fork branch-name check, only
the prepared local branch was renamed. The import was a fast-forward to the
exact authorized checkpoint. There is no unrelated history and no new merge.
The original author branch stays at its checkpoint. See
`preparation-transcript.txt`, `ancestry-before.log`, `checkpoint-import.log`
and `audit-ancestry.py` for commands, failures/retries and allowed history.

## Repair and preservation

Restored `initial-attempt.v.txt` to
`Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v`, applied the archived
explicit Dune module/alias patch, and replaced the premature comment terminator
in the header with plain pointer-size prose. `attempt-01.v.txt` records the
first restored source. The first gated build then reached the witness theorem
and failed because the final argument of `N.lt_trans` was unresolved when
checking `eq_refl`. The second attempt supplies the explicit upper bound
`2^32`; this changes only proof elaboration. Every original statement and
all eight definitions are retained verbatim. The header also identifies the
fixer and distinguishes the theorem's numeric
LR guard from the inherited IL's Thumb-bit test. No substantive spec or
definition change was needed. No generated map, ISA, prerequisite proof, or
original Astra log is edited. The only Dune additions are this proof module
and its exact-target alias. No globs or unrelated target additions are used.

## Exact proved coverage

The unchanged e05 finite `_prog` is the official single-core FreeRTOS V11.1.0
ARMv6-M Cortex-M0 getter. Its bytes and provenance are inherited, not proved
to refine hardware. Entry is `0x12dc`; the folded literal at `0x12e4` supplies
`0x20000108` to R3. The instruction at `0x12de` loads the four-byte
little-endian `pxCurrentTCB` word into R0. The designated exit is before
BX LR at `0x12e0`. Literal pool immutability and the e05 lift/provenance are
explicit trusted boundaries. The generated map SHA256 remains
`ab04b58fe6006e5fd75b5cf3c44cf5aaf51fabef7f644b12cd55a785c110d6f4`.

The 13 original declarations are:

| Name | Coverage |
| --- | --- |
| `current_task_nwc` | Code does not depend on the store. |
| `current_task_welltyped` | Generated finite program typing. |
| `current_task_preserves_memory` | Whole-memory equality for all actual endstates. |
| `current_task_zero_bound` | A symbolic positive power-of-two bound. |
| `current_task_witness_models` | Typed entry witness for every bounded memory and 32-bit LR. |
| `current_task_entry_satisfiable` | Typed readable witness for every bounded memory and ordinary-return LR, retaining both exactly. |
| `current_task_entry_nonempty` | Explicit inhabited memory-zero/LR-one instance. |
| `current_task_correct` | `satisfies_all` invariant from entry to designated exit. |
| `current_task_post_at_bx` | R0 is the INITIAL memory word; all variables except R0/R3 equal entry. |
| `current_task_preserves_callee_saved` | R4-R11, SP and LR agree with entry. |
| `current_task_return_step` | Actual generated BX step clears LR bit zero and preserves the entire state. |
| `current_task_caller_result` | Combines the result/frame with the actual ordinary BX step. |
| `current_task_original_bytes` | The postcondition entails whole-memory and every-byte equality. |

The functional invariant assumes a modeled initial 32-bit ARMv6-M store and
the exact entry. Exit corollaries additionally require an actual trace to
the designated exit and no earlier designated exit. Actual execution supplies
load permission premises; entry witnesses explicitly provide all four read
permissions. Witness memory is arbitrary below `2^(8*2^32)`; witness LR is
odd and below `0xfffffff0`. The ordinary return theorems use exactly that
odd/range condition, excluding EXC_RETURN tokens. The inherited IL's BX
instruction itself tests the Thumb bit; the extra numeric range is a theorem
scope restriction, not an implemented exception-return model.

There is no input argument, TCB-field load, TCB-validity or nonzero-pointer
condition. All memory, permission variables, flags and all registers other
than R0/R3 are framed. No size, overlap, scheduler-cardinality, CPU-feature or
tunable restriction is introduced. There are no assumed callee contracts.
This is sequential IL partial correctness and an ordinary return step; no
termination, IRQ/atomicity, exception/hardware, whole-kernel or binary/lifter
refinement result is claimed.

## Validation policy and evidence

Every compiler/query must pass through the shared `resource-run.py` gate with
unit `r07-current-task-fix`, memory cap **1750000 KiB**, stack **65536 KiB**,
the read-only isolated `picinae-env` wrapper, cache disabled and `-j1`.
No cap increase, gate bypass, concurrent proof compilers, dependency install,
shared environment/config change or other-process signal is permitted.

`build-01.log` captures the failed first fixer build, including shared-gate
wait messages, full compiler stdout/stderr and exit 1 at line 136. The core
and generated getter dependency closure was fully compiled during that run.
`build-02.log` records the successful full proof target and all 13 assumptions
queries in one gated lease, exit 0. `attempt-02.v.txt` is the exact source
compiled by that successful command, including the final header clarification.
The successful target command inside the required gate was:

```bash
ulimit -v 1750000
ulimit -s 65536
dune build --cache=disabled -j1 --display short \
  Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.vo
```

The next command, under the SAME gate/limits, recorded raw output in
`assumptions.log` via `tools/record-command.sh`:

```bash
PROOF_MEMORY_KB=1750000 PROOF_STACK_KB=65536 bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_xTaskGetCurrentTaskHandle_proof \
  current_task_nwc current_task_welltyped current_task_preserves_memory \
  current_task_zero_bound current_task_witness_models \
  current_task_entry_satisfiable current_task_entry_nonempty \
  current_task_correct current_task_post_at_bx current_task_preserves_callee_saved \
  current_task_return_step current_task_caller_result current_task_original_bytes
```

`validate.sh` provides a reproducible gated target/13-theorem assumptions
query followed by source/declaration/ancestry audits. It sets
`PROOF_MEMORY_KB=1750000` explicitly
so the assumptions helper does not request its larger default limit.
All commands are recorded by `tools/record-command.sh` with real exit codes.
Only full `.vo` checking counts; no `.vos` or skipped proofs are accepted.

The final whole-tree source audit against the pinned origin passes with
`NEW totals: {}`; the two-file unit source audit has no suspicious tokens at
all. Baseline unrelated admissions and module-interface parameters are
inventoried honestly; they cannot substitute for transitive assumptions
inspection. `declaration-assumption-audit.log` verifies all 13 statements
and eight definitions verbatim, 13 `Qed`s, preserved author evidence and each raw
transitive assumptions report. The eight closed results are `current_task_nwc`,
`current_task_welltyped`, `current_task_preserves_memory`,
`current_task_zero_bound`, `current_task_witness_models`,
`current_task_entry_satisfiable`, `current_task_entry_nonempty` and
`current_task_original_bytes`. The other five results have ONLY the inherited
Stdlib axiom documented in e00/r06; their raw output is verbatim:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Those five are `current_task_correct`, `current_task_post_at_bx`,
`current_task_preserves_callee_saved`, `current_task_return_step` and
`current_task_caller_result`. No imported admission or unproved callee/kernel
contract is present. There is no remaining proof gap within these statements;
the hardware/lifter/termination/concurrency boundaries above remain outside
this unit's claim.

No push, PR, remote comment/write, branch deletion, new worktree or
subdelegation is performed. Final postcommit clean-tree evidence belongs only
under `/home/charles/code/friends/.refs/picinae-llm-proofs/units/r07-current-task-fix/`.
