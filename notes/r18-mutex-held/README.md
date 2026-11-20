# r18-mutex-held author checkpoint

Initial author: gpt-6-astra, reasoning xhigh, requested service tier default.
Status: PARTIAL. Final proof producer: none. Local-only branch `llm-proofs/r18-mutex-held`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-48d97224`.

The sole initial proof attempt is preserved byte-for-byte in
`initial-attempt.v.txt`, SHA256 recorded in `06-initial-source.log`.
The one full build command and raw stdout/stderr/exit are in
`08-initial-build.log`. Admission waits do not count as compiler attempts.
No installation, publication, subdelegation, or shared-environment edits.

Prepared HEAD was the clean e00 commit
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent
`49956416928e5b6bb3928b54ae33e3b81091f006`. The read-only remote branch check
succeeded with empty output before the prepared branch was renamed. An initial
sandbox DNS failure and an initial Git metadata read-only failure were retried
with approved escalation. No remote mutation occurred. The checkout was advanced
only by ff-only merge to assigned prerequisite
`5fec2fc24d0c739bafc08add426f02a3085e15cd`.
`audit-ancestry.py` checks the exact ten prerequisite commits, unit branch,
pinned origin, scoped subsequent commits, and generated lift hash.
The accepted r06 proof and its preserved partial author history are inherited;
the new proof imports only the ISA and its own generated lift, not r06.

Provenance validation (`05-provenance.log`) checks the actual isolated pinned
FreeRTOS V11.1.0 tasks.c against the manifest, plus committed configuration,
layout and generated-source hashes. It records the precise C body, opcodes,
immutable literal and global symbol. `pxCurrentTCB` is at `0x20000108`;
`uxMutexesHeld` is offset 72 in the 84-byte, alignment-4 TCB. Both pointer and
UBaseType_t sizes are 4. The call-free eight-instruction map is unchanged.
No binary-to-IL refinement has been proved.

## Intended declarations and coverage

- `mutex_held_correct`: all-path sequential invariant partial correctness,
  typed input, entry `0x153c` and first BX cut `0x154a`.
- `mutex_held_post_at_bx`: executed trace returns original current pointer in
  R0; NULL leaves memory unchanged; non-NULL increments the original count
  modulo 2^32 with exactly one four-byte little-endian store.
- `mutex_held_memory_frame`, `mutex_held_written_bytes`,
  `mutex_held_count_increment`, `mutex_held_null_memory`: original-memory
  algebraic effects, including wrapped addresses and possible aliases.
- `mutex_held_register_frame`, `mutex_held_preserves_callee_saved`: R4-R11,
  SP, LR, permissions and other untouched variables. R0/R3/N/Z/C/V may change.
- `mutex_held_entry_models`, `mutex_held_entry_satisfiable`,
  `mutex_held_current_satisfiable`: typed/permitted input witnesses for every
  typed memory and every 32-bit current pointer, including zero. No callee
  contract or assumed functional result.
- `mutex_held_return_step`, `mutex_held_caller_result`: actual ordinary BX and
  trace extension under odd LR below `0xfffffff0`.
- `mutex_held_nwc`, `mutex_held_welltyped`: immutable finite map and typing.

No size/count/nonoverlap/alignment/tunable/feature restriction in the IL
contract. Valid C-object interpretation separately needs the recorded object
layout. Permissions arise from actual execution in the correctness theorem;
explicit permitted input witnesses are supplied, without a full execution
existence/termination claim. No IRQ, hardware exception-return, concurrency,
whole-kernel or scheduler cardinality result.

## Trust and validation status

The baseline contains unrelated admitted examples and module interface
parameters. `07-source-audit.log` inventories these and reports no new tokens.
The expected inherited core assumption is
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`, as
disclosed by e00/r06; only actual raw transitive queries may certify the new
proof. A source audit alone is not that certificate.

## First build result and mandatory Sol handoff

The single gated full `.vo` target build exited **1**. Core prerequisites and
`pvTaskIncrementMutexHeldCount_armv6m.vo` built successfully. The proof module
failed at original line 184, characters 34-55, within
`mutex_held_current_satisfiable`:

```
Unable to unify "(0 ?= 2 ^ ?M1535) = Lt" with "(0 ?= memsize 32) = Lt".
```

The first ten declarations, through `mutex_held_entry_satisfiable`, were
processed with Qed before the failure. There is **no full proof .vo**, so they
are not presented as a completed module certificate. Six subsequent
statements are retained verbatim with `Abort`: `mutex_held_current_satisfiable`,
`mutex_held_correct`, `mutex_held_post_at_bx`,
`mutex_held_preserves_callee_saved`, `mutex_held_return_step`, and
`mutex_held_caller_result`. Their exact initial proof bodies remain in
`initial-attempt.v.txt`. No second Astra compile or repair cycle was run.

No new-theorem Print Assumptions output is available. The provided
`query-assumptions.sh` is a **not-run recipe**, not evidence. Running the helper
now would rebuild the failed or aborted target and cannot certify missing
constants. The ten completed-prefix declarations also await transitive
assumptions inspection after the fixer builds the full module. The inherited
FE assumption is documented, not asserted to be the only assumption of these
unverified main statements.

Coordinator action: launch a NEW gpt-6.1-sol fixer, xhigh/default, from this
local checkpoint, preserving all 16 statements unless genuinely wrong (and
explaining every change). First resolve the memory-bound unfolding error;
then validate the untested invariant/branch proof and return corollaries.
Keep the same 2,000,000 KiB cap, resource gate, stack 65536, -j1 and disabled
cache. Run the exact full target and all 16 transitive assumption queries;
source audit success alone is insufficient. No functional correctness,
termination, complete binary soundness, or done status is claimed here.
