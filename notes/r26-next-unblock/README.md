# r26-next-unblock PARTIAL author handoff

Initial author: gpt-6-astra, xhigh/default. Final proof model: none certified.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-86e7a14d.
Assigned local branch: llm-proofs/r26-next-unblock. Publication is not authorized.

The one-shot source is preserved verbatim in `initial-attempt.v.txt`. The full
`.vo` build command, resource admission messages, compiler output, and real
exit status are in `05-initial-build.log`. No second Astra repair/build cycle
is authorized after a compiler failure. The coordinator must launch a NEW
Sol xhigh/default fixer on failure; the fixer must preserve these statements
unless genuinely wrong and explain any statement changes.

## Specification

The finite unchanged generated program is call-free. It enters at 0xc6c,
branches at 0xc74, and both paths meet at the pre-BX cut 0xc7e. The nonempty
path is 0xc80..0xc8c. Immutable code literals point to pxDelayedTaskList at
0x20000078 and xNextTaskUnblockTime at 0x20000010. Original memory determines
the list pointer, count at offset 0, head pointer from xListEnd.pxNext at
8+4=12, and head item value at offset 0. Empty count selects 0xffffffff;
nonzero count selects that head value. A single four-byte little-endian
store updates the output global. All other bytes retain ORIGINAL memory.

The main statement uses arbitrary typed initial stores, with no nonnull,
alignment, count, nonoverlap, or head-value restriction. Execution traces
supply read/write permission requirements. The all-readable/all-writable
witness supports every typed input memory and odd ordinary LR=1. This is a
sequential IL partial-correctness claim; modular-address aliasing is allowed
because every load precedes the only store. It is not C memory safety or a
valid scheduler/list-cardinality theorem. The optional list-header projection
connects the actual sentinel layout to the raw reads. The byte frame has the
explicit output-region nonoverlap hypothesis. R0/R1/R4-R12/SP/LR, permissions,
and temporaries are framed; R2/R3/NZCV/memory may change. The separate actual
BX step requires odd LR below 0xfffffff0 and preserves its input store.
No callee or kernel oracle, CPU IRQ model, hardware claim, termination, or
binary/lifter refinement is introduced.

Source/config/layout/global-address evidence is in `04-provenance.log`, from
pinned FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0 and accepted
ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
The generated lift hash is verified against the accepted e05 manifest.

## Ancestry and environment

Started clean at e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9, whose parent
is pinned origin 49956416928e5b6bb3928b54ae33e3b81091f006. Fast-forwarded only
to assigned prerequisite 4ff26413448da4d8f064b0273ac5472cc9de7e5a. Its eleven
accepted commits include the e03/e04/e05/r00 histories and their reviewed
merges. Only scoped r26 commits may follow. No other branches changed.
The read-only remote collision check succeeded empty before local rename.
Initial sandbox network/Git-metadata restrictions were retried with approved
escalation; no remote write occurred. `audit-ancestry.sh` checks the pinned
base, prerequisite, exact ancestry union, scoped subsequent commits, and
unchanged protected lifts/config/layout/core artifacts.

No dependencies installed. The shared toolchain is used read-only. Every
compiler must enter the assigned resource admission helper with memory cap
2000000 KiB, stack 65536 KiB, `-j1`, and `--cache=disabled`. Admission waiting
is not a failed proof attempt. There are no concurrent compilers in this unit.

## Assumptions

A source audit alone is not a transitive certificate. The inherited r00
validation has nineteen closed facts. Baseline main execution theorems can
use Stdlib FunctionalExtensionality.functional_extensionality_dep; that
inherited axiom must be reported if present in the final query. Any imported
admitted proof disqualifies completion. No assumption claim is made for an
unbuilt main theorem.

## Final status: PARTIAL, hand off to a new Sol fixer

The SINGLE full target build exited 1. Dependencies compiled successfully,
including Picinae_armv6m.vo, armv6m_list_model.vo and the unchanged generated
prvResetNextTaskUnblockTime_armv6m.vo. The new proof target did NOT produce a
successful .vo. Rocq reported signal ABRT and `Fatal error: out of memory`
after printing `Goal at < 3180 >` and twice `Goal at < 3198 >` (entry 0xc6c
and return cut 0xc7e). This localizes the failure to next_unblock_correct,
but does not establish whether the allocation failed in a closing tactic
or kernel checking. No precise allocation culprit is claimed.

The first ten declarations precede that main theorem and were traversed by
the failed compiler. Their unchanged Qed proofs remain as completed helper
source. They have NO separate full-module/assumptions certification in this
unit. All six main execution/return statements, from next_unblock_correct
through next_unblock_caller_result, are preserved verbatim as Abort in the
active source. The initial entire one-shot proof remains byte-for-byte in
initial-attempt.v.txt. No proof repair was attempted. No main theorem is
exported or claimed proved. The root Dune module entry and exact target
alias remain for the fixer.

No second Dune/Rocq build or Print Assumptions run was made after failure,
as required by the Astra handoff policy. `tools/print-assumptions.sh` itself
builds the target, so running it would start an unauthorized second compiler
cycle. `assumptions-status.txt` records that limitation; there is no invented
raw assumptions output. The sixteen required query names are in
assumptions-targets.txt. The fixer must complete and kernel-check the exact
statements under the same gate/cap, then run that helper and inspect all
transitive assumptions, honestly recording inherited FE if present.

Remaining work: complete the main finite-program correctness proof, derive
actual trace memory/register-frame corollaries, check the guarded ordinary
BX and caller theorem, successfully build the full target, and query every
main/helper theorem. Consider abstract-memory/cut lemmas to reduce memory,
without changing the specification. Any genuine statement correction needs
an explicit explanation. No new admission, axiom, or parameter was introduced.
