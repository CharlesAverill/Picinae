# r19-scheduler-state — PARTIAL handoff

Initial author model: `gpt-6-astra`, reasoning `xhigh`, assigned service tier
`default`. Final proof producer: none. No unit theorem was kernel checked.
Branch: `llm-proofs/r19-scheduler-state`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-43c5d429`.

The exact prepared e00 HEAD was `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
After the successful empty fork branch check, only the prepared branch was
renamed and fast-forwarded to the assignment-specific prerequisite
`5fec2fc24d0c739bafc08add426f02a3085e15cd`. Its ten commits above origin are
accepted prerequisites, including the r06 author checkpoint and Sol completion.
The script `audit-ancestry.py` checks this exact allowed set plus scoped own
commits. No other branch changed; no publication or installation occurred.
The first tool inspection recorded a clean starting tree; `01-before.log`
already includes this unit's newly created evidence directory.

`initial-attempt.v.txt` is the exact one-shot proof, SHA256
`d7db5e3a1d34a8ad8ba713349e3c17af3548e2968a02f134636bd08b6aa9f4d7`.
`audit-statements.py` enforces the 13 original statements and seven definitions.
`09-initial-build.log` records the single attempted full Dune target, stdout,
stderr, admission waits, and true exit code. The resource helper applies
1,750,000 KiB address space and 65,536 KiB stack limits; Dune uses one job,
cache disabled, full `.vo` mode, and this worktree's isolated `_build`.
`assumptions-command.sh` is the gated query command for all 13 named facts,
using the required `tools/print-assumptions.sh`. It is run only after successful
full validation. No query result is inferred from source inspection.

The specification is over the unchanged finite e05 program. At entry 0x12fc
there are no register arguments. Original little-endian words at 0x20000024
(`xSchedulerRunning`, four bytes, object offset zero) and 0x20000008
(`uxSchedulerSuspended`, four bytes, object offset zero) determine the result
at the sole BX cut 0x1310. The branch at 0x1304 returns 1 when running=0;
otherwise actual NEG/ADC/LSL returns 2 when suspended=0 and 0 otherwise.
The planned frame preserves all variables except R0/R3/N/Z/C/V, including
all memory bytes, callee registers, SP, LR, permissions, and temporaries.
The separate actual modeled BX step requires odd LR below 0xfffffff0 and
clears its low bit. `scheduler_state_caller_result` combines those properties.

The functional theorem assumes a modeled initial store and exact entry;
post-at-exit corollaries additionally assume an actual `exec_prog` trace and
no earlier designated exit. Permission premises are supplied by actual loads.
`scheduler_state_entry_satisfiable` supplies a typed store for every bounded
modeled memory and every odd LR below 0xfffffff0, readable at both four-byte
globals. No Boolean restriction on either global is imposed. The arithmetic
helper is universal in the word, with no extra contract premise. There are no
calls or callee contracts, input pointers, size/overlap/path exclusions, CPU
feature or tunable hypotheses. No IRQ/concurrency/whole-kernel/cardinality,
termination, hardware exception-return, or binary/lifter-refinement claim.

Pinned source/config/layout evidence and checked hashes are in
`06-evidence.log`, reproducible with `inspect-evidence.py`. The source is
FreeRTOS V11.1.0 commit `dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`,
ELF SHA256 `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
The generated lift SHA256 remains
`079c2ba35ac01da4db0ec699cdda334fc68bf870f396a448e2410b38cd4c04c8`.
Folded literal pools are trusted immutable code. This unit does not extend
accepted e05 call-free artifact evidence into a whole-lifter soundness theorem.

Both scoped and full source audits against pinned origin pass with no new
admissions, axioms or parameters. Full-tree baseline inventory is unchanged:
seven `Admitted`, one `admit`, 89 `Parameter` tokens. These lexical totals
are not transitive assumptions. Baseline/r06 main proofs disclose
`FunctionalExtensionality.functional_extensionality_dep`; the unit may report
it only after its own raw query succeeds. Any other admitted dependency
prevents a completion claim.

## First build outcome and required handoff

The single full target build exited **1** after successful `.vo` builds of
Picinae_core, Picinae_theory, Picinae_statics, Picinae_finterp,
Picinae_simplifier_base, Picinae_ISA, Picinae_simplifier_v1_1,
Picinae_armv6m and xTaskGetSchedulerState_armv6m. No successful unit target
command exists. This was a syntax error, not a memory-cap failure:

```
File "./Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v", line 12, characters 55-56:
Error: Syntax error: illegal begin of vernac.
```

The initial header's `sizeof(void*)` accidentally terminates the Rocq comment.
No unit theorem was reached. In accordance with the one-shot Astra policy,
there was **no second proof/build cycle and no assumptions run**. No raw
`Print Assumptions` output exists for this unit, and no transitive certificate
is claimed. The exact initial source and diagnostics remain archived.

The active file is now an explicitly PARTIAL scaffold: seven original
definitions and all 13 theorem statements are preserved verbatim, with every
proof ending in `Abort`. Its header spelling is sanitized to `sizeof(pointer)`
solely to make the scaffold readable as Rocq; this scaffold is **not rebuilt**
and is not a validation claim. There are no new admissions, axioms or parameters.
No completed helper is claimed, because even the first theorem was not reached.

Coordinator: hand this commit to a NEW `gpt-6.1-sol`, xhigh/default fixer.
Restore the initial attempt, correct the header delimiter, and complete the
proof under the same cap and shared admission gate. Retain all definitions and
statements unless genuinely wrong; document every statement change. Run the
full target successfully, then the supplied gated assumptions command and
source/ancestry audits. All functional, witness, frame and return proofs remain
unvalidated. Do not publish or modify the original author branch.
