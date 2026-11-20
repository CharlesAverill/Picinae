# r10-suspend-all — PARTIAL: initial full build failed

Initial author: OpenAI `gpt-6-astra`, reasoning effort `xhigh`, service tier
`default`. One-shot author policy applies. No final proof producer is claimed.
A new `gpt-6.1-sol`, xhigh/default fixer is required; this author did not repair
the failed attempt or launch another proof build.

Assigned branch: `llm-proofs/r10-suspend-all`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-d8b8261f`.
Pinned origin / merge base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Exact assigned prerequisite: `5fec2fc24d0c739bafc08add426f02a3085e15cd`.
Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole
parent is the pinned origin. The permitted prerequisite union includes the
reviewed e03/e04/e05 artifacts and r06 original/Sol completion history.
Only the assigned prerequisite was fast-forwarded; no unrelated history was
imported. The remote branch collision check exited 0 with no result before
renaming only the prepared branch. No remote writes or installs were done.
The initial sandbox DNS and Git-metadata permission errors were resolved by
approved escalation of the same read-only remote check/local Git operations.
The initial tree was clean before creation of this unit's notes.

## Specification

`Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.v` uses the actual finite
`vTaskSuspendAll_armv6m_prog`; the generated file remains byte-identical.
Entry: `0x574`. Exit: first `0x57c`, immediately before `BX LR`.
Pinned V11.1.0 source/config/layout evidence establishes the four-byte
`uxSchedulerSuspended` object at `0x20000008`, offset zero, and
`configNUMBER_OF_CORES=1`. No guessed struct offsets are used.

The exact memory postcondition writes `(1 + initial_word) mod 2^32` to that
word in the original memory. The byte corollary describes all four stored
little-endian bytes and preserves every 32-bit address outside
`[0x20000008,0x2000000c)`. The register frame preserves every variable except
memory, R2, R3, and NZCV, including R0/R1/R4-R12/SP/LR, all permission maps
and all temporaries. The callee-frame corollary explicitly names R4-R11/SP/LR.
No result-register guarantee is needed for this void function.

Main declarations:

- `suspend_all_correct`: `satisfies_all` partial correctness from typed entry.
- `suspend_all_post_at_bx`: exact memory and register frame on an actual
  execution reaching the first exit cut.
- `suspend_all_original_memory_effects`: original-memory word increment,
  four individual byte values, and outside-byte frame.
- `suspend_all_preserves_callee_saved`: R4-R11/SP/LR preservation at that cut.
- `suspend_all_return_step`: actual guarded ordinary `BX LR` step, odd LR
  below `0xfffffff0`, with unchanged whole post-store state.
- `suspend_all_caller_result`: combines the endpoint post and actual return
  step using the original LR and its preservation.
- `suspend_all_entry_satisfiable` and `suspend_all_entry_nonempty`: typed,
  read/write-permitted witnesses for arbitrary bounded memory and arbitrary
  odd ordinary-return LR, plus an explicit inhabited case.
- `suspend_all_nwc`, `suspend_all_welltyped`: code independence and typing.

The input memory bound is exactly `m < 2^(8*2^32)` (architectural typing).
There is no counter/nonzero/size/overlap bound, and wraparound is included.
The endpoint results require the real execution and first-exit premises;
permissions are enforced by that execution relation. There is no callee
contract or unconstrained oracle. No termination, hardware/IRQ, atomicity,
whole-kernel/cardinality result, CPU-feature or tunable-generalization, or
binary/lifter refinement is asserted. The inherited folded literal pool is
immutable code evidence, not a mutable-memory assumption in the theorem.

## Evidence

All recorded commands and true exits are under `logs/`.
`initial-attempt.v.txt` is the exact initial author source; its SHA256 is
`50f84eb3cf4b90cf8ac40dac817e929faed92c5a6981a0470a606b1b524ee87b`.
`07-initial-build.log` records the single initial full `.vo` target command,
under the shared admission helper, 1,750,000 KiB address-space cap,
65,536 KiB stack, `-j1`, and `--cache=disabled`. Queue delay is not a failed
proof attempt. No concurrent proof compiler runs within this unit.

`audit-provenance.py` checks pinned ELF/source/config/layout/symbol/lift hashes
and prints source/config/disassembly evidence. `08-provenance.log`: exit 0.
`audit-ancestry.py` enforces the exact assigned prerequisite union plus
only scoped local unit commits. `09-ancestry-prerequisite.log`: exit 0.
`06-source-audit.log`: repository-wide source audit against pinned origin,
exit 0, no new admissions, axioms or parameters. Existing unrelated baseline
admissions are reported honestly; this source audit is not an assumptions
certificate. The inherited core uses
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
actual transitive assumptions must be inspected before completion.

The explicit root Dune list adds only this proof (its lift was already
listed by e05); `@r10-suspend-all` names exactly its `.vo` target.

## Initial build failure and handoff

The shared gate admitted the single initial build after a RAM-reserve wait.
The exact Dune command was:

```sh
dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.vo
```

It exited **1**. Full compiler stdout/stderr and command/limits are verbatim
in `logs/07-initial-build.log`. The failure is at original source line 139,
characters 27-38, in `suspend_all_memory_word`:

```text
Error: In environment
m : memory
Unable to unify "2 ^ 32" with "4".
```

The initial proof used `rewrite getmem_setmem by reflexivity`; the concrete
inequality side condition was not solved by that tactic. No repair was
attempted. The compiler reached and accepted the preceding six declarations
in this run (nwc, typing, zero bound, typed witness, arbitrary-memory entry
satisfiability, nonempty entry); these remain as their original Qed scripts.
There is **no successful full unit .vo target**, so these are not represented
as a separately delivered full-module certificate.

The failing memory-word lemma and every later declaration are retained with
**identical statements** and `Abort` in the active `.v` file. The exact initial
proof bodies remain in `initial-attempt.v.txt` with its original hash. No new
admission, axiom, or parameter was introduced. The original definitions and
all 16 statements are checked by `audit-statements.py`.

Actual certified unit functional-correctness coverage: **none**. The listed
main theorem names describe proposed statements, not available constants.
No unit `Print Assumptions` query was executed because the full module did not
compile; the assumptions helper would re-run the build, contrary to the
one-shot handoff policy. There is therefore **no raw unit assumptions output**
and no claim that transitive assumptions have been certified. Baseline FE is
disclosed above, not substituted for a unit certificate. The prepared
`print-all-assumptions.sh` queries all 16 declarations after a Sol completion.

Remaining work: restore the archived attempt, fix proofs without changing
statements unless genuinely wrong (explain any such change), complete the
full exact .vo target through the same capped admission gate, run all 16
Print Assumptions queries, and inspect every transitive dependency. The
original-memory increment/byte frames, main invariant, callee frame, and
ordinary return are unvalidated. No termination/binary/hardware claim follows.
The active Abort handoff was not recompiled: doing so would constitute a
second author build, and a successful Abort-only module would not certify
these theorems anyway.
