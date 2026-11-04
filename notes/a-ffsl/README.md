# a-ffsl — PARTIAL, one-shot author handoff

Initial author: **gpt-6-astra / xhigh**. Final proof model: **unset**.
The initial full Dune build exited **1**. No second build or proof repair was
performed. The coordinator must assign a **new gpt-6.1-sol / xhigh / priority
fixer**, retaining the statements unless they are genuinely wrong and explaining
every statement change. This child did not delegate or publish anything.

Branch: `llm-proofs/a-ffsl`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-1290b26e`.
Only prerequisite: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9` (e00-build),
whose sole parent is pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006`.
No prerequisite import was needed. The prepared branch was
`t3/aarch64-ffsl-proof`; only that branch was renamed. The successful read-only
fork collision check had empty output. No fork branch was used as a base.
The first sandboxed remote check failed DNS, and the first sandboxed rename
failed with read-only Git metadata. Both succeeded with authorized escalation;
no automatic approval rejection occurred.

## Build and exact first failure

`first-build.log` contains the exact command, complete stdout/stderr and actual
exit code. The initially absent `_build` was populated by this one command:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 3000000; ulimit -s 65536; export PROOF_MEMORY_KB=3000000; dune build --cache=disabled -j1 --display short Examples/claude/arm8_ffsl_proof.vo'
```

Verbatim diagnostic (line numbers refer to the archived initial attempt):

```text
File "./Examples/claude/arm8_ffsl_proof.v", line 87, characters 22-32:
Error: Illegal application (Non-functional construction):
The expression "VarEqDec" of type "EqDec ARM8Arch.var"
cannot be applied to the term
 "v" : "?T"
```

The completed dependency targets include `Picinae_armv8.vo`,
`Examples/claude/arm8_common.vo`, `Examples/claude/ffsl_arm8.vo`, and
`Examples/claude/ffsll_arm8.vo`, plus the required core modules shown in the log.
There is **no successful complete unit-target build** and no unit proof `.vo`.
This was an elaboration failure, not evidence of memory-cap exhaustion.
Nothing was installed; the shared isolated environment was reused read-only.

## Preserved statements and attempt

`initial-attempt.v.txt` is the exact initial complete source submitted to Dune.
`Examples/claude/arm8_ffsl_proof.v` preserves every statement and definition.
Proofs from the first failing declaration onward are replaced by `Abort`, not
by assumptions. This is archival packaging, not a second proof attempt; this
packaged source was not compiled after the failure.

The build processed these five proofs before the failure:

- `ffsl_nwc`: state-independent code.
- `ffsl_welltyped`: typing of the unchanged generated IL.
- `ffsl_ffsll_program_identity`: exact equality of both generated programs.
- `ffsl_preserves_memory`: no change to modeled 64-bit memory.
- `ffsl_preserves_callee_saved`: X19–X30, SP, separate model R_LR and Z8–Z15.

These reached Qed during the failed compile; they have no independently
completed unit `.vo` or assumptions certificate, so they are not advertised as
a completed proof unit.

The aborted public targets are `ffsl_correct` and `ffsll_correct`. They state
partial correctness at both RET offsets (40 and 68), for every typed 64-bit
input: zero iff input zero, otherwise a result in 1..64 with exactly the
least significant set bit at result-1. SP and actual return register X30 are
included in the postcondition. Signed input is its two's-complement 64-bit
pattern, including LONG_MIN. No nonzero, sign, path, size, overlap, CPU-feature
or tunable restriction was introduced. The alias is one implementation.

Other aborted statements: `ffsl_entry_satisfiable`, `ffsl_lowest_set_bit`,
`ffsl_spec_satisfiable`, `rbit32_bound`, `rbit32_bits`, `ffsl_clz_rbit`,
`ffsl_asr_upper`, `ffsl_isolate`, and `ffsl_value_spec`.
All proofs after the entry witness are **unreached**, not known to work. The
fixer must validate the RBIT arithmetic, isolation/routing, modular width
normalization and actual symbolic execution, not merely fix the first error.

## Assumptions, provenance and scope limits

`tools/print-assumptions.sh` was **not run**: the target failed, and running it
would rebuild the failed target contrary to the one-shot handoff rule. There
is no raw Print Assumptions output for any new theorem and no claim that its
transitive assumptions are closed. `assumptions-request.txt` records the capped
command required after a future successful full build.

The reviewed e00 baseline documents inherited
`Stdlib.FunctionalExtensionality.functional_extensionality_dep` in existing
main theorems. That is baseline information, not a substitute for querying
these theorems. The source audit reports no new prohibited declarations; its
inherited totals are seven admissions, one tactic admission and 89 interface
parameters. No AMD64 theory or admitted example is directly imported by this
unit; transitive assumptions still require actual kernel queries.

`generated-lift-audit.log` records both unchanged lift hashes and an empty
diff against pinned origin. `provenance-read.log` records all 18 instruction
matches for each name from the external e02 evidence, read without importing
its branch. Target runtime hash is
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`,
ELF entry `0x94b10`, Ghidra entry `0x194b10`, 72-byte extent.
Instruction-text agreement does not establish lifter soundness. Neither the
intended `satisfies_all` theorem nor this partial handoff establishes
termination or full binary/hardware correctness.

`ancestry-before.log` was captured before implementation; its sole untracked
item is the notes directory being created by the recorder. The initial
inspection before that recorder showed a clean worktree. Post-implementation
audits are recorded alongside it. No remote writes, host installs, unrelated
branch edits, or changes to shared campaign status files were made.
`commit.log` and `ancestry-after.log` are local ignored evidence files so the
post-commit record can contain the actual final commit hash and clean status;
all build diagnostics, source audits and the initial attempt are committed.
