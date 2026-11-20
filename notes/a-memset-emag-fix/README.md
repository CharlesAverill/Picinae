# a-memset-emag-fix — BLOCKED, partial source attempt

Initial proof author: **gpt-6-astra**, xhigh/default as recorded in the
unaltered author evidence. Fixer: **gpt-6.1-sol**, xhigh/default requested.
Final checked proof producer: **unset**. No new declaration is certified.

Branch: `llm-proofs/a-memset-emag-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-2fcee8ec`.
Exact author checkpoint: `4b2f5bc78d3f544645dae5fb9f3714faf2db68dc`.
Pinned origin/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Actual blocker and exit status

The required gate printed **33** `ADMISSION WAIT a-memset-emag-fix available
RAM reserve` messages, without ever printing `ADMITTED`. After roughly eleven
minutes waiting, only this unit's waiting gate process was interrupted.
The recorder retained the real **exit 130**, traceback and all output in
`02-restored-build.log`. Dune and Rocq never started. This is scheduling
blockage, not a compiler error or evidence of exceeding the assigned cap.
No successful new `.vo` target command exists. No queued unit job remains.

`06-resource-snapshot.log` records the shared config and reservations read-only.
The snapshot had MemAvailable=39133268 KiB, active reservations totalling
16500000 KiB, the required new reservation=3000000 KiB, and the configured
available floor=20971520 KiB. Admission would leave 19633268 KiB, below that
floor. No cap, reserve, shared configuration or other process was changed.
The sole interrupted PID was identified by its exact resource-run command
and `--unit a-memset-emag-fix`; no other unit was signaled.

The exact attempted target command is in `build.sh` and the recorder log:

```bash
bash notes/a-memset-emag-fix/build.sh 02-restored-build
```

It invokes the mandatory shared resource gate at **3000000 KiB**, then the
read-only isolated environment, stack **65536**, and
`dune build --cache=disabled -j1 --display short Examples/claude/arm8_memset_emag_proof.vo`.
It neither requests `.vos` nor skips kernel checking. No new dependency was
installed. The gate itself never admitted a compiler during this attempt.

## Preserved source and proposed repairs

The complete original archive was restored into a working candidate before
attempting validation. `restored-repair-candidate.v.txt` preserves that
candidate plus these proposed script-only repairs, all **unvalidated**:

1. Replace unavailable `N.pow_pos_nonneg` in the inhabited-input witness with
   `N.neq_0_lt_0` and `N.pow_nonzero`, proving positivity without constructing
   the astronomical memory-width power.
2. Add the missing local pure `msub_add_l` helper, adapted from
   `amd64_common.v`, which the copied `msub_off` script references. No AMD64
   proof module or function contract is imported.
3. In `emag_finish`, defer the set-equivalence arithmetic goal until the
   store-chain goal instantiates the written-offset set. This corrects the
   tactic's dependency order; it does not change a proposition.

There are **no substantive definition, invariant, or statement changes**.
The 22 original statements compare verbatim with the archive, checked by
`check-source.py`. Original author evidence, branch, and exact 56-instruction
map are untouched. Lift SHA256 remains
`d88c12780e15542ee4a78674e9621deab12a58e415382ee50914b116b8cec8a8`;
author archive SHA256 remains
`48a043c9b21104979a4b40eae0b3450c0c47ed885f298477ce2484c0b3033bcf`.

Since no compiler was admitted, the compilable proof source retains the
checkpoint's first four Qed bodies and all subsequent Abort statements.
Only a status comment points to this handoff. The candidate's unverified
Qed commands are archived as text, not offered as completed proofs.
The root Dune list is unchanged from the author checkpoint; it already
selects the exact target and required lift dependencies explicitly.

## Theorem scope and remaining work

`memset_emag_correct : memset_emag_contract` remains **Abort**. The intended
contract covers all permitted d,n<2^64 with d+n<=2^64, all alignments, low8(X1)
filling, every outside byte, unchanged X0, and the saved-register list
X19..X29/SP/X30/full modeled Z8..Z15. Endpoint d+n=2^64 is permitted.
No small-size, overlap/separation, CPU, vector/ZVA, or tunable restriction
was added. Zero count/null input remains permitted by the statements.

The inhabited-input witness, all memory/range helpers, branch/loop/tail
preservation, and actual RET theorem still require kernel checking and
iterative repair. The full main theorem must exist and pass a real `.vo`
build; compiling a source whose main theorem is Abort would remain partial.
The proposed main tactic script should not be assumed complete: branch-bit
normalization, byte-replication automation, frame/store-chain obligations,
and aligned-cursor establishment/advance all remain unchecked.

`tools/print-assumptions.sh` was not run: the main theorem does not exist,
and even compilation could not be admitted. **No new raw main-theorem
assumptions output is available.** The original
`notes/a-memset-emag/inherited-lift-assumptions.txt` is preserved verbatim;
it records inherited `FunctionalExtensionality.functional_extensionality_dep`
for the lift typing theorem only, not a functional-correctness certificate.
No transitive-assumption completion claim is made.

The intended result is partial correctness of the inherited scalar IL before
RET, with a separate RET-step obligation. It is not termination, hardware
refinement, lifting validation, real-memory allocation/permissions/faults,
concurrency, or timing correctness.

## Audits and ancestry

`00-initial-ancestry.log` records the initial e00 HEAD, sole origin parent,
merge-base, log, diff stat, and prepared checkpoint ancestry. The initial
worktree was clean before creating these notes. T3 renamed its prepared
branch from `t3/2fcee8ec` to `t3/a-memset-emag-fix` before our branch rename.
The read-only `git ls-remote --heads fork
refs/heads/llm-proofs/a-memset-emag-fix` succeeded with empty output before
renaming only this prepared branch. The sandboxed DNS attempt exited 128;
the successful escalated read is recorded in `01-remote-check.log`.
The branch fast-forwarded from exact e00 to the exact author checkpoint.

Allowed pre-unit history is precisely origin..author-checkpoint, including
its reviewed e00/e02/e11/e08 commits. `ancestry-audit.sh` checks that exact
set and only scoped fixer commits after it. No fork base or unrelated
arm-validation/duneify/fix/ixb history was imported.

The final source/statement/ancestry logs accompany this handoff. The source
auditor uses the required pinned base. A lexical source pass cannot replace
missing kernel checks or transitive Print Assumptions.

All changes are local. No push, PR, comment, remote write, other-branch
change, shared plan/status update, environment installation or shared
toolchain modification occurred. No subagent/subdelegate was used.

`10-final-scope.log` has exit 1 solely because its naive substring count
included the traceback's Python source line as another wait message. The
correct line-prefix check in `11-blocker-verified.log` passes (exit 0),
confirming 33 actual messages, no admission, and recorder exit 130.

To resume proof work, first restore `restored-repair-candidate.v.txt` into
`Examples/claude/arm8_memset_emag_proof.v`, then repair and run the gated
build. The current tracked `.v` intentionally retains Abort statements;
a build of that sanitized source alone cannot certify the main theorem.
