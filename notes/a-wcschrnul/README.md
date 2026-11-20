# a-wcschrnul author handoff

Initial author model: `gpt-6-astra`, reasoning effort `xhigh`; assigned service
 tier `default` (runtime tier is not independently inspectable here).
Status: **PARTIAL**, mandatory handoff to a NEW `gpt-6.1-sol` fixer with
`xhigh` / `default`; no further Astra proof repair or compiler run occurred.
Final proof model: none; Astra did not complete this proof.

The sole full build exited **1** at initial source line 151, characters 31-33:

```text
Error: Syntax error: '|' or ']' expected (in [or_and_intropattern]).
```

The failed line is `destruct H as [->|[->|[->|->]]]; reflexivity.` inside
`wcschrnul_input_satisfiable`. Eight earlier Qeds were processed in that
failed compiler invocation (map/frame facts and the four pure helpers),
but **no full new proof .vo exists** and none is claimed certified as a
completed module. The satisfiability, main correctness and return proofs
were not completed; their statements remain verbatim with `Abort` in the
active source. Untested branch tactics and all initial proof bodies remain
verbatim in the archived initial attempt. This is packaging a failed attempt,
not a second proof repair cycle. No compiler was run after this packaging.

Successful requested full-target commands: **none**. Core dependencies and
the unchanged e30 lift compiled successfully during the failed target build.
The failure was syntactic, not a memory-cap failure. No cap increase is needed
or authorized by this evidence.

Branch: `llm-proofs/a-wcschrnul`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-62dac67c`.
Assigned prerequisite: `bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9`.
Pinned base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
The prepared branch started clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole parent is the base.
The initial shell inspection recorded empty `git status --short`; the
subsequent recorded pre-import audit sees only this unit's newly created notes.
The remote branch collision check succeeded with empty output before the
prepared branch was renamed. The only import was an exact fast-forward to
the assigned e30 head. No other branch was changed and nothing was published.

## Contract and proposed results

`wcschrnul_correct` is a `satisfies_all` partial-correctness statement over
the complete, unchanged nine-instruction `e30_wcschrnul_arm8` map. Entry is
`0x19e4c0`, the preincrement load loop is `0x19e4d0`, and RET is `0x19e4e0`.
Input X0 is a 64-bit pointer p, X1 contributes only its low 32 bits c,
SP is sp and X30 is lr. `wcschrnul_stop` specifies the least K with
`getmem 64 LittleE 4 m (p+4*K) = c` or zero; all earlier words differ
from both. `wcschrnul_input` requires actual A_READ bits for every byte
through that stop word and `p+4*(K+1) <= 2^64`. No signed-wchar restriction,
alignment, CPU/tunable switch, overlap restriction, or callee oracle occurs.
At the unique RET, the postcondition preserves memory, X1 low32, SP and X30
and sets X0 to `p+4*K`.

`wcschrnul_return` separately describes execution of that exact RET into
`Addr lr` while retaining the result and frame. This does not prove that a
finite execution reaches RET. `wcschrnul_preserves_memory` and
`wcschrnul_preserves_callee_saved` cover every endpoint and include X19-X30,
SP, the entire modeled Z8-Z15 cells, A_READ/A_WRITE and X1.
`wcschrnul_input_satisfiable` proposes a typed, readable empty wide string
at unaligned pointer 1 for every 32-bit character pattern. The four pure
helpers classify hit/miss indices, bound addresses and justify full-word
equality via 32-bit modular subtraction. `wcschrnul_nwc` and
`wcschrnul_welltyped` provide the usual map facts.

These are intended IL results only: no lifter refinement, hardware fault
freedom, concurrency guarantee, or termination claim. Real-machine use of
unaligned loads also depends on memory type/alignment configuration, absent
from this IL. Binary/package provenance is inherited from accepted e30.
The exact generated lift hash is
`ab43b39ccf445c4cb9889ae1e2df855f35c9daf85d53056c1f7d2c4127bd3d20`.

## Evidence

- `initial-attempt.v.txt`: exact one-shot source, SHA256
  `4d3988242e3c104d76273dea3e3ea98238ee911a429a037552de4c7e7585ba29`.
- `initial-statements.txt`: verbatim initial theorem/lemma declarations.
- `04-initial-build.log`: exact resource-gated full `.vo` command, all
  compiler output and its true exit code on completion. Cap 1750000 KiB,
  stack 65536 KiB, one compiler, `--cache=disabled -j1`; no dependency installs.
- `02-initial-source-audit.log` and `06-full-source-audit.log`: exit 0;
  zero new lexical admissions or axioms/parameters. Inherited unrelated
  admissions remain outside this target's import closure.
- `00-before.log`, `01-branch-check.log`, `05-prerequisite-audit.log`:
  prepared branch, remote collision, exact allowed history and protected lift.
- `run-assumptions.sh`: reproducible gated use of `tools/print-assumptions.sh`
  for all eleven proposed results, to run only after full target success.

The baseline core uses `FunctionalExtensionality.functional_extensionality_dep`
(see inherited `notes/e00-build/logs/13-arm8-assumptions.log`). This is not
an assumptions certificate for the new module. Until successful compilation
and raw queries exist, transitive assumptions for the new results are unverified.

## Remaining work for the new Sol fixer

Restore and repair the archived witness and proof attempts, retaining every
statement unless it is genuinely wrong and documenting every statement
change. The first failure precedes both branch tactics and the main proof;
those later portions are untested, and this handoff does not predict their
success. Complete the nonvacuity witness, both CCMP variants, preincrement
loop invariant and ordinary RET lemma, then build the full `.vo` and run
`run-assumptions.sh` through the same admission gate. Review all transitive
assumptions. No new helper contract or admitted callee is present.

`assumptions-status.txt` records why no new-module Print Assumptions output
exists. The only fresh assumptions output in this build is the unchanged
lift's own typing query, reproduced verbatim in `lift-assumptions.txt`.
It lists only the inherited functional extensionality axiom. It must not be
presented as certification of the aborted main results.
