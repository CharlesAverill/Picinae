# r13-reset-event author checkpoint

Initial author model: `gpt-6-astra`, requested xhigh/default.
State: **PARTIAL**, not done. Final proof model: none; the Astra attempt failed.
Branch: `llm-proofs/r13-reset-event`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-fe0e672b`.

## Scope and evidence

The initial statements are in `initial-attempt.v.txt`; its exact hash and the
unchanged generated lift hash are in `initial-source-sha256.log`.
`provenance.log` verifies the pinned tasks.c SHA256 and records its exact
function, configuration priority count, compiled object-layout fields,
immutable global-address literal and all ten instructions. This uses only
read-only local evidence from the accepted prerequisite and isolated e04
source tree. No dependency was installed and no generated lift was edited.

The proposed contract starts at 0x1524 and cuts before BX LR at 0x1536.
Initial memory supplies the current-TCB pointer at 0x20000108, event word at
TCB+24, and priority at TCB+44. R0 receives the original event word. The only
memory change is the four-byte little-endian store of `(5-priority) mod 2^32`
at TCB+24. It includes exact byte equations and the modular complement frame.
There are no alignment, non-overlap, priority-range, feature or tunable
preconditions. All addresses wrap at 32 bits; aliases are allowed and the
frame excludes the four written addresses. The separate normal-priority
corollary uses priority<5. Typed/permitted entry witnesses cover arbitrary
bounded memories and arbitrary odd LR below 0xfffffff0. The ordinary BX step
uses those LR guards and preserves the entire post-store state. R4-R11,
R12, SP, LR, permissions and temporary variables are framed.

This is sequential IL partial correctness, not hardware/IRQ, exception,
termination, whole-kernel, scheduler cardinality or validated binary/lifter
refinement. No unconstrained callee contract is used; the artifact is call-free.

## Ancestry and preparation

Prepared clean HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Pinned origin/base is `49956416928e5b6bb3928b54ae33e3b81091f006`.
The read-only remote-name check initially encountered sandbox DNS failure;
its network-enabled retry succeeded with no remote head (`r13-remote-check.log`).
Only the prepared local branch was renamed. A sandbox attempt to rename/merge
could not write Git metadata; its authorized elevated retry completed the rename
and exact fast-forward to `5fec2fc24d0c739bafc08add426f02a3085e15cd`.
`r13-before.log` records the initial clean status/base/log/stat.
`ancestry-prerequisite.log` records the imported base/log/stat and working edits.
`check-ancestry.py` verifies that all ten accepted prerequisite commits are
present and any subsequent commits change only this unit's proof/notes or dune.
This accepted history includes the r06 initial author checkpoint and Sol repair.
No unrelated history, original author branch changes or remote writes occurred.

## Validation policy

Only one initial full Dune build is permitted for this Astra author.
`initial-build.log` captures the admission helper, exact capped command, stdout,
stderr and true exit code. The gate sets memory=2000000 KiB and stack=65536 KiB;
the build also sets those limits, cache disabled, -j1, and the exact full .vo.
No other proof compiler runs within this unit. Admission waits are not failures.
`source-audit.log` is the whole-tree audit against the pinned origin (exit 0);
it inventories unrelated inherited admissions without asserting they are trusted.
`provenance.log` and `ancestry-check.log` also exited 0.

The inherited r06 assumptions certificate records
`FunctionalExtensionality.functional_extensionality_dep` for its main results.
That is context, not a substitute for this unit's own transitive assumptions.
Completion requires this unit's full target and verbatim Print Assumptions;
otherwise the result is PARTIAL and must go to a new Sol xhigh/default fixer.

## Final outcome and Sol handoff

The sole full build was admitted after resource waits and failed with exit 1:

```
rocq Examples/FreeRTOS/armv6m_uxTaskResetEventItemValue_proof.{glob,vo} (got signal ABRT)
Fatal error: out of memory
RELEASED r13-reset-event exit=1
EXIT_CODE=1
```

The compiler supplied no source location. The failed proof .glob and auxiliary
file were empty; no unit .vo was produced. There was no `_build/log` available
to copy; `initial-build.log` is the exact captured compiler stdout/stderr.
Core/model/generated-lift dependencies compiled successfully, but there is NO
successful proof target command and NO certified new theorem. No second build,
reduced-proof trial, raised cap, or other repair was attempted.

All 15 theorem/lemma statements are preserved verbatim in the live proof file
with `Abort.`; the entire initial proof text remains in `initial-attempt.v.txt`.
This is a sound WIP representation: no aborted statement becomes an assumption.
The definitions and explicit Dune module/alias remain for the fixer. The WIP
packaging was not recompiled, per the one-attempt handoff policy.
`statement-audit.log` verifies unchanged definitions/declarations/statements.
`final-source-audit.log` and `final-unit-source-audit.log` both exit 0: no new
admissions, axioms or parameters. These are lexical audits, not proof certificates.

Proposed main theorem names are `reset_event_correct`, `reset_event_post_at_bx`,
`reset_event_preserves_callee_saved`, `reset_event_original_memory_effects`,
`reset_event_return_step`, and `reset_event_caller_result`. Proposed auxiliary
facts cover welltyping/nwc, witness typing/satisfiability, stored word, written
bytes, memory frame and ordinary priority subtraction. NONE is claimed proved.

No `tools/print-assumptions.sh` run or raw unit Print Assumptions output exists:
the unit .vo is missing, and that helper would start a second Dune build.
Transitive assumptions therefore remain UNVERIFIED for all proposed results.
Inherited FE is documented above and must be reported if it appears in the
fixer's actual queries; inherited admitted dependencies would disqualify done.

Return to the coordinator for a NEW gpt-6.1-sol xhigh/default fixer. Keep the
statements unless genuinely wrong, explain any change, obey the same 2000000
KiB admission gate unless Charles/coordinator explicitly authorizes another cap,
and complete the full .vo plus every relevant assumptions query. No host install,
publication, remote write, or subdelegation occurred in this unit.

The postcommit audit will be saved outside the clean worktree at
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/r13-reset-event/after.log`.
