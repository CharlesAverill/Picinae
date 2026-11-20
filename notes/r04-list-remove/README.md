# r04-list-remove — PARTIAL Astra author handoff

Initial author: **gpt-6-astra, xhigh/priority**. Final proof producer: **none**.
Branch: `llm-proofs/r04-list-remove`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ab3d95c2`.

The one full Dune attempt exited **1**, at initial source line 229:

```
Goal at < 160 >
Goal at < 178 >
Goal at < 178 >
File "./Examples/FreeRTOS/armv6m_uxListRemove_proof.v", line 229, characters 4-5:
Error: [Focus] Wrong bullet +: Current bullet + is not finished.
```

The first entry-to-0xb2 branch of `list_remove_correct` leaves obligations
open before the next invariant case. This is not a memory-cap failure.
No second proof compiler run, repair cycle, dependency installation,
subdelegation, remote write, push, PR, or publication occurred. The coordinator
must use a **new gpt-6.1-sol xhigh/priority fixer** to continue; preserve all
statements unless genuinely wrong, explaining each statement change.

## Exact initial attempt and scope

`initial-attempt.v.txt` is the full original 446-line initial author attempt,
SHA256 `9c3ab7428dc523d7df0de3df5f962f8c40d2017f1700ee09aad1235ee79c7833`.
`build-initial.log` contains exact command, compiler stdout/stderr and exit.
The build used the read-only shared environment, `ulimit -v 2000000`,
`ulimit -s 65536`, `--cache=disabled -j1`, and full `.vo` mode:

```
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_uxListRemove_proof.vo'
```

**There is no successful complete unit-target command and no unit .vo.**
Prerequisite core/ISA/r00/generated target .vo files did build successfully
inside this single invocation; that is not unit completion.

The seven completed proof bodies reached Qed before the failing theorem:
`list_remove_nwc`, `list_remove_welltyped`, `list_remove_register_frame`,
`rm_read_write`, `rm_read_frame`, `list_remove_mem_frame`,
`list_remove_mem_effects`. They are preserved verbatim. No standalone full
module or transitive-assumption certificate is claimed for these helpers.

The nine remaining statements are preserved as `Abort`:
`list_remove_correct`, `list_remove_at_bx`, `list_remove_return_step`,
`list_remove_entry_witness`, `list_remove_singleton_layout`,
`list_remove_singleton_witness`, `list_remove_multi_layout`,
`list_remove_multi_witness`, `list_remove_returns`.
Their initial proof scripts remain in the archive. No admitted proof or new
axiom/parameter was introduced. `declaration-audit.log` checks exact statement,
definition and completed-body preservation. Aborted source was not recompiled.

The intended contract uses original memory, actual program addresses and
AAPCS32; count has no upper bound below the full 32-bit field range. It
expresses both index branches, N.prev=B, B.next=N, index repair, container
clear, count/return decrement, opaque value/owner preservation, unchanged
removed-item links, exact conditional word footprint, byte/word frames and
callee/SP/LR frame. Permission/typing witness statements include singleton
B=N=L+8 and distinct neighbors for either index branch. The field separation
matrix does not require all objects pairwise disjoint. The ordinary BX
statement uses odd LR below 0xfffffff0. NZCV are correctly excluded from the
preserved-register predicate. No proof of termination, finite-list cardinality,
hardware exceptions, scheduler, IRQ, TCB or lifter refinement is claimed.

**Remaining gaps:** actual satisfies_all execution, trace-to-BX extraction,
ordinary return integration, typed/readable/writable witness proofs, full .vo,
and every transitive Print Assumptions query. See `assumptions-status.txt` for
why the helper was not run after failure and for the exact future query list.
Inherited baseline functional extensionality is disclosed there, not assumed
away or falsely reported closed.

## Ancestry and hygiene

Initial prepared branch was `t3/list-remove-contract`, clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose parent is pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006`.
The first sandboxed network check failed DNS. The escalated read-only check
succeeded with empty output, then was repeated through the recorder in
`fork-collision.log` (exit 0, no matching fork head). The first branch rename
failed because shared Git metadata was read-only. Automatic review then
rejected an escalated rename/import after mistakenly treating the first
failed network check as final. Persisted successful collision evidence was
provided and the same bounded operation succeeded. No restriction was bypassed.
Only the prepared local branch was renamed. The explicitly accepted r00
`4ff26413448da4d8f064b0273ac5472cc9de7e5a` was imported by `--ff-only`.

`allowed-prerequisites.txt` pins exactly the reviewed e00/e03/e04/e05/r00
ancestry authorized by the assignment. `audit-ancestry.sh` verifies pinned
origin/merge-base, prerequisite ancestry, and only unit-owned paths in later
single-parent commits. No r01/r02/r03/r04/e19/fork history was imported.
The completed r02 initializer source was read via `git show` as a template;
it is neither imported nor a logical prerequisite. Generated map, ISA,
frontend and accepted r00 source remain unchanged. Root Dune adds only this
unit module; all other listed modules are inherited from accepted ancestry.

`source-audit.log` reports no new suspicious tokens relative to pinned origin.
Baseline unrelated admissions/signature parameters remain inventoried; lexical
success alone is not a transitive-assumption audit. `partial-unit-audit.log`
and `declaration-audit.log` cover the final partial source.
