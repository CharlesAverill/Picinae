# r47-list-refinement — PARTIAL Astra handoff

State: **PARTIAL**, not done. Initial author model: `gpt-6-astra`;
assigned reasoning/service tier: `xhigh/default`. Final proof model: **unset**.
No fixer was delegated. Coordinator must launch a NEW `gpt-6.1-sol`
`xhigh/default` fixer. There was exactly one full target build and no repair
cycle or second compiler invocation after failure.

Branch: `llm-proofs/r47-list-refinement`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ae1d8d8a`.
The prepared branch was `t3/r47-list-refinement`, clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`; its sole parent and merge base are
`49956416928e5b6bb3928b54ae33e3b81091f006`.
A successful empty read-only fork-name check preceded the local rename.
One sandboxed retry of the remote check failed DNS (recorded, exit 128),
and an initial sandboxed rename was denied by the read-only Git metadata;
the authorized escalated check/rename/import then succeeded. No remote write,
publication, other branch change, host installation, or shared toolchain
modification occurred.

## Exact authorized integration

Before integration, `r47-prerequisite-union.log` recorded the exact 19-commit
union of origin-base..r03 and origin-base..r04, also saved in
`allowed-prerequisites.txt`. Fast-forward to exactly
`7e49f57f76af3afaedf1c2b7bd5cf810cf4efef2`, then merge exactly
`18dcb8cb928ba1e712aaa9aa8bb8f43aef51910f`.
The only conflict was the explicit root Dune module list; retain both entries.
Import merge: `4c17e59602851b3156a0c2e45aa63add7fb0b142`.
The ancestry auditor permits that union, this exact two-parent merge, and
single-parent unit commits touching only the new module, root dune, and these
notes. No r01/r02/r05 or unrelated proof branch was imported.

## One-shot result and exact failure

Recorded command (`dune-initial.log`, **exit 1**):

```bash
bash --noprofile --norc -e -c 'ulimit -v 4000000; ulimit -s 65536; export XDG_CACHE_HOME=/home/charles/code/friends/.toolchains/r47-list-refinement/cache; export TMPDIR=/home/charles/code/friends/.toolchains/r47-list-refinement/tmp; /home/charles/code/friends/.toolchains/arm-validation/picinae-env dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_list_refinement.vo'
```

Full core, r00, both generated maps, and both accepted r03/r04 proof `.vo`
dependencies rebuilt before the new module failed. **No successful r47 target
command exists.** No `.vos`, cache reuse, or skipped proof checking was used.
All build/cache/temp state was isolated under
`/home/charles/code/friends/.toolchains/r47-list-refinement/`; `_build` is a
symlink there. The recorded live compiler resource check showed one insertion
compiler with `Max address space 4096000000` bytes and `Max stack size
67108864` bytes (the assigned 4,000,000/65,536 KiB caps), RSS 917008 KiB.

Exact diagnostic from initial source line 97:

```text
File "./Examples/FreeRTOS/armv6m_list_refinement.v", line 97, characters 36-45:
Error: Cannot infer the implicit parameter A of eq whose type is "Type".
```

This is in the statement of `ring_hd_member`, whose binders `a` and `xs`
lack an element-type annotation. Intended domain is `N` / `list N`, consistent
with every other ring definition. No binder or statement was changed by
Astra. The new Sol fixer should explain the necessary annotation explicitly;
it is not permission to weaken other statements. All later proof attempts
are untested, not near-complete merely because this first error is small.

`initial-attempt.v.txt` preserves the entire initial source verbatim, including
all proof attempts and inline assumptions queries. `initial-statements.txt`
preserves all 30 exact theorem/lemma statements. Mechanical handoff conversion
retains the two checked prefix proofs and replaces the failed and all later
proofs with `Abort`; no admission is introduced. `handoff-retention.log`
checks byte-for-byte statement retention. The archived active module has NOT
been rebuilt, and the unannotated failed statement remains for the fixer;
no claim is made that this partial source elaborates as a full file.

## Intended specification and outstanding proof obligations

`ring_rep` explicitly records original-memory 20-byte header layout, maximum
sentinel value at L+8, sentinel first/last links, finite distinct real-node
sequence, all node next/previous/container/value/owner fields, exact natural
length as the header count, and cursor sentinel/member membership.
`ring_geometry` supplies nonnull aligned nonwrapping objects and numeric
20-byte separation among header/real objects, allowing embedded sentinel
aliasing and empty/singleton equal-neighbor cases. `ring_permissions` gives
all-byte read/write permissions of the stated regions. Fresh insertion uses
a separate real item and original opaque fields, never an assumed output.

Unproved main statements:

- `ring_insert_memory` / `ring_insert_refines`: insert before current index,
  across every split/cursor; new sequence membership and count +1, unchanged
  cursor and opaque maps, exact r03 byte/register frame in `insert_end_post`.
  Explicit bound `N.of_nat(length xs)+1 < 2^32` connects modular increment to
  mathematical cardinality; no wraparound claim is silently added.
- `ring_remove_memory` / `ring_remove_refines`: remove exactly the selected
  member, count -1, repair current cursor to predecessor in the equal branch,
  and use r04 effects for cleared container, unchanged removed links/value/
  owner, original-byte and register frames. Empty result and both index cases
  are in the intended statement domain.
- `ring_insert_layout`, `ring_remove_layout`, `ring_insert_pre`,
  `ring_remove_pre`: derive actual local layout, word separation and permissions
  from representation, not assumed global/callee correctness.
- `ring_empty_witness`, `ring_singleton_witness`, `ring_multi_witness`,
  `ring_empty_insert_witness`, `ring_singleton_remove_witness`,
  `ring_multi_remove_witness`: concrete finite byte images and operation entry
  satisfiability. All are unverified and need real proof completion.

The IL corollaries refer to the unchanged generated maps and checked r03/r04
contracts. They condition on actual execution reaching BX at 0x70 / 0xbc and
exclude an earlier cut exit. They do not establish existence of a trace,
termination, IRQ/concurrency/scheduler behavior, hardware or binary soundness.
AAPCS32 widths and inherited lift provenance are explicit in the source.
The new module imports r03/r04 typing, no-write-code, invariant, exit and frame
facts; it does not edit or replace those function proofs or the ISA.

## Assumptions and audits

Only `ring_last_app` and `ring_last_member` reached Qed/Print Assumptions in
the failed compiler invocation. Both printed verbatim:

```text
Closed under the global context
```

The raw named output is in `dune-initial.log`. These prefix checks do NOT
constitute a successful full module target or any list-refinement proof.
`tools/print-assumptions.sh` was not invoked after failure because it rebuilds
the target, contrary to the required immediate Astra handoff. The capped
`print-all-assumptions.sh` is prepared for the new fixer to run only AFTER a
successful full build; it lists every one of the 30 intended results.

Read inherited raw certificates:
`notes/r03-list-insert-end-fix/24-final-all-assumptions.log` and
`notes/r04-list-remove-fix/21-assumptions.log`. They disclose inherited
`FunctionalExtensionality.functional_extensionality_dep` for the main IL
contracts. Their memory/fixture facts are closed where recorded. These are
accepted prerequisite certificates, not fresh r47 transitive checks. No
r47 main theorem is certified and no assumption status is claimed for it.

Audits with true exit 0:

- `source-audit-initial.log`: whole repository versus pinned origin base;
  baseline totals unchanged (7 admitted, 1 admit, 89 interface parameters),
  NEW totals empty. Baseline unrelated admitted files are outside this target.
- `source-audit-final.log`: new module has zero admissions/new axioms/parameters.
- `retention-final.log`: all 729 inherited files byte-identical; Dune adds
  exactly `Examples.FreeRTOS.armv6m_list_refinement`.
- `handoff-retention.log`: all 30 original statements unchanged.
- `ancestry-precommit.log`: exact prerequisite union and scoped import merge.

No post-failure proof repairs or compiler processes were started. Remaining
work is substantial: complete the layout/memory/refinement/witness proofs,
check full .vo, run all transitive assumption queries, repeat source/retention/
ancestry audits, and record the actual final proof producer.
