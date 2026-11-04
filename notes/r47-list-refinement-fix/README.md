# r47-list-refinement-fix

Status: **PARTIAL / WIP — stopped on Charles’s explicit wrap-up order**. This is a Sol repair of the exact
Astra checkpoint. No completed finite-ring memory-transition or composed
list-refinement theorem is claimed. See the recorded build and assumptions
logs for actual certificates; source `Qed` text alone is not a certificate.

- author_model: `gpt-6-astra`, xhigh/default.
- repair_model: `gpt-6.1-sol`, xhigh/default.
- final_proof_model: unset pending successful full-target checking.
- Assigned branch: `llm-proofs/r47-list-refinement-fix`.
- Worktree: `/home/charles/.t3/worktrees/Picinae/t3-2c979cb3`.
- Exact prerequisite: `0093bb733adbdee3d63e3b2b5673c8b57f919f66`.
- Origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Wrap-up status

Charles ordered immediate wrap-up: no further proving, compiler retries or
waiting. The pending own admission/build process was stopped; log 13 records
exit 143 while queued. No other unit process was signalled. All current proof
attempts are retained as WIP at his request. A `Qed` in this checkpoint is not
claimed checked unless the logs actually reached it.

There is **no successful full r47 `.vo` build and no fresh complete assumptions
certificate**. Last completed compiler run: `10-build.log`, exit 1 at the
redundant command in `ring_sentinel_object` (source line 265 at that run).
The subsequent local repair and later helper proofs remain unverified.
The four original main memory/refinement declarations remain `Abort`; no
admission, new axiom or parameter was introduced. The isolated 3M-cap OOM in
broad search was repaired past that point; do not describe this as a genuine
remaining cap-impossibility result. Long shared-admission waits are recorded
verbatim. `final_proof_model` remains unset for the unit.

Next step after explicit resumption: check the present target under the same
admission/cap rules, repair later helper obligations, complete both exact
memory transitions and both original composed IL theorems, then run all
transitive assumptions/audits. The branch remains local only.

## Preparation and source retention

The initial tool inspection found clean e00 HEAD
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole parent is the pinned
origin base. The sandboxed remote-name check failed DNS; an escalated read-only
retry succeeded with no result. `01-collision.log` repeats the successful empty
check immediately before renaming only the new prepared local branch and
fast-forwarding to the exact assigned prerequisite. No other branch or remote
was changed. `00-before.log` records the prepared branch's history and status
(the only untracked path was the newly created unit evidence directory).

The specific assignment authorizes all 22 prerequisite commits in
`git rev-list <base>..<checkpoint>`, including the accepted r00/r03/r04 forest,
its reviewed merge, and the Astra checkpoint. `audit-ancestry.py` checks exactly
that set plus single-parent commits scoped to this proof module and these notes.
No fork branch or unrelated validation/dune history was used as a base.

`check-retention.py` compares all 30 intended statements byte-for-byte to
`notes/r47-list-refinement/initial-statements.txt`. The sole elaboration change
is `forall a xs` -> `forall (a:N) (xs:list N)` in `ring_hd_member`. Its original
statement has no term fixing the implicit element type of `hd`/`In`/equality;
the annotation supplies the intended domain already used throughout this model.
No logical precondition or conclusion is altered. All original definitions,
generated lifts, prerequisite proofs, ISA files, and root Dune remain unchanged.
The root explicit module list already includes this module at the checkpoint.

## Intended and partial coverage

The model is finite byte memory for the 20-byte FreeRTOS List_t header, with
embedded sentinel L+8 and distinct aligned nonwrapping real 20-byte items.
It records count, cursor, maximum sentinel value, both sentinel links, every
item link/container, and original opaque value/owner maps. Fresh insertion
allocates a separate item. Permissions cover all bytes of the header/items
and the fresh item. The intended count bound for insertion is length+1<2^32.
No 64-bit pointer or ABI model is imported.

Repairs replace broad unbounded proof search with finite membership cases,
explicit chain suffix/boundary lemmas, and geometry facts that normalize
sentinel link slots to header offsets 12 and 16. They retain empty/singleton
neighbor aliases and arbitrary current-index insertion splits. New topology
helpers expose finite segments and prove predecessor cursor validity for both
remove-index branches. Concrete finite images and operation-entry witnesses
cover empty, singleton with both cursor cases, and two-node rings with every
allowed cursor position.

The proposed `ring_insert_local_contract` and `ring_remove_local_contract`
bridges derive actual r03/r04 preconditions from ring representation and
permissions, then apply their checked execution theorems. Their conclusions
are the original exact memory/register/byte-frame contracts at BX 0x70/0xbc.
These bridges do not establish that the final bytes represent the desired
finite sequence. The original `ring_insert_memory`, `ring_remove_memory`,
`ring_insert_refines`, and `ring_remove_refines` statements remain present as
`Abort` while those obligations remain open; they export no assumptions.

Execution scope is sequential AAPCS32 IL, with insertion R0=L/R1=P and
removal R0=P, and traces actually reaching the stated BX cut without an earlier
exit. Insertion requires the inherited ordinary LR condition; the removal
contract stops before BX and imposes no extra LR hypothesis. No call/kernel,
scheduler, termination, trace-existence, concurrency, IRQ, hardware or lifter
soundness theorem is assumed. Exact upstream commit/ELF hashes and inherited
trusted-lift provenance remain in the proof header.

## Resource and validation evidence

Every compiler job enters the shared `resource-run.py` helper with
`--memory-kib 3000000`; stack 65536, cache disabled, Dune -j1. No concurrent
proof compilers are started in this unit. Builds use the read-only shared
`picinae-env` wrapper. No installation or shared environment mutation occurs.
All local build state is in this isolated worktree's `_build` directory.

- `02-build.log`: dependency closure rebuilt; first subsequent source error.
  Elapsed 2:26.01, peak RSS 929292 KiB, exit 1.
- `04-build.log`: broad `firstorder` search in fresh geometry hit the cap,
  `Fatal error: out of memory`, peak RSS 2701736 KiB, no swap, exit 1.
- `05-build.log`: after replacing that search with explicit finite cases,
  fresh geometry passes; later arithmetic normalization fails. Peak RSS
  459448 KiB, exit 1. This resolves that specific cap failure; it is not
  evidence that the intended full memory-refinement proof cannot fit.
- Subsequent numbered build logs preserve true exits/stdout/stderr and all
  admission waits. Waiting on the shared gate is not a compiler failure.

`build.sh N` records the exact gated full `.vo` target command as
`N-build.log`. `print-checked-assumptions.sh` queries every actually exported
lemma/theorem plus the imported r03/r04 typing, no-write-code, execution and
memory/frame contracts, under PROOF_MEMORY_KB=3000000. It deliberately does not
query aborted declarations. A successful helper-only module would remain
PARTIAL because the four original main obligations above are still absent.

The source audit versus pinned base reports no admissions, axioms or
parameters in this unit. Whole-repository inherited interface parameters and
unrelated baseline admissions are not evidence of transitive dependence.
The accepted baseline FE axiom must be reported honestly if it appears in
fresh transitive assumption output:

```
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Remaining work: complete and check both pure-memory ring transformations and
both original composed IL-refinement theorems, then query those main theorems.
Do not infer done, full binary correctness, or termination from partial helpers.
No push, PR, comments, remote write, host install, or shared campaign-file edit.
