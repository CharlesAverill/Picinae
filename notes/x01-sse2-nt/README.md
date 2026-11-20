# x01-sse2-nt — PARTIAL handoff to Sol

Assigned branch: `llm-proofs/x01-sse2-nt`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-d1776e8c`.
Base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Sole prerequisite: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
No installation, shared environment modification, remote write, or subdelegation.
Every proof compilation/query uses `ulimit -v 8000000`, `ulimit -s 65536`,
Dune `--cache=disabled -j1`, and the existing read-only toolchain wrapper.

## Lift inspection (not a binary validation)

`02-nt-instructions.log` records the generated instruction comments and a clean
comparison of `memcpy_amd64.v` with e00. Provenance remains inherited: Ubuntu
amd64 glibc 2.35-0ubuntu3.12, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`.
No e01 binary evidence is imported or claimed.

Public entry `0x1c4870` skips the REP-dispatch entry at `0x1c4a10`.
For `n > 128`, nonoverlap refutes the backwards-overlap branch at `0x1c4a79`.
The comparison at `0x1c4a7f` selects NT iff `n > m[0x3215a8]`.
It jumps directly to `0x1c4bad`, so the AVX template's hypotheses on
`0x31a3f8` and `0x3215a0` must not be blindly copied to this entry.
The opposite-overlap test at `0x1c4bb3` must also be discharged from nonoverlap.

The head stores copy 64 bytes. With `a = 64 - d mod 64`, the aligned bulk
has `n-a` bytes. The four-page path is selected when the low 32-bit
complement of `s-d` has zero bits under mask `0xf80`, OR when
`(n-a) >> 4 >= current_memory[0x3215a8]`. That second threshold read occurs
AFTER the head stores. Using the initial threshold there needs an explicit
frame fact (e.g. the global's eight bytes are outside the destination),
or reasoning directly with the updated value. No such fact is assumed
silently in the suffix/helper proofs.

The two-page bulk uses `floor((n-a)/8192)` outer iterations, remainder
`(n-a) mod 8192`, and 64 inner iterations. Each inner iteration loads eight
16-byte vectors, then stores them to two pages. The four-page bulk uses
`floor((n-a)/16384)`, remainder `(n-a) mod 16384`, 64 inner iterations,
and sixteen 16-byte vectors across four pages. The counters are tested at
the bottom: the selected chunk count must be positive. A future full-entry
proof needs a justified lower-bound/tunable constraint or a precise selected
path condition, not an arbitrary size upper bound.

SFENCE and prefetches are modeled without memory-order/cache effects.
There is no assertion of CPU feature availability, fault freedom,
termination, concurrent-memory correctness, or lifter soundness.

## Validation result: PARTIAL, first failed attempt preserved

The full inherited dependency target passed (exit 0):

```bash
dune build --cache=disabled -j1 --display short Examples/claude/amd64_memcpy_loops_proof.vo
```

The first full new target failed (exit 1):

```bash
dune build --cache=disabled -j1 --display short Examples/claude/amd64_memcpy_nt_proof.vo
```

Both used the capped wrapper documented above. Exact shell commands and full
compiler stdout/stderr are in `01-dependencies.log` and
`07-initial-nt-build.log`. The error is at line 52 of the new file, in
`nt_row_advance`: `Tactic failure: Cannot find witness.` Peak RSS for the
failed Dune invocation was 424432 KiB; swaps were zero. This is a proof-tactic
failure, NOT evidence that the 8 GB cap is inadequate.

No repair or second build of the new target was attempted after this error.
`08-handoff-diagnostic.log` confirms that the source still has checkpoint
SHA256 `370d8cc31a381399cad0994852fa4bcc6083baa7c982b8521f6400e5179ddbb5`
and that no `amd64_memcpy_nt_proof.vo` exists. The `.v` file is the original
UNCHECKED proof attempt, preserved for the new Sol fixer under Charles's
updated policy. Its draft proof comments and `Qed` text do not certify any
new exported theorem. Later statements/proofs in the file were not reached
by the compiler. No full NT strategy, nor even the new tail theorem, is
claimed complete.

`04-source-audit.log` used the requested pinned base and exited 0, with
`NEW totals: {}`. There are no new admissions, axioms, or parameters.
Inherited admissions elsewhere remain outside this selected dependency
closure; the source audit alone is not a transitive proof certificate.

## Assumptions

`09-inherited-loop-assumptions.log` and `10-inherited-abi-assumptions.log`
record the unmodified `tools/print-assumptions.sh` queries on successfully
built dependencies. `pack16` and `cpy_store4` are closed under the global
context, as are `memcpy_nwc` and `memcpy_preserves_callee_saved`. Both
`memcpy_correct_loops` and `memcpy_welltyped` report exactly the inherited baseline:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

New main-theorem assumptions are UNAVAILABLE because the new module did not
compile. The failed module was not rebuilt just to repeat that failure in
the assumptions harness. No assumption inventory for any new theorem is
claimed. Dependency assumptions do not certify the unchecked new source.

## Ancestry and handoff

Only the reviewed e00 commit and this unit's local handoff commit may appear
above the pinned origin base. The initial history and remote collision
checks are in `x01-before.log` and `x01-collision.log`; the local rename is in
`branch-rename.log`. Final immutable commit/hash, diff-stat, and clean-status
evidence will be recorded in the permitted external unit directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x01-sse2-nt/postcommit.log`.
This avoids changing the commit in order to embed its own hash.

The coordinator should launch a NEW Sol (`gpt-6.1-sol`, xhigh/priority)
fixer from this handoff, preserving statements unless they are actually
wrong and explaining any necessary statement changes. This child did not
subdelegate and made no remote write.

## Charles's updated proof policy

The policy steering arrived while `01-dependencies.log` was still active.
No Rocq/Dune proof failure had occurred before the steering; the only earlier
command failures were sandbox DNS for the read-only branch collision query
(exit 128, preserved in `x01-before.log`) and the initial sandboxed local
branch rename (read-only git metadata). The required read-only query then
succeeded with no matching branch, and the authorized local rename succeeded
through sandbox escalation. No other branch was changed.

The active build must finish. After the first failed relevant proof build,
Astra must stop repairs and hand off this statement/attempt to a NEW
`gpt-6.1-sol`, xhigh/priority fixer delegate through the coordinator. This
child does not launch that delegate. The attempted statements must remain
unless the fixer identifies and explains an actual error.

## Draft theorem coverage (not a completion claim)

- `nt_row_advance`: four 16-byte stores, loads from the current memory, extend
  the copied-offset set by a 64-byte row under nonoverlap and exact bounds.
- `nt_done_chunk`, `nt_done_next_chunk`: 64 inner iterations cover all pages
  of a chunk; generic positive page count includes both 2 and 4.
- `nt_staged_advance`: advance one of the pages in a row, tracking original
  source bytes and the outside-written-set frame over abstract memory.
- `nt_tail_final`: the two final 64-byte copy blocks through their RET cuts.
- `nt_tail_loop`: the two actual lifted 64-byte tail-loop bodies.
- `memcpy_nt_tail_correct`: partial correctness from `0x1c4ccb` (two-page
  tail) or `0x1c4e73` (four-page tail), given an already copied prefix
  `[0,c)`, `c+64<n`, `n-c<2^32`, nonoverlap, `n<2^64`, `d+n<2^64`, modeled
  registers, `RDI=d+c`, `RSI=(s+c) mod 2^64`, `RDX=n-c`, `RAX=d`, and
  unchanged RSP. There is no arbitrary upper bound on total size beyond
  the AMD64 pointer/range conditions; the residual bound is required by EDX.
  No global/CPU threshold is read in this suffix. On either NT RET cut the
  postcondition is RAX=d, unchanged RSP, original-source `copied`, including
  the frame outside the destination. No termination conclusion is claimed.
- `memcpy_nt_tail_nonvacuous`: a concrete modeled state with empty copied
  prefix, distinct source/destination, and 128 uncopied bytes.
- `memcpy_nt_first_page_stores`: the first four actual MOVNTDQ instructions
  in either NT bulk body, from loaded low XMM lanes, extending `cpy` by a
  64-byte row. This local lemma does not assume the final copied predicate.

Still required for x01 completion: original-entry dispatch/head/alignment,
complete two/four-page load/store and counter obligations, post-bulk tail
entry, full-entry invariants/main theorem, nonvacuity evidence for new helper
contracts where needed, and all kernel and assumptions checks. The draft
uses the proved SSE2 modules only; it never imports the admitted AVX NT file.
