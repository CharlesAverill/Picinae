# r08-tick-count: DONE within sequential IL scope

Initial author and final proof model: **gpt-6-astra**, xhigh. One-shot initial
proof passed the full target on its first build; no Astra repair cycle.
Assigned service tier: default. No dependency installation or publication.

Branch: `llm-proofs/r08-tick-count`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-f5cd5d9c`.
Exact reviewed prerequisite: `5fec2fc24d0c739bafc08add426f02a3085e15cd`.
Pinned origin: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Meaning and limits

`Examples/FreeRTOS/armv6m_xTaskGetTickCount_proof.v` proves the accepted finite
`xTaskGetTickCount_armv6m_prog`, without modifying the generated lift or
assuming any callee/kernel contract. The source template is the accepted
r06 getter proof (Astra statements, Sol completion) in the assigned prerequisite;
that parent proof is not imported by the new proof module. No r00 kit is needed.

The exact path is entry `0x584` (immutable literal at `0x58c`), LDR `0x586`,
and the first BX LR cut `0x588`. The result is the four-byte little-endian
word in **original memory** at `0x2000002c`, `xTickCount` object offset zero.
The frame preserves every variable except R0/R3, including every memory byte,
permissions, flags, R4-R11, SP and LR. No stack allocation or writes occur.

- `tick_count_correct`: `satisfies_all` invariant theorem for any modeled entry
  store, over the actual finite program.
- `tick_count_post_at_bx`: executed, first-cut trace implies R0 equals the
  original tick word and the full frame.
- `tick_count_caller_result`: the same result/frame and the actual BX step,
  with odd original LR below `0xfffffff0`.
- `tick_count_return_step`: actual generated BX can step to `LR & 0xfffffffe`,
  preserving the complete store, under the same ordinary-return guards.
- `tick_count_preserves_callee_saved`: R4-R11, SP and LR at the first BX cut.
- `tick_count_preserves_original_bytes`: memory equality and byte equality at
  every address, relative to entry memory.
- `tick_count_preserves_memory`: generic memory frame over all endstates.
- `tick_count_nwc`, `tick_count_welltyped`: code independence and welltyping.
- `tick_count_zero_bound`, `tick_count_witness_models`,
  `tick_count_entry_satisfiable`: a typed/read-permitted witness for **every**
  bounded memory (`m < 2^(8*2^32)`), with that same memory and ordinary LR=1.

The invariant/functional facts require modeled input, entry trace identity,
and (for postconditions) an executed trace with no earlier exit cut. Read
permissions are supplied by actual execution; the independent witness shows
these premises are compatible with arbitrary modeled memory. There are no
additional count, size, overlap, feature, or tunable bounds. The only extra
return restrictions are odd LR and LR below `0xfffffff0`. The latter excludes
exception returns; the old ISA primitive itself does not implement them.

This is sequential IL partial correctness plus a concrete return step, **not**
termination, IRQ/hardware atomicity, exception behavior, scheduler cardinality,
whole-kernel correctness, or a proved binary/lifter refinement. The ELF/lifter
and immutable literal folding retain the accepted provenance trust boundary.

## Pinned evidence

`evidence.log` verifies source hashes against the committed manifest and records
source/config/layout/global-address evidence. The fixture is official FreeRTOS
V11.1.0 commit `dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`, ELF SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.

The pinned configuration selects 32-bit ticks, one core and trace disabled;
TickType_t and pointers are each four bytes. ARM_CM0's
`portTICK_TYPE_IS_ATOMIC=1` defines away tick critical-section macros in the
pinned source. This explains the call-free accepted body without requiring
an unconstrained oracle or a hardware atomicity claim. The lift manifest has
no blocked helpers, closure prerequisites or unsupported instructions.

The generated source SHA256 remains
`68aff25ab81b55dd8c885e4ac56056074634de87dfaf8d64edb9477e8d6c40e9`.
Only the new proof module and its exact alias were added to root Dune's
explicit list; all existing prerequisite files are unchanged.

## Successful validation

`initial-build.log` records the full command, compiler stdout/stderr, admission,
release and true exit **0**:

```sh
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r08-tick-count --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 1750000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_xTaskGetTickCount_proof.vo'
```

This was a fresh worktree build of full `.vo` dependencies and the target;
no `.vos`, skipped proof checking, copied objects or shared build cache.
`initial-attempt.v.txt` is byte-identical to the final proof source;
`initial-source-hashes.log` records the proof/lift/Dune hashes before build.

`assumptions.log` contains verbatim `Check` and `Print Assumptions` for all
12 exported facts, using `tools/print-assumptions.sh` inside the same admission
helper and cap, with `PROOF_MEMORY_KB=1750000`, `PROOF_STACK_KB=65536`. Exit **0**.
The helper's required Dune check was up-to-date and did not recompile the proof.
Admission initially waited for paging/RAM reserve, then succeeded unchanged.

`assumptions-review.log` checks all twelve raw outputs: six closed facts and
six facts with exactly the inherited baseline assumption below. There are
**no admitted transitive proof dependencies**. For `tick_count_correct`,
`tick_count_post_at_bx`, `tick_count_preserves_callee_saved`,
`tick_count_return_step`, `tick_count_caller_result`, and
`tick_count_preserves_original_bytes`, the verbatim assumption is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The other six outputs say `Closed under the global context`. Functional
extensionality is documented in e00's baseline and the accepted r06 template;
it is not hidden or described as a closed theorem.

`source-audit.log` runs `tools/audit-proof-source.py --base
49956416928e5b6bb3928b54ae33e3b81091f006` (exit **0**, `NEW totals: {}`).
It inventories unrelated inherited baseline admissions, which are not in the
new target's proof dependency assumptions. `unit-source-audit.log` is clean
with no suspicious tokens at all (exit **0**).

## Ancestry and operations

`r08-initial-ancestry.log` records the clean prepared e00 HEAD and its sole
pinned-origin parent. The prepared local branch was automatically named
`t3/prove-tick-count` by the time of the audited rename (initial inspection
had shown `t3/f5cd5d9c`). No unexpected commits were present.

`r08-fork-collision.log` records successful empty read-only `git ls-remote`.
Initial sandbox DNS/Git-metadata restrictions were overcome with approved
escalated read-only network/local Git operations; failed import/rename logs
are retained alongside the successful ones. The import was an exact
`git merge --ff-only 5fec2fc24d0c739bafc08add426f02a3085e15cd`; only the
prepared local branch was renamed. No other branch was changed.

`audit-ancestry.py` checks pinned merge-base, the exact prerequisite forest,
scoped linear unit commits, assigned branch, and unchanged generated hash.
The import/precommit/after-implementation logs retain full origin-to-HEAD
logs, diff stats, and status. Only the explicitly assigned prerequisite's
ancestry and this unit's commits are permitted. No fork history was used.
All work and commits are local. There are no remaining proof gaps within the
stated sequential IL scope.
