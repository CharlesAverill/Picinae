# r09-tick-count-isr — DONE

Initial author and final proof model: **gpt-6-astra**, xhigh.
Requested service tier: default. One initial full build passed; no repair cycle.
All twelve statements and initial proofs are byte-for-byte unchanged from
`initial-attempt.v.txt`; `audit-validation.py` verifies this and the raw
assumptions reports. The accepted r06 source was used as a template, with
its Astra/Sol attribution disclosed in the proof header; no r06 theorem is
imported. Generated IL and ISA files are unchanged.

Branch: `llm-proofs/r09-tick-count-isr`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-584f983b`.
Exact prerequisite: `5fec2fc24d0c739bafc08add426f02a3085e15cd`.
Pinned origin/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
The final commit SHA and postcommit clean status are recorded in the unit's
external evidence directory and returned to the coordinator.

## Proven scope

`Examples/FreeRTOS/armv6m_xTaskGetTickCountFromISR_proof.v` proves the actual
finite generated `xTaskGetTickCountFromISR_armv6m_prog`. Entry is 0x590;
the immutable literal at 0x598 places 0x2000002c in R3. The 0x592 load reads
four little-endian bytes from xTickCount, object offset zero. At the first
BX LR cut 0x594, R0 equals this word from **initial** memory, with every
variable other than R0/R3 preserved. This includes every memory byte, read
and write permissions, flags, temporaries, R4-R11, SP and LR. There are no
calls, stack accesses or assumed callee/kernel contracts.

All names below have prefix `tick_count_isr_`:

| Theorem/helper | Coverage | Transitive assumptions |
|---|---|---|
| `nwc` | Program independent of store | closed |
| `welltyped` | Actual generated program typing | closed |
| `preserves_memory` | All modeled program endstates preserve memory | closed |
| `zero_bound` | Positive power-of-two bound at any width | closed |
| `witness_models` | Typed entry for every bounded architectural memory | closed |
| `entry_satisfiable` | Same arbitrary memory, permissions for all four read bytes, LR=1 satisfying return guards | closed |
| `correct` | `satisfies_all` partial correctness from entry to first designated exit | inherited FE only |
| `post_at_bx` | Original-memory result and frame at actual first BX cut | inherited FE only |
| `preserves_callee_saved` | R4-R11, SP and LR frame | inherited FE only |
| `original_bytes` | Original word returned; all original bytes unchanged | inherited FE only |
| `return_step` | Actual generated BX step with unchanged store | inherited FE only |
| `caller_result` | Functional result/frame plus actual guarded BX step | inherited FE only |

The functional theorem assumes a modeled 32-bit ARMv6-M store and the exact
entry. Exit corollaries also require an actual `exec_prog` trace and
`unterminated` for the preceding trace, so the cut is the first designated
exit. Actual load execution supplies permissions; the separate witness
shows they are satisfiable for every memory `m < 2^(8*2^32)` (zero is one
inhabitant by `zero_bound`). There are no register arguments or bounds on
the tick value, no size/overlap/path-length/CPU-feature/tunable hypotheses.

The return results additionally require `N.odd (s R_LR) = true` and
`s R_LR < 0xfffffff0`. They exhibit `can_step` at 0x594 to
`LR & (N.ones 32 - 1)` with the same store. The upper bound deliberately
excludes EXC_RETURN; the inherited IL itself checks only the Thumb low bit
and does not implement hardware exception-return semantics. No further
caller execution or return-target accessibility is claimed.

This is sequential IL partial correctness, not asynchronous ISR atomicity,
CPU IRQ/hardware correctness, whole-kernel invariants/cardinality,
termination, or a binary/lifter-refinement theorem. No such stronger result
is claimed completed. Broader e05 call closures are not used.

## Pinned provenance

Official FreeRTOS V11.1.0 commit
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`;
ELF SHA256 `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
`audit-provenance.py` reads the existing isolated e04 source/ELF without
modifying it, verifies hashes of ELF/tasks.c/portmacro.h/FreeRTOS.h/config,
layout and generated lift, and checks the empty call/unsupported lists.
`provenance.log` records exit 0 and the source body and compiled macros.
The exact source/config establish 32-bit TickType_t, single-core fixture,
and compiled mask/priority-check macros with no operations in this getter.
This explains the accepted call-free body; the source macro named
`portTICK_TYPE_IS_ATOMIC` is not evidence of a proved asynchronous property.
The proof retains inherited immutable-literal and unvalidated lifting trust.

## Full kernel build and source/assumptions audits

The first full build completed with exit 0 (`initial-build.log`), following
three admission waits for paging activity. All heavy runs passed through:

```sh
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r09-tick-count-isr --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 1750000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_xTaskGetTickCountFromISR_proof.vo'
```

Dune built the full dependency closure from this worktree's fresh build
directory using `mode vo`, with no `.vos`, no shared cache and one compiler.
Root Dune adds only the new proof module (its generated dependency was
already selected) and exact alias `@r09-tick-count-isr`.
No installation, shared environment edit, host dependency change or other
process intervention occurred.

`assumptions.log` contains the exact gated command and verbatim `Check` and
`Print Assumptions` output for all twelve names, using
`tools/print-assumptions.sh` with PROOF_MEMORY_KB=1750000 and
PROOF_STACK_KB=65536. Exit 0. Versions recorded there are Rocq 9.1.1,
OCaml 4.14.2 and Dune 3.22.2. Six facts are `Closed under the global context`;
the remaining six report exactly:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib axiom documented in e00's
`notes/e00-build/logs/15-extensionality-provenance.log`. No imported admitted
proof or other transitive assumption appears. `validation-audit.log`
checks every report individually and confirms exact initial proof retention.

`source-audit.log` records the required whole-tree
`python3 tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006`,
exit 0, NEW totals `{}`. Baseline unrelated admissions and module-interface
parameters remain inventoried (7 Admitted, 1 admit, 89 Parameter), unchanged.
`initial-source-audit.log` scopes the new proof and reports all totals empty.
There is no new admission, axiom or parameter in this unit. These lexical
checks supplement, rather than replace, the transitive assumptions audit.

## Preparation, ancestry and local-only handoff

Initial `git status --short` was empty on `t3/tick-count-isr-proof`, HEAD
71470bffba65392adf1873a3df9f0cf0ca4f1ac9, whose sole parent was pinned origin.
Initial merge-base was pinned origin. The first sandboxed read-only remote
check failed DNS resolution. The successful escalated check in
`remote-name-check.log` exited 0 with no result before branch rename.
Initial sandboxed merge/rename attempts could not write Git metadata and
made no history/branch changes. Approved retries fast-forwarded ONLY to
the exact assigned prerequisite and renamed ONLY the prepared local branch;
`import-prerequisite.log` and `rename-branch.log` record exit 0.
`ancestry-before.log` records the e00-only history/diff; its status includes
only this unit's newly created logging directory, after the initially clean
observation. No fork branch was used as a base.

`audit-ancestry.py` verifies the pinned origin/merge-base, the exact union of
prerequisite commits, unchanged generated lift, assigned branch and scoped
linear unit commits. It prints the full required log, diff stat and status.
`ancestry-imported.log` and `ancestry-precommit.log` preserve those records.
The accepted r06 parent proof and its original partial checkpoint are present
in the explicitly allowed prerequisite closure; no unrelated history was
imported. Final external evidence is restricted to
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/r09-tick-count-isr/`.
No other branch was changed, and no push, PR or remote write was performed.
