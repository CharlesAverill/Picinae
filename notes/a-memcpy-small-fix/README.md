# a-memcpy-small-fix

Proof repair by OpenAI gpt-6.1-sol, xhigh/priority, following the archived
OpenAI gpt-6-astra initial statements and scripts. Local branch:
`llm-proofs/a-memcpy-small-fix`. Worktree:
`/home/charles/.t3/worktrees/Picinae/t3-d5c9940f`.

**Status: DONE for the assigned small-path IL partial-correctness scope.**
The full `.vo` build succeeded (27-build.log, exit 0), all 50 facts received
raw transitive Print Assumptions queries (34-assumptions.log, exit 0), and
37-assumptions-audit.log verifies 14 closed facts and 36 inherited-FE-only facts.
All 16 original statements, all original definitions, and both initial archives
are preserved. No admissions, Abort declarations, new Axiom/Parameter, or
imported admitted proof occurs in the unit's certified dependency closure.
No within-unit proof gap remains. The original author evidence under
`notes/a-memcpy-small/` is unchanged.

## Specification and boundary

The unchanged e08 generated union map has 99 generic instructions and nine
mempcpy-wrapper instructions. The theorem starts at actual generic model entry
`0x19ab40` (ELF `0x9ab40`) and stops at the four small RET cuts `0x19ab74`,
`0x19ab8c`, `0x19aba4`, `0x19abc8`. It concerns the inherited explicit scalar
lift of Ubuntu ARM64 glibc 2.35-0ubuntu3.15, libc SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
The generated union, manifests, pcode and all inherited evidence remain unchanged.
This is partial correctness of that IL, not validation of binary-to-IL soundness.

`memcpy_small_correct` retains every original premise: the typed initial ARM8
store, X0=d/X1=s/X2=n, initial memory m, 0<=n<=32, d+n<=2^64, s+n<=2^64,
modular nonoverlap of all source/destination bytes, initially readable source
bytes, and writable destination bytes. There are no extra alignment, positivity,
non-null, CPU-feature, or tunable assumptions. Pointers and count are 64-bit.
The result copies each ORIGINAL source byte to destination, preserves EVERY
outside-destination byte, returns X0=d, and preserves SP, X19..X30, the distinct
modeled R_LR, and entire modeled Z8..Z15 values. The exported frame theorem is
entry-trace scoped: a global noassign assertion on the wrapper-containing map
would be false.

`memcpy_small_witness_typed` and `memcpy_small_entry_inhabited` provide arbitrary
typed-memory, pointer and permitted-entry witnesses throughout the stated
nonoverlapping/nonwrapping domain. `memcpy_small_zero_entry` includes the
explicit d=s=n=m=0 witness. The huge finite permission mask is kept symbolic.
There are no new helper/callee contracts assumed instead of proved execution.

No medium/large or mempcpy/wrapper correctness, termination, fault freedom,
hardware/CPU/cache/IRQ behavior, or lifter refinement is claimed.

## Repair

All 16 initial theorem/lemma statements and every original definition/predicate
are retained byte-for-byte (see `audit-declarations.py` and its recorded run).
No contract correction or domain restriction was necessary. The initial scripts
were restored directly from both `.v.txt` archives before iterative repairs.
The missing pure `msub_add_l` arithmetic fact is proved in the ARM memory helper
without importing AMD64. The restored `msub_off` and `cpy_store` then compile.
The three witness proofs keep their original definitions and statements.

The main proof's tactic defects included a redundant command after an already
closed witness/entry goal, invalid `clear -;` syntax, a tactic-local identifier
binding, an unbound frame-tactic parameter, and an invalid nested disjunction
pattern. A final-size `subst n` also selected the register equation instead
of the case equality; the composition now rewrites the equality explicitly.
Those are repaired without changing mathematical statements.
The initial all-sizes symbolic expansion exhausted the assigned memory cap.
The repair closes one opaque `memcpy_small_case_0` through
`memcpy_small_case_32` at a time and composes those facts in the main theorem.
Scratch arithmetic flags and unused NG/OV values are abstracted after each
instruction; CY/ZR and every framed register remain available. Proved memory
contracts rewrite opaque getmem/setmem operations. Opaqueness and delayed
unfolding change proof conversion behavior, not the definitions or IL semantics.
Every successful result still receives a full kernel Qed check.

Logs preserve failed builds and explicit interruptions of superseded checks,
as well as isolated full-Qed checks for sizes 0, 1, 9 and 16. These isolated
checks alone are not a completion certificate for the full target.

## Reproduction and resource limits

No installation, shared environment change, remote write, push, PR, campaign
edit, other-branch mutation or subdelegation was performed. Only the prepared
local branch was renamed, after the successful empty fork collision query.
All proof builds and assumptions processes inherit `ulimit -v 2000000` KiB,
`ulimit -s 65536`, `-j1`, and disabled Dune cache; no concurrent proof compilers
were run. `32-resources.log` records the active compiler's actual hard/soft
address-space and stack limits and a roughly 1.1 GiB RSS observation.
`inspect-compiler.py` is a live-build diagnostic, not a post-build replay step.
`build.sh` and `assumptions.sh` set those limits explicitly and use the
existing read-only `arm-validation/picinae-env` wrapper.

```sh
bash tools/record-command.sh notes/a-memcpy-small-fix/27-build.log \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash notes/a-memcpy-small-fix/build.sh
bash tools/record-command.sh notes/a-memcpy-small-fix/34-assumptions.log \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash notes/a-memcpy-small-fix/assumptions.sh
```

The actual target is `Examples/claude/arm8_memcpy_small_proof.vo`, with its
`arm8_memcpy_common.vo` dependency. Root Dune already selects those exact modules
in the approved author checkpoint; the repair adds no unrelated module/glob.

## Ancestry

Initial HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole
parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`. The prepared
branch was clean before evidence creation (see `initial-clean-status.txt`).
After the empty read-only fork query, only that prepared branch was renamed.
An exact ff-only merge imported author checkpoint
`473a40d2fda1588cc8af046ddf0d060d858fb08d`. Above origin the allowed prerequisites
are exactly e00, `081d0233cd6667803b3907343b2fea6dc9eba714`,
`052521a753adbda077843ec7b259801282a7b1e9`,
`378fe1b57514b9af3f017a72b4ca665910156cc7`,
`9ae8e6800fa044797efd98372857e6ac89b18e1b`, and that author checkpoint.
Only this unit's scoped fix commit may follow it. `audit-ancestry.py` checks the
exact set, parent, branch, pinned origin, merge base and protected generated map.
The post-commit full SHA and clean status are recorded in the authorized external
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-memcpy-small-fix/`.

## Completed validation and theorem inventory

- `27-build.log`: full relevant target, exit 0; all 33 concrete size lemmas,
  the original main theorem, and its exported frame reach Qed.
- `33-artifacts.log`: emitted common `.vo` (178528 bytes) and main `.vo`
  (27084592 bytes), source hashes, and unchanged 16-statement/11-definition audit.
- `34-assumptions.log`: unedited Check and Print Assumptions output for all
  50 facts, exit 0. `37-assumptions-audit.log` classifies every fact, exit 0.
  The earlier classifier log 35 preserves a script-only counting failure:
  it overlooked the two inline Qed commands. The corrected checker counts
  all 50 Qeds, verifies all query outputs and rejects any other assumption.
- `29-source-audit.log`: exact pinned-base whole-tree source audit, exit 0.
  Baseline/current totals remain 7 Admitted, 1 admit, 89 module-interface
  Parameters; new suspicious-token totals are empty. Those admitted examples
  are not imported here; the transitive assumptions query is decisive.
- `28-declarations.log` and `33-artifacts.log`: every initial mathematical
  declaration retained verbatim, exit 0.
- `30-protected-inputs.log`: original author evidence, generated maps, manifest,
  pcode and Dune selection unchanged; exact hashes recorded, exit 0.
- `36-precommit-ancestry.log`: exact prerequisite set, branch and merge-base
  validation, exit 0. The post-commit exact-set/scoped-path audit, full SHA,
  complete origin-range log/stat and clean status are saved externally.

The seven original main-module facts are `memcpy_small_nwc`,
`memcpy_small_welltyped`, `memcpy_small_witness_typed`,
`memcpy_small_entry_inhabited`, `memcpy_small_zero_entry`,
`memcpy_small_correct`, and `memcpy_small_preserves_callee_saved`.
The original nine common facts are `byte_of_getmem`, `byte_setmem_cases`,
`cpy_empty`, `cpy_equiv`, `cpy_copied`, `addmsub`, `cpy_load`, `msub_off`,
and `cpy_store`. The new supporting facts are the proved pure `msub_add_l`
and `memcpy_small_case_0` through `memcpy_small_case_32`.

All ten common facts, nwc and the three witness facts are closed. Welltyping,
all 33 execution helpers, main correctness and the exported frame have exactly
this inherited transitive output (baseline provenance: notes/e00-build/README.md):

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The other results print verbatim `Closed under the global context`. No new
axiom or callee/kernel contract is assumed. All output, including failed and
interrupted attempts, is retained; none of those earlier attempts is counted
as the successful full-target validation.

The first staged whole-diff whitespace check exited 2 solely on original
whitespace in raw logs (the compiler's blank context line and `/proc/limits`
padding). Those outputs are deliberately preserved verbatim. The subsequent
staged source/script/documentation whitespace check excludes raw logs and
passes; both results are retained in the external unit evidence directory.
