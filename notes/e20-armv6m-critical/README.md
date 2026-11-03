# e20 ARMv6-M critical-section engineering — PARTIAL

This unit delivers an explicit sequential projection and separate strict finite
extractions of the actual FreeRTOS V11.1.0 `vPortEnterCritical` and
`vPortExitCritical`. It does not deliver architectural synchronization semantics.
Picinae cannot currently express the hardware observations needed for that
result. The exit assertion call closure also remains blocked. r43 owns function
correctness; no new function proof or assumed counter transition is introduced.

Branch: `llm-proofs/e20-armv6m-critical`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-126cc3e3`.
Prepared HEAD: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9` (e00).
Accepted prerequisite imported by exact fast-forward:
`0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6` (e19 plus reviewed e00/e03/e04/e05).
Pinned origin/base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing source: `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` via e03 only.
No fork history, extra units, subagents, new worktree, remote writes, pushes,
PRs, remote comments, shared plan/status edits or shared environment changes.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No installations occurred. Existing e04 cross tools/ELF, e05 Python venv,
arm-validation wrapper and e19 manuals were read-only inputs. PDF text was
extracted with the existing isolated `.refs/arm/manuals-tools/bin/pdftotext`
into `/tmp/e20-DDI0419E.txt`; no external evidence directory was written.
No target binary was executed. All generated artifacts/evidence are unit-local.

## Primary architecture evidence and concrete model gap

The actual Arm PDFs were read locally, with hashes independently checked.
Web fetches of the same official URLs timed out; no secondary source substitutes.
`provenance.json` pins document hashes, versions and URLs.

* [ARMv6-M ARM DDI 0419E ID070218](https://documentation-service.arm.com/static/5f8ff05ef86e16515cdbf826),
  SHA256 `7a61a708b40748219991145090ad7dd8ee41474ff89f4e45219a32f5ea93632f`.
  A3.7.3 (A3-59) distinguishes explicit data-access ordering, completion and
  instruction-context synchronization. A6.7.21/22/24 (A6-121/122/124) give exact
  DMB/DSB/ISB T1 encodings. The only supported option is SY (0xf), with full
  system scope/all explicit accesses. Other options are reserved; although the
  manual specifies SY execution, software must not rely on it. We reject them.
  DMB orders observations of explicit memory accesses without requiring their
  completion; it does not order every instruction. DSB waits for preceding
  explicit accesses and cache/branch-maintenance operations to complete before
  subsequent instructions execute. ISB synchronizes instruction fetch/context
  after earlier completed context changes. These are distinct obligations.
  B1.4.6 distinguishes register visibility from other architectural effects;
  B2.5 (B2-221) explains SCS write completion and side-effect visibility through
  DSB/ISB. Those effects cannot be inferred from an ordinary Picinae store.
* [Cortex-M0 TRM DDI 0432C ID113009](https://documentation-service.arm.com/static/5e8e294afd977155116a6a5b),
  SHA256 `b4af6066093567dfb40fe641c55a2bd066fb487743d35bf22ced25da56e4383e`.
  3.2 confirms privileged-only execution on this specific core. We retain e19's
  dynamic `nPRIV=0` base guard and Handler/Thread state; no transition is assumed.

The base IL has a sequential register store and a single dense byte-memory
value. It has no pending transactions, externally observed order, DMA/other
observers, instruction prefetch/pipeline, memory attributes, NVIC side effects,
execution-priority visibility delay, or exception delivery/return transitions.
It cannot faithfully express whether DSB has completed a peripheral write or
ISB made a changed system context visible. Adding an arbitrary counter or a
barrier marker would not fill that gap. No architectural refinement theorem is
asserted; overall status is therefore PARTIAL.

## Exact supported sequential boundary

`Picinae_armv6m_sync.v` leaves `Picinae_armv6m.v` entirely unchanged. Its new
strict decoder accepts exactly `f3bf 8f4f` (DSB SY), `f3bf 8f5f` (DMB SY), and
`f3bf 8f6f` (ISB SY), requiring every fixed bit. The disjoint BL second-halfword
class with first halfword `f3bf` is retained. Nonbarrier operations delegate to
the e19 mask wrapper, including its EXC_RETURN guards and unsupported-system
rejections. No inherited permissive barrier decoder is used for the new shapes.

A sync view is `option sync_kind * (length * stmt)`. At each admitted barrier
address it records a distinct DMB/DSB/ISB occurrence and length 4. The tag is an
instruction occurrence annotation, not evidence of completed synchronization.
Ordinary instructions carry no tag. The generated `_sync_view` is a finite,
state-dependent map with the base and normal-return guards. It is not a dynamic
execution trace: clients must retain tags along their chosen instruction path
if they need occurrence observations. A static map does not prove reachability.

`armv6m_sync_project` explicitly discards the occurrence tag; only in this
**named sequential projection** does a barrier become a length-4 Nop. Its entire
observation domain is sequential GPR/flag/memory/PRIMASK/mode state, ordinary
jumps and IL fault exits. Claims about hardware ordering, access completion, IRQ exclusion/delivery,
MMIO, instruction-fetch coherence, synchronization timing or system-context
visibility are outside that domain. No such claims are attached to typing.
The projection is a specified engineering abstraction, not a proved simulation
of hardware. Occurrence views and projected programs are exported separately.

The only new CLI profile is `critical-seq-v1-base`; e03 remains the default and
both e19 profiles retain exactly their acceptance/output behavior. It enforces
`nPRIV=0` at every entry. The high/MMIO literal filter conservatively rejects any
literal word >=0x40000000 in the new profile, including actual `vPortYield`'s
0xe000ed04 NVIC address. This can reject scalar high constants too, deliberately.
It is a static filter, not a proof about values of variable pointers: callers
still need ordinary-memory/access/stack contracts. No MMIO/NVIC meaning is
assigned to a write to the pure memory value. WFI, PSP, CONTROL, SVC, PendSV and
exception transitions remain rejected/outside e20. No U/P synchronization
profile was invented; finite direct-instruction tests of inherited privilege
behavior are not admission of nPRIV=1 into the base map.

## Actual binary and call closure

Input: `.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf`,
SHA256 `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
Official FreeRTOS V11.1.0 source commit:
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`.
Compiler: Arm GNU Toolchain 13.2.Rel1, GCC 13.2.1.
`provenance.json` records exact function bytes, every instruction, literal
address/value, direct call, tool/source hash and the actual global symbol.
`logs/critical.objdump` is the independent actual binary disassembly.

Enter is at 0x3e68, sized 24 bytes including its literal pool: CPSID, literal
address load of 0x20000000, memory load, 32-bit increment, memory store, DSB SY,
ISB SY, BX LR. It has eight executable entries and no direct calls.
Exit is at 0x3e80, sized 48 bytes including pools: push, actual nesting load and
zero check, branch to assertion on zero, reload/decrement/store/reload/check,
conditional skip around CPSIE, pop PC, assertion arguments and BL at 0x3ea0
to `fixture_assert_fail` at 0x419c. It has seventeen executable entries.
Literal/data halfwords, second halves and out-of-range addresses are absent
from the executable maps. Immutable literal bytes are a trusted extraction
precondition; no missing callee is filled with a stub.

Nesting is the four-byte object `ulCriticalNesting` at 0x20000000. Actual loads
and stores remain in the IL; no separate counter state or assumed transition
replaces them. Increment is 32-bit modular arithmetic. No overflow exclusion,
underflow exclusion, pairing discipline, reentrancy, atomicity or interrupt
exclusion is proved. The zero exit path remains the actual assertion call, not
an assumed return/nonreturn or an unreachable branch. BL writes LR=0x3ea5;
its would-be return address 0x3ea4 is literal data, absent from the finite map. Its callee rejects at WFI
0x41a6, so the exit/caller closure remains BLOCKED on e23/r44. r43 must provide
satisfiable preconditions/invariants and the real path/ABI/memory-frame results.
The CPSIE instruction retains e19 privilege behavior. Its execution depends on
the actual comparison/branch path; Handler mode does not imply safe unmasking.
No exception arrival, priority change or interrupt exclusion follows here.

## Validation and evidence

`validate.sh` is the exact repeatable command sequence. All Rocq/Dune/assumption
checks run sequentially with `ulimit -v 2000000`, `ulimit -s 65536`; Dune uses
`--cache=disabled -j1`. Only one compiler runs at a time, with no cap increase.
Each log records CWD, exact command, complete output and real exit code.

The finite Rocq fixtures cover assembled instruction shapes, reserved options,
all 65,536 barrier second halfwords (including the disjoint BL class), distinct
barrier views, projected state/frame samples, actual global literal lowerings,
finite map/base/EXC_RETURN exclusions, conditional branch/CPSIE instructions,
actual assertion-call target and return-address write, and actual load/store
opcode shapes and modular arithmetic samples (including wrap). The latter run with small test addresses to keep dense memory
finite under the cap, **not** as a relocated function execution. No function
contract is inferred from any sample. The real high global address is checked
in the actual bytes, symbol table, literal lowering and manifest.

Python exhausts 16-bit acceptance, all barrier second halfwords/options,
register/SYSm templates and fixed-bit mutations. Private mutated ELFs test
reserved options, invalid fixed bits, late WFI and zero stdout on every failed
extraction. Actual ELF probes preserve old profile rejection behavior, accept
the new critical bodies, reject vPortYield at its high/MMIO literal, WFI at
assertion, and PSP at exception handlers. A changed width that yields valid
scalar instructions is not mislabeled a malformed barrier.

Compatibility checks compare all old 16-bit predicates and every second
halfword of the old system/BL templates, reproduce original e19 lifts/fixture,
run unchanged e19 frontend/e03 finite regression tests, and regenerate all 90
e05 artifacts. Only coverage's frontend-source-hash field may differ; all
other data including the 41 old lifts and 24 blocked closures stays identical.
Original e03/e04/e05/e19 artifacts are unchanged in Git.

Final successful commands, assumptions counts, audits and commit identifiers
are recorded below after validation finishes. Earlier failed attempts remain
in logs: missing NArith notation/type-scope imports (03/04), initial mutation
expectations overlooking valid BL or a distinct valid barrier (06/07), an
initial rejection test that changed instruction width into valid scalar code
(08), and old fixture reproduction with a different object basename (11).
The latter changed ELF metadata/hash; reproducing with original `snippets.o`
restored byte-identical fixture output (12). No admission was used to repair any
failure. Failed runs are not counted as verification.

## Handoff

Use r43 only for sequential projected contracts until a separate hardware
model/refinement exists. e23/r44 must handle/exclude the actual assertion path
with satisfiable premises. e24/r45 must compose finite call maps without hiding
missing targets. e21/r46 retain all NVIC/PendSV/MMIO/exception/yield obligations.
A future synchronization extension needs external-access observation/completion
and instruction-context/priority state plus a hardware refinement argument;
the present annotation view supplies occurrence information only.

## Final verified results

Every step of `bash notes/e20-armv6m-critical/validate.sh` completed with exit 0.
Toolchain verification also exited 0: Rocq 9.1.1 / OCaml 4.14.2 / Dune 3.22.2,
with inherited limits exactly 2000000 KiB address space and 65536 KiB stack.
No Dune verification is pending. The default build compiled the final source
versions (including the modular arithmetic sample); byte comparisons against
`_build/default` confirmed the checked module/test sources are current.

Exact successful commands (the runner/venv paths and all arguments are recorded
verbatim in the named logs and `validate.sh`):

* `generate.py --check` — exit 0, `logs/final-generation.log`.
* `frontend-tests.py` — exit 0, `logs/final-frontend.log`; negative extraction
  subprocesses deliberately exit 1 with empty stdout, asserted by the test.
* `picinae-env dune build --cache=disabled -j1 --display short @armv6m-critical @Examples/FreeRTOSCritical/freertos-critical-projections`
  — exit 0, `logs/final-dune-critical.log`.
* `picinae-env dune build --cache=disabled -j1 --display short`
  — exit 0, `logs/final-dune-default.log` (full selective default).
* `PROOF_MEMORY_KB=2000000 picinae-env .../venv/bin/python -B notes/e20-armv6m-critical/check-assumptions.py`
  — exit 0, `logs/final-assumptions.log`. All **22 facts** report exactly
  `Closed under the global context`, with no inherited axioms in those facts.
  The complete raw query is `assumptions-query.v.txt`; output is saved verbatim.
  These include the new projection typing theorem, all generated typing/decode
  facts, finite fixtures and the inherited typing facts on which they depend.
* Unchanged e03 `legacy-check.sh`, e19 `frontend-tests.py`, and new
  `compatibility.py` — each exit 0 in the corresponding `final-*` logs.
* e19 `recheck-e05.py` with the pinned e04 ELF, objdump and source paths
  — exit 0, `logs/final-e05-compatible.log`: all 90 artifacts checked,
  89 byte-identical plus only coverage's expected frontend-hash metadata delta.
  Old 41 bodies and all 24 blocked call closures are preserved.
* `provenance.py --check`, `audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006`
  and `git diff --check` — each exit 0 in the corresponding `final-*` logs.
  Source audit NEW totals are empty; inherited baseline remains seven
  `Admitted`, one `admit`, and 89 module-interface `Parameter` tokens.
  None was added by this unit, and none is an assumption of the 22 queried facts.

Before renaming, `git ls-remote --heads fork refs/heads/llm-proofs/e20-armv6m-critical`
returned exit 0 with empty output (the first sandbox DNS attempt exited 128;
read-only network escalation succeeded). The observed prepared branch was
`t3/126cc3e3`, then T3 named it `t3/armv6m-critical` before the local rename.
The first rename hit read-only Git metadata; the explicitly authorized local
rename and exact `git merge --ff-only 0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6`
then succeeded through sandbox escalation. No fork branch was used or changed.
A recorded read-only empty remote-name recheck is in `logs/fork-collision-recheck.log`.

`logs/00-prepared-head.log` replays the prepared e00 commit's merge-base,
origin-to-prepared log and diff stat; the original checks were also performed
before rename/import. `logs/01-imported-ancestry.log` records the accepted
import and its full base diff. `audit-ancestry.sh` enforces the pinned origin,
exact merge base, exact accepted e19 ancestor, assigned branch, and an explicit
list of own commits above it. The after-implementation audit is recorded in
a subsequent evidence commit; final full SHA and clean-tree audit are returned
in the handoff. Partial status refers to the documented semantic/closure gaps,
not to a failed or pending build of the engineering subset.
