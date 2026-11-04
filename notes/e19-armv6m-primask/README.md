# e19 ARMv6-M PRIMASK engineering

The unit adds genuine sequential PRIMASK register effects and separate strict
finite lifts of `ulSetInterruptMask` and `vClearInterruptMask`. No function
correctness, interrupt exclusion, asynchronous delivery, scheduling, callee
contract, safety or termination result is claimed. r42 owns mask callee proofs.
Full e05 remains PARTIAL, with its 24 blocked call closures unchanged.

Branch: `llm-proofs/e19-armv6m-primask`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-96390313`.
Only reviewed e00/e03/e04/e05 prerequisites and this unit's local commits are
allowed above pinned origin. No subagents, worktree creation, pushes, PRs,
remote comments, remote mutation, shared plan/status edits or shared environment
changes occurred. No external evidence directory was used.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No new dependency was installed. The existing wrapper, e04 compiler/ELF and
e05 standard-library-only Python venv were reused read-only. Two primary-source
PDFs were downloaded only into `.toolchains/e19-armv6m-primask/`. Text extraction
used the existing isolated `.refs/arm/manuals-tools/bin/pdftotext` read-only,
with temporary text in `/tmp`. Initial bare `pdftotext` was unavailable (exit
127); no host installation was attempted. No target binary was executed.

## Primary architecture sources

Read the actual PDFs, not an ARM7/ARMv7 substitute:

* [Arm ARMv6-M Architecture Reference Manual, DDI 0419E, ID070218](https://documentation-service.arm.com/static/5f8ff05ef86e16515cdbf826),
  issue E, 29 June 2018, SHA256
  `7a61a708b40748219991145090ad7dd8ee41474ff89f4e45219a32f5ea93632f`.
  B1.3.1 (B1-182) defines Thread/Handler mode and privilege, including the exact
  `CurrentModeIsPrivileged` rule. B1.4.3 (B1-188) defines the one-bit PRIMASK;
  B1.4.4-6 (B1-189) define CONTROL.nPRIV, reserved-bit RAZ/WI, and ordered
  architectural register updates. B4.1.1/Table B4-1 (B4-262) gives SYSm values;
  B4.2.1-3 (B4-264 through B4-267) give CPS/MRS/MSR T1 bits, operands and
  execution pseudocode. B1.5.8 (B1-198 onward) gives the exception-return
  boundary; the new profile conservatively excludes targets >=0xfffffff0.
* [Arm Cortex-M0 Technical Reference Manual, DDI 0432C, ID113009](https://documentation-service.arm.com/static/5e8e294afd977155116a6a5b),
  SHA256 `b4af6066093567dfb40fe641c55a2bd066fb487743d35bf22ced25da56e4383e`.
  Section 3.2 (3-3) confirms this core has privileged execution only. This
  justifies the explicit base-profile `nPRIV=0` guard for the Cortex-M0 fixture;
  it is not an assumption about every possible ARMv6-M implementation.

## Exact model boundary

`Picinae_armv6m.v` adds three typed one-bit state fields:

* `S_PRIMASK`: architectural PRIMASK.PM; reserved bits are absent, not unknown.
* `S_HANDLER`: whether CurrentMode is Handler. This is architectural mode state,
  not a new independently assumed permission bit.
* `S_CONTROL_NPRIV`: CONTROL.nPRIV, controlling Thread privilege on the optional
  U/P-extension profile. Handler remains privileged when nPRIV=1 (e.g. handling
  an exception from an unprivileged Thread).

Privilege is computed as Handler OR NOT nPRIV. The fragment never changes mode
or CONTROL, and makes no claim about transitions into/out of either. The base
profile rejects any input store with nPRIV != 0 at the finite program boundary.
It supports either Thread or Handler mode. The U/P profile models both Thread
privileges without assuming privilege. These fields are ordinary typed store
inputs; there are no added axioms or assumed privilege propositions.

CPSID writes mask=1 and CPSIE writes mask=0 only while privileged. MRS PRIMASK
writes a zero-extended one-bit mask into Rd when privileged, and 32-bit zero
when unprivileged. MSR PRIMASK writes source bit 0 when privileged; source bits
31:1 are ignored. Unprivileged writes have no effect. The operations preserve
NZCV, memory, access maps, mode, CONTROL and unrelated registers. Finite tests
check these observations; no general frame/callee theorem is asserted here.

This is an architectural register-state fragment in sequential Picinae IL.
The manual distinguishes register visibility from effects on execution priority
when priority decreases: CPS/MSR do not by themselves establish every guarantee
that follows an ISB/exception transition. This unit models neither priority
visibility timing nor asynchronous exceptions, interrupt delivery or memory
ordering. Mask=1 is not a proof that the FreeRTOS critical-section contract holds.
The inherited scalar instruction IL remains identical. Existing artifacts are
rebuilt against the expanded store; old proofs are not falsely transferred to
new mask functions. Legacy non-mask system approximations in `arm2il` remain
unusable through the strict frontend and are not certified by this work.

## Decoder and strict frontend

CPS accepts only exact `b662`/`b672`. MRS uses exact first halfword `f3ef`,
second halfword `8<Rd>10` for PRIMASK. MSR uses `f38<Rn> 8810`. r0-r12 and LR
are allowed; SP/PC are excluded. Fixed bits are enforced, including the
parenthesized bits in Arm's diagrams. Reserved SYSm values are invalid in the
Rocq decoder; valid but unmodeled SYSm registers remain strictly rejected.

`armv6m_lifter.sh --profile ...` exposes:

* `legacy-e03` (default): unchanged acceptance set and byte-identical lift text.
* `primask-v1-base`: only the two CPS encodings and exact MRS/MSR PRIMASK shapes
  are added. Generated maps enforce `armv6m_base_profile s` (`nPRIV=0`).
* `primask-v1-up`: same static encoding set, with explicit U/P mode semantics.

Both new profiles use `lift_armv6m_mask`. Its formal instruction guard excludes
all remaining system approximations, and its dynamic target guard excludes
BX/BLX/POP-PC exception-return targets, conservatively in both modes. Ordinary
BX LR remains available for the two real functions, with no invented exception
return. A rejected dynamic profile has no IL map entry (`None`); it does not
execute `Nop`, `Unknown`, or a made-up exception. Generated decoder facts for
new profiles check the formal static support predicate, independently of Python.
The old lift and its historical target behavior remain unchanged.

DSB/DMB/ISB, WFI/WFE/SEV/YIELD, SVC/BKPT, MSP/PSP/CONTROL and non-PRIMASK system
register encodings remain frontend-rejected. There is no approximation switch.
Real `vPortEnterCritical`/`vPortYield` still reject at DSB, assertion still rejects
at WFI, PendSV/SVC still reject at PSP. Critical nesting, barriers, exception
transitions and assertion behavior belong to e20/e21/e23; maps belong to e24.

## Provenance and artifacts

The reviewed prerequisite is `95da7ab7cee78f09a528aed86c1dfaf29520a9a8`.
The ISA originally came from timing `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`
via reviewed e03 `5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b`. No timing merge
or fork branch import occurred. The official FreeRTOS V11.1.0 source commit is
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`. The exact e04 ELF is
`.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf`, SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
The compiler is Arm GNU Toolchain 13.2.Rel1, GCC 13.2.1.

`Examples/FreeRTOSMask/` contains separate base-profile finite maps:
`ulSetInterruptMask` at 0x4090 (MRS, CPSID, BX LR) and
`vClearInterruptMask` at 0x4098 (MSR, BX LR). `generate.py` verifies the ELF hash,
assembles and disassembles a Cortex-M0 fixture independently, then regenerates
both exact real lifts and the fixture. `--check` compares without overwriting.
No pinned old e05 coverage, helper manifest or lift was edited.

The original e05 `--check` detects the changed frontend source hash in
`coverage.json`, as expected. `recheck-e05.py` executes the unchanged driver with
only its final comparison adapted in memory: it requires all other bytes to be
identical and allows exactly that provenance field to differ. It writes no old
artifacts, retains `__file__` for the real driver hash, and verifies all 90
artifacts. All 41 lift files, manifests, rejections and 24 blocked closures remain
unchanged; 89 files are identical, only coverage's frontend hash differs.

## Verification

The exact commands and real exit codes are in `logs/`; `validate.sh` provides
the final repeatable sequence. Every Rocq compiler is sequential, with
`ulimit -v 2000000`, `ulimit -s 65536`; Dune uses `--cache=disabled -j1`.
Assumptions checking uses `PROOF_MEMORY_KB=2000000`. No cap increase, host-wide
process kill, target execution or package install occurred.

Finite Rocq tests exercise both CPS effects for all mode/nPRIV/mask bits, all
14 valid MRS/MSR registers, eight source words that distinguish bit 0 from
reserved bits, and unrelated register/flag/memory/access/state observations.
They check every halfword in the CPS region, every reserved SYSm, SP/PC operand
rejections, bad fixed bits, independently assembled bytes, finite entry maps,
base-profile exclusions, actual mask lowerings and exception-return exclusions.
These are finite execution/decoder tests, not the r42 function proofs.
Python exhausts all 65,536 halfwords to verify the only 16-bit acceptance delta,
all register/SYSm templates, and all single fixed-bit mutations. It probes the
actual ELF with all three profiles, requiring zero stdout on each rejection.
The original e03 arithmetic/branch/stack tests and rejection tests are retained.

Final verification completed with exit 0 for every step in `validate.sh`:

* `generate.py --check` and `frontend-tests.py`;
* `dune build --cache=disabled -j1 --display short @armv6m-primask @Examples/FreeRTOSMask/freertos-mask-lifts`;
* `dune build --cache=disabled -j1 --display short` (full selective target);
* `legacy-check.sh`, including the original finite decoder/arithmetic/stack
  Rocq checks and all original strict ELF rejections;
* `recheck-e05.py ... --check` (89 identical artifacts, one hash-only metadata
  delta, all 41 original lifts and 24 blocked closures retained);
* `PROOF_MEMORY_KB=2000000 ... check-assumptions.py`: all **23 facts** report
  exactly `Closed under the global context`, including `welltyped_arm2il`,
  `welltyped_lift_armv6m_mask`, both real lift typing facts and every e19 finite
  test. The raw query is `assumptions-query.v.txt`; the complete raw output is
  `logs/final-assumptions.log`. No inherited axiom occurs in these facts.
* Full `audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006`
  and `git diff --check`. Baseline tokens remain seven `Admitted`, one `admit`
  and 89 module-interface `Parameter`; NEW is empty. None was added here.

The first full build in `logs/11-dune-full.log` actually compiled all inherited
core/ISAs, all 41 e05 lifts and AMD64/ARM8 smoke proofs, as well as the new tests.
The final mask build compiled the final regenerated mask artifacts and tests;
the subsequent full build succeeded incrementally. There is no pending Dune
verification. `provenance.json` records all exact input/source hashes, manual
versions and function bytes; `provenance.py --check` verifies that snapshot.
No engineering blocker remains within the explicitly bounded register fragment.

Earlier failed attempts are retained: missing Bool import (01, exit 1), a test
conjunction exceeding `auto`'s default search depth (04, exit 1), a mistaken
handler symbol name in a test (05, exit 1), and an unnecessarily large synthetic
memory address (09, out of memory, exit 1). The synthetic cell now uses address
zero; the same 2M cap is retained. Log 10 is the expected unmodified e05 hash
mismatch, superseded by the strict compatibility check in log 12. A later
sandbox DNS failure (16, exit 128) is superseded by the successful recorded
empty fork-name query (17, exit 0); the initial pre-rename query also succeeded.

## Ancestry and handoff

Prepared HEAD was exactly reviewed e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`. The exact read-only fork-name query
returned empty before renaming only `t3/96390313` to the assigned local branch.
The e00-to-e05 ancestry check passed, then `git merge --ff-only 95da7ab...`
imported only explicitly allowed e00/e03/e04/e05 ancestry. The first Git rename
hit read-only external Git metadata; the authorized local operation succeeded
through sandbox escalation. No fork branch was used as a base or changed.

`audit-ancestry.sh` requires origin to remain pinned at
`49956416928e5b6bb3928b54ae33e3b81091f006`, verifies that exact merge base and
e05 ancestry, and compares every post-e05 commit against an explicit own-SHA
list. It records `git log --oneline origin/llm_generated_proofs..HEAD` and
`git diff --stat origin/llm_generated_proofs...HEAD`, plus the unit diff.
Before/after logs accompany the handoff; full final SHA is returned separately.
Raw objdump output includes column padding. The unit-local `.gitattributes`
allows that trailing padding in raw logs, following the e03 evidence convention;
source whitespace checks remain enabled. The first staged whitespace check
flagged this raw padding before the evidence attributes were added.

Follow on with r42 for actual mask callee correctness and frames; e20 for
critical nesting/barrier effects; e21 for NVIC/MSP/PSP/exception transitions;
e23 for assertion WFI; e24 for map composition. None is certified implicitly by
these decoder/typing facts.

Implementation commit: `53d10faad31da182de6d1d2b084c9ef51f5d1cce`.
`logs/23-ancestry-after-implementation.log` (exit 0) records the merge base,
full origin-to-HEAD log and diff stat after that commit, admitting exactly that
one own commit above the reviewed e05 checkpoint. `logs/24-pinned-artifacts-unchanged.log`
(exit 0) confirms pinned e03/e04/e05 artifacts/notes are unchanged. A following
local evidence-only commit records this audit; its full SHA is the final handoff.
