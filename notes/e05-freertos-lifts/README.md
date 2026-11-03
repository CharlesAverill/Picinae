# e05 FreeRTOS lifts: partial full-unit completion

All 41 planned actual function bodies from the exact e04 FreeRTOS V11.1.0
Cortex-M0 ELF have reproducible finite ARMv6-M extractions and full `.vo`
decoder/typing/data checks. **Full e05 remains PARTIAL**: 24 call closures reach
six strictly rejected helpers; exception and interrupt models are missing.
No new function correctness proof was attempted, and no correctness, safety,
termination, frame or ABI-preservation theorem is claimed.

Branch: `llm-proofs/e05-freertos-lifts`.
Prepared worktree: `/home/charles/.t3/worktrees/Picinae/t3-a0eced30`.
There were no subagents, worktree creation, pushes, PRs, comments or remote writes.
No shared campaign plan/status files were edited. All evidence is in this
repository; there are no external evidence writes.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

The only environment creation was:

```bash
python3 -m venv --without-pip /home/charles/code/friends/.toolchains/e05-freertos-lifts/venv
```

It exited 0. No packages were installed. Python uses only its standard library.
Rocq 9.1.1, OCaml 4.14.2 and Dune 3.22.2 were verified through the existing
read-only wrapper (`logs/05-toolchain.log`, exit 0). The e04 compiler/objdump,
ELF and sources were reused read-only. Every compiler invocation was sequential,
with address-space limit 2,000,000 KiB and stack 65,536 KiB, Dune `-j1` and cache
disabled. Assumptions queries set `PROOF_MEMORY_KB=2000000` and enforce the same
limits. No cap increase or process killing occurred.

## Provenance and deliverables

The pinned official kernel V11.1.0 commit is
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`.
The read-only input is
`/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf`,
SHA256 `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
GCC is Arm GNU Toolchain 13.2.Rel1, 13.2.1. The e04 manifest pins source files,
config, symbols, layout probes, map, binary and tools. The driver verifies the
ELF, layout, symbols, map, config, expanded config and source hashes; it compares
the original e04 disassembly byte-for-byte before analyzing instructions. ELF
bytes, mapping symbols and actual symbol metadata are checked against those
records. It calls the unchanged reviewed e03 frontend on each planned entry.
The ISA's upstream provenance remains timing commit
`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`, as documented by e03; no timing
branch or unrelated history was merged into this unit.

Generated artifacts are in `Examples/FreeRTOS`:

- 41 `<fn>_armv6m.v` files, with original absolute addresses, all instruction
  starts, mapped data, needed complete literal words and finite `_prog` maps.
- 41 `<fn>.json` manifests: source/body/ELF hashes, opcodes, Thumb symbols and
  return candidates, exact literals/global references, call/branch edges,
  critical/ISR call boundaries, unproved callees and transitive rejected helpers.
- `abi.json`: exact compiled type/field offsets, all global/object addresses,
  source/config/map hashes and the ABI boundary. The generic AAPCS requirements
  are documented as future proof obligations, not established preservation facts.
- `coverage.md`/`coverage.json`: honest extraction and closure coverage.
- `helpers.json`: 33 transitively reached helpers, including 27 supported but
  unextracted ordinary bodies and six strictly rejected system helpers.
- `helper-rejections.json`: exact commands, exit 1, zero stdout, first frontend
  failure and all diagnostic unsupported opcodes for those six helpers.
- `asynchronous-boundaries.json`: real SysTick/PendSV/SVC/first-task boundaries,
  with separate strict frontend probes. SysTick's body passes, but no exception
  contract is inferred; PendSV/SVC/first-task reject. No programs are committed
  for these diagnostic probes.
- One Dune alias per function and the aggregate
  `@Examples/FreeRTOS/freertos-lifts`; explicit modules in root `dune`.

The driver is `Examples/freertos/cortex-m0/extract.py`. Future function proofs
must use separate `armv6m_<fn>_proof.v` files. `Examples/FreeRTOS/README.md`
explains finite-map boundaries, literal immutability and return obligations.
The corrected inventory uses `uxQueueMessagesWaiting`,
`xTimerGenericCommandFromTask` and `xTimerGenericCommandFromISR` (r41).

## Actual validation

Run the final checked workflow from this worktree:

```bash
bash notes/e05-freertos-lifts/validate.sh
```

Exact commands, stdout/stderr and real exits are stored in `logs/`. This script
uses the no-pip venv and the existing isolated Picinae wrapper. Its extraction
command is:

```bash
/home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python -B \
  Examples/freertos/cortex-m0/extract.py \
  --elf /home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf \
  --objdump /home/charles/code/friends/.toolchains/e04-freertos-build/arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin/arm-none-eabi-objdump \
  --source /home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0 \
  --check
```

This exits 0 only when all 90 generated artifacts (including root `dune`)
reproduce byte-for-byte. All 41 planned frontend calls exit 0. The six helper
calls and three exception/first-task calls exit 1 as expected, with no partial
Coq stdout. The separate SysTick body probe exits 0; none of these four
asynchronous probes contributes a generated proof artifact.

Verified build commands, run inside the wrapper with the caps above:

```bash
dune build --cache=disabled -j1 --display short @Examples/FreeRTOS/freertos-lifts
dune build --cache=disabled -j1 --display short
```

Both exited 0. `logs/06-dune.log` records the initial absent-output build of the
ISA dependency closure and all 41 generated `.vo` files. `logs/09-dune-full.log`
records the subsequent full selective build, including inherited core and
AMD64/ARM8 abs smoke proofs. These are actual full `.vo` checks, not `.vos`.
Final rechecks are `logs/recheck-dune-full.log` and `logs/recheck-assumptions.log`.
No Dune verification remains pending.

The assumptions command is:

```bash
env PROOF_MEMORY_KB=2000000 \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  /home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python -B \
  notes/e05-freertos-lifts/check-assumptions.py
```

It exited 0. It runs the aggregate Dune target, then one capped Rocq compiler
over `Check` and `Print Assumptions` queries for **all 258 facts**: 41 decode,
41 typing, 41 Thumb-entry and 132 literal facts, plus inherited
`welltyped_lift_armv6m`, `welltyped_armv6mprog`, `welltyped_arm2il`. Every query
reports exactly:

```text
Closed under the global context
```

Verbatim full output is in `logs/12-assumptions.log` and the final recheck log;
the complete query text is `assumptions-query.v.txt`. The checker requires 258
closed reports and fails on any nonzero compiler exit or assumptions list.
These facts do not import an admitted lemma. No functional theorem exists here
for which assumptions could be reported.

The source audit against pinned origin exited 0:

```bash
/home/charles/code/friends/.toolchains/e05-freertos-lifts/venv/bin/python -B \
  tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006
```

It found no new `Admitted`, `admit`, `Axiom` or `Parameter`. The baseline remains
seven `Admitted`, one `admit` and 89 module-interface `Parameter` tokens;
those baseline files are unchanged by this unit. See `logs/10-source-audit.log`
and final `logs/recheck-source-audit.log`. `git diff --check` also exits 0.

Earlier failures are retained honestly: `03-extraction.log` exited 1 because
the initial driver compared `objdump -d -z` against e04's `-d -w` output. The
driver now independently verifies the exact e04 command output and uses `-z`
for complete instruction diagnostics. No ISA/frontend checks were relaxed.
`01-before.log` contains a sandbox DNS failure and a shell whose final command
masked that failure; its exit 0 is not evidence of a successful remote check.
`02-prerequisite-import.log` supersedes it with a successful, empty exact fork
collision check and fail-fast ancestry/import command (exit 0). Initial local
Git writes were sandbox-blocked and completed through the permitted escalation.

## Ancestry audit

Initial HEAD was exactly reviewed e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`; the worktree was clean before
creating evidence. The prepared local branch was renamed only after the exact
read-only `git ls-remote --heads fork refs/heads/llm-proofs/e05-freertos-lifts`
check returned empty and e00-to-e03 ancestry passed. No fork branch was used
as a base or changed.

Pinned origin and merge base are
`49956416928e5b6bb3928b54ae33e3b81091f006`. The only imported ancestry above it is:

- e00: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
- e03 original: `59f696d32a5623cdfbceb9a1e0f91e2cc7c054c1`.
- e03 prerequisite integration: `dac36c0a03088a90bb6e6385f82cb355d27cc204`.
- e03 final Dune validation: `5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b`.
- e04: `abe7eda601a63d47eb70e765f4ae2c4ca235cca4`.

e03 was fast-forwarded from e00, then e04 was merged with own integration
commit `8c01958e73ec7fe959c60b29444505afbb599d13`
(`Merge reviewed FreeRTOS fixture into e05 lifts`). Only e05's own commits
follow that integration. `audit-ancestry.sh` verifies the exact allowed commit
set and unchanged e03 model/frontend and e04 fixture, then prints the requested
merge base, origin-to-HEAD log and diff stat. Before/after evidence is retained
in `logs/01-before.log`, `logs/14-ancestry-before-commit.log` and the committed
after-implementation audit. The final handoff supplies the full final SHA.

## Concrete blockers and proposed follow-on units

All exact rejected addresses/opcodes are in the coverage matrix and manifests.
The following are engineering/model prerequisites, not waived IRQ contracts:

1. PRIMASK/CPS: `ulSetInterruptMask` at `0x4090` (`f3ef 8010`, MRS PRIMASK)
   and `0x4094` (`b672`, CPSID); `vClearInterruptMask` at `0x4098`
   (`f380 8810`, MSR PRIMASK). Model the register and actual mask transitions.
2. Critical nesting/barriers: `vPortEnterCritical` at `0x3e68` (`b672`),
   `0x3e72` (`f3bf 8f4f`, DSB), `0x3e76` (`f3bf 8f6f`, ISB);
   `vPortExitCritical` at `0x3e98` (`b662`, CPSIE). Use the exact
   `ulCriticalNesting` global at `0x20000000`; establish contracts separately.
3. PendSV/NVIC: `vPortYield` barriers at `0x3e58`/`0x3e5c` and the ICSR
   write to `0xe000ed04`. Ordinary memory typing does not trigger PendSV.
   PendSV entry `0x40a0` rejects MRS PSP; SVC rejects MRS PSP at `0x40f8`;
   first-task entry `0x4080` rejects CPSIE. Model PSP/MSP, handler transitions
   and exception return explicitly; inspect the full asynchronous manifest.
4. Assertion boundary: `fixture_assert_fail` at `0x419c` (`b672`, CPSID) and
   `0x41a6` (`bf30`, WFI). Either model the real nonreturning behavior or prove
   the call unreachable from an explicit satisfiable function precondition.
5. Ordinary helper extraction/contract groups: queue copying/locking
   (`prvCopyDataToQueue`, `prvCopyDataFromQueue`, `prvUnlockQueue`), task
   ready/delayed/event-list management (`prvAddCurrentTaskToDelayedList`,
   `prvAddNewTaskToReadyList`, `xTaskResumeAll`, event-list helpers), stream
   read/write helpers plus the actual e04 newlib `memcpy`/`memset`, and static
   task/stack initialization. `helpers.json` lists all 27 supported but
   unextracted helpers. Add finite-map composition as a small separate unit;
   then prove each real callee's functional, preservation and frame contract.

The 17 entries without rejected helpers are the five list functions, task
count/current/tick/tick-ISR getters, suspend-all/missed-yield setters,
reset-event-value, internal-timeout-state, mutex-held-count, scheduler-state,
next-unblock-time and name-search. These are candidates for r00/list/leaf proof
work once authorized; extraction alone is no proof. The remaining entries
cannot be declared supported whole-kernel paths merely because their own
bodies decode. No remote publication is authorized by this handoff.
