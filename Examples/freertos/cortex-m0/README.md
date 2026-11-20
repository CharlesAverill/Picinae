# FreeRTOS Cortex-M0 extraction fixture (e04-freertos-build)

This builds a real, statically linked ARMv6-M FreeRTOS kernel for later e05
extraction. It contains normal, unmodified official C kernel sources and the
official GCC ARM_CM0 port, including `port.c` **and** `portasm.c`. It does not use
the RISC-V `RTOSDemo.elf`, timing tests, replacement kernel assembly, or mocks.
No target execution, lifting, typechecking, or functional correctness proof was
performed. Theorem checking and `Print Assumptions`: **N/A (binary-only unit)**.

## Reproduce

From the repository root:

```sh
make -j1 -C Examples/freertos/cortex-m0 RUN=build
```

Use a fresh `RUN` name for subsequent invocations; existing artifacts and logs
are never overwritten. A run builds **twice**, serially, from separately
extracted, checksum-verified source archives. `E04_ENV` can select a distinct
`/home/charles/code/friends/.toolchains/e04-freertos-build-*` directory.
The default isolated environment is:

```
/home/charles/code/friends/.toolchains/e04-freertos-build
```

`reproduce.sh` creates a local Python venv using `/usr/bin/python3 -m venv
--without-pip`. `build.py` uses only the standard library (Python >=3.11) and
limits its entire process tree to an 8,000,000,000-byte address space. Existing
host `make`, `curl`, `sha256sum`, and `cmp` are used; nothing is installed into
the host. All compiler/source archives, unpacked dependencies, firmware,
objects, and build outputs stay in the per-unit environment. No shared
environment is changed. The first build requires network access to official
download URLs; cached builds verify the same pinned archive hashes.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

## Pinned inputs and compilation

`inputs.json` records official URLs, immutable source identity, and archive
SHA256 checksums. No local evidence identified a preferable pinned release.

- FreeRTOS-Kernel **V11.1.0**, annotated tag object
  `f388a5c8078e152913e4eb3c5d75bf89561392df`, peeled commit
  `dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`.
  Official commit archive SHA256:
  `31e570365bc3feb7fbbfa36b93cbc4e2da22f4d02801a1b1513b0f25594f1cea`.
  License: MIT; verbatim `LICENSE.FreeRTOS` and original source notices.
- Official Arm GNU Toolchain **13.2.Rel1**, x86_64 Linux / arm-none-eabi.
  GCC reports `13.2.1 20231009`, build `arm-13.7`. Archive SHA256, checked
  against Arm's published `.sha256asc`:
  `6cd1bbc1d9ae57312bcd169ae283153a9572bd6a8e4eeae2fedfbc33b115fdbb`.
  Compiler, cc1, assembler, linker, inspection tools, target libc/libgcc, and
  license hashes are in `evidence/manifest.json`. The toolchain's `license.txt`
  contains its component terms, including GCC runtime and newlib notices.

The exact common flags and per-invocation commands are in `build.py` and
`evidence/commands.jsonl`. Every kernel and platform translation unit uses
`-mcpu=cortex-m0 -mthumb -mfloat-abi=soft -O1`, with DWARF4 debug information,
`-ffreestanding -fno-builtin`, no LTO, no regular inlining or IPA specialization,
and `-fkeep-static-functions`. Function/data sections are enabled for inspection,
but **linker garbage collection is not enabled**. This intentionally retains
planned getters and private helpers, including unreferenced functions.
Required port `always_inline` definitions remain governed by upstream source.

Linked kernel translation units are `list.c`, `tasks.c`, `queue.c`,
`event_groups.c`, `stream_buffer.c`, `timers.c`,
`portable/GCC/ARM_CM0/port.c`, and `portable/GCC/ARM_CM0/portasm.c`.
`platform.c` is the only application/startup translation unit. The only library
members pulled into the ELF are the toolchain's real newlib `memset`, `memcpy`,
and `strlen` implementations from `thumb/v6-m/nofp/libc.a` (some upstream
archive member names contain `-stub`; these contain normal implementation code,
not fixture stand-ins). `libgcc.a` is offered to the linker but contributes no
member in the recorded map. There are no unresolved ELF symbols or allocator
stubs. `-nostartfiles -nostdlib` avoids a vendor board startup or host libc.

`SOURCE_DATE_EPOCH=1715904000`, `LC_ALL=C`, `TZ=UTC`, prefix maps, and disabled
build IDs remove timestamp and build-directory variation. `__FILE__` paths
become `/kernel/...` or `/fixture/...`. The two ELF files include identical
debug information as well as code/data. The map/log paths intentionally retain
the actual build directories for audit.

## Configuration and ABI

`FreeRTOSConfig.h` is part of the binary identity. The complete preprocessed
configuration is saved in each output's `config-macros.txt`. This is single-core,
preemptive, time-sliced, 5 priorities, 32-bit ticks, 16-byte task names,
notifications with one array entry, static allocation only, mutexes/recursive
mutexes/counting semaphores, event groups, stream/message buffers, and software
timers. The mutex-holder, task-state, task-name-search, suspend, delay, and
scheduler getters/helpers are enabled. Assertions remain enabled and call a
separate platform failure loop. MPU, tickless idle, queue sets, trace/runtime
statistics, newlib task TLS, and heap allocation are disabled.

`layout-probe.c` includes one unmodified kernel `.c` file per compile-only probe
so GCC can evaluate actual private `sizeof`, `_Alignof`, and `offsetof` values.
The probes never enter the firmware and are never executed. Values are extracted
as little-endian fixed records from `.picinae_layout` and saved in `layout.json`.
Each private structure's size is checked against its public static counterpart.
For this exact build:

| Type | Size (bytes) | Selected offsets (bytes) |
|---|---:|---|
| `ListItem_t` | 20 | value 0, next 4, previous 8, owner 12, container 16 |
| `MiniListItem_t` | 12 | value 0, next 4, previous 8 |
| `List_t` | 20 | count 0, index 4, end sentinel 8 |
| `TCB_t` | 84 | top of stack 0, state list 4, event list 24, priority 44, name 52, base priority 68, mutex count 72, notified value 76, notify state 80 |
| `Queue_t` | 72 | mutex holder 8, send list 16, receive list 36, messages 56, length 60, item size 64, RX/TX locks 68/69 |
| `EventGroup_t` | 24 | bits 0, waiting list 4 |
| `StreamBuffer_t` | 36 | tail 0, head 4, length 8, buffer 24, flags 28, notification index 32 |
| `Timer_t` | 40 | list item 4, period 24, ID 28, callback 32, status 36 |

Pointers, `BaseType_t`, `UBaseType_t`, `StackType_t`, and `TickType_t` are all
4 bytes. All listed structure alignments are 4; the port requires 8-byte stack
alignment. The port declares 32-bit tick loads atomic: future proofs must follow
the actual getter instructions rather than presume every tick getter masks IRQs.

## Symbol handoff

`evidence/symbols.json` contains 202 functions and 52 objects, with symbol values,
normalized code addresses, sizes, linkage, section, and source translation-unit
origins. Thumb `st_value` has bit 0 set; **clear that bit for extraction**.
`nm.txt`, the linker map, and the full ELF preserve private functions, globals,
literal pools, and ARM mapping symbols. No symbols were stripped.

`planned-symbols.txt` maps all r01-r40 rows to actual V11.1.0 entries;
`planned-availability.json` verifies every row. Both r40 entries are present.
No planned function row needs pruning for this configuration, but two names need
correction before e05 generation:

- r20: `xQueueMessagesWaiting` in the plan/timing filename is actually
  **`uxQueueMessagesWaiting`**.
- r40: `xTimerGenericCommand` is an upstream macro. Split its implementation
  work into **`xTimerGenericCommandFromTask`** and
  **`xTimerGenericCommandFromISR`** rather than searching for a nonexistent body.

`gated-availability.json` records representative **absent** dynamic-allocation,
queue-set, trace, and allocator entries; new units for those APIs must be pruned
or assigned a different binary configuration. The remaining emitted public and
private helpers are enumerated by `symbols.json` for follow-on unit expansion.

## Validation and limits

Final command, from the worktree root:

```sh
make -j1 -C Examples/freertos/cortex-m0 RUN=verified02
```

**Exit 0.** All **110** recorded subprocess invocations exited 0. This includes
two full builds, five layout probes per build, ELF inspection, undefined-symbol
checks, vector-to-handler checks, planned/gated symbol checks, and ten successful
`cmp` commands. The exact argv/cwd/exit records are in `evidence/commands.jsonl`;
verbatim output is in `evidence/build.log.gz` and `evidence/console.log.gz`.
Host orchestration versions were GNU Make 4.3, Python 3.12.3 in the no-pip venv,
Git 2.43.0, curl 8.5.0. No package install was performed.

- ELF SHA256: `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
- `.text` (code + constants/literal pools) SHA256:
  `047d482ecfce1814f0e563a77da8f8349e9995dda8598ee2b6cee5dacc440db3`.
- `.data` SHA256:
  `824d5539cfad095ba33d7553aff77d991feeb6b62104588afae10fba545c8a01`.
- Flash binary, vectors, layout, symbols, availability, and ISA-audit JSON also
  compare identically; see `evidence/comparison.json`.

ISA evidence is `elf32-littlearm`, EABI5 soft float, `Tag_CPU_arch: v6S-M`,
microcontroller profile, `Tag_THUMB_ISA_use: Thumb-1`, zero ARM-state mapping
symbols, and all function entries marked Thumb. The 7,006 decoded instructions
contain 692 wide BLs, 8 MRSs, 6 MSRs, 3 DSBs, and 4 ISBs; all other decoded
instructions are 16-bit. These wide forms are valid on ARMv6-M. Data/literal
pools are handled as data according to the mapping symbols. No unknown/undefined
instruction appears in the disassembly. This is compiler/ELF/disassembly
evidence, **not** a formal instruction-set or runtime correctness proof.

The verified ELF is at:

```
/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf
```

The independent second copy is under `verified02-b/out`. Both output directories
contain full maps, disassembly, macro dumps, layout probes, and manifests with
per-file hashes of the entire unmodified source archive and all generated output.
Committed evidence contains the first map plus compressed disassembly/config
and full command logs; firmware/source/dependency binaries are not committed.

Early attempts are preserved, not reported as successes: `trial01` exited 1
because the fixture initially used old port vector names; `trial02` exited 1
after linking because `INCLUDE_xSemaphoreGetMutexHolder` had not been enabled.
Those were fixed in platform/configuration code only. `trial03`, `verified01`,
and final `verified02` each exited 0; the final evidence supersedes earlier
inventories. Compressed failure logs are retained for both failed attempts.

The parent base has no Dune setup. This unit's actual Make/GCC checks pass;
**Dune integration verification remains pending e00/e05**. No Rocq files or
theorems were changed, and running unrelated admitted proof files would provide
no verification of this binary.

## Platform/interrupt contracts still open

The flash range is `[0, 256 KiB)` and RAM is `[0x20000000, 0x20010000)`.
The core vector table is at zero with an initial MSP of `0x20010000`. `.data`
initializers are copied and `.bss` cleared by the separate C `Reset_Handler`.
SVC/PendSV/SysTick vectors reference the real official port handlers. Handler
installation introspection is disabled because architectural Cortex-M0 has no
VTOR; the port's own internal `portARCH_NAME` string says Cortex-M0+, but all
objects are compiled specifically for Cortex-M0, with MPU disabled.

The application provides idle/timer static-memory callbacks and a small worker
that exercises actual static task/queue/mutex/event/stream/timer creation.
Assertion failure disables interrupts and loops. External IRQ vectors, oscillator
setup, peripheral HAL, watchdogs, boot remapping, and physical device memory
capacity are board responsibilities. The configured 12 MHz CPU/SysTick clock
and 1 kHz tick must match a real board before execution. The target was not run
on host, QEMU, or hardware. No board-boot claim is made.

Future contracts must model PRIMASK/IPSR/CONTROL/MSP/PSP, SVC exception entry and
return, NVIC/SCB/SysTick MMIO, interrupt masking/nesting, pending context switches,
callback validity, and concurrent IRQ changes. Ordinary leaf proofs need explicit
interrupt-stability/frame preconditions. Port exception machinery, platform
callbacks, and newlib callees need separate contracts or future proof units.

## Ancestry and follow-on work

Prepared worktree: `/home/charles/.t3/worktrees/Picinae/t3-9e2ec7f4`.
Assigned local branch: `llm-proofs/e04-freertos-build`. It started at exactly
`49956416928e5b6bb3928b54ae33e3b81091f006`, with empty `origin..HEAD` and diff.
The read-only `git ls-remote --heads fork
refs/heads/llm-proofs/e04-freertos-build` check exited 0 with empty output before
the prepared branch was renamed. T3 renamed its initial `t3/9e2ec7f4` branch to
`t3/freertos-cortex-m0-build` while the audit ran; the branch-identity guard
stopped the first rename attempt without mutation, and the correct prepared
branch was rechecked before the successful rename. No fork branch was used as a
base. No prerequisite commits were imported. Only this unit's local commit is
allowed above the pinned base. No push, PR, remote comment, or remote mutation.

`evidence/ancestry-before.txt` records the base/log/stat before commit. The final
post-commit audit, including full SHA and diff stat, is saved in the unit's unique
external evidence directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/e04-freertos-build/`.
Shared campaign plan/status files were not changed.

Next: e05 consumes this exact ELF/layout/symbol inventory after e03 and e00 are
available. Split r40 into its two actual function entries; correct r20's spelling.
The expanded emitted-helper inventory can support later queue/stream/timer call
graph units. Lift/decoder rejection of unsupported instructions remains e03/e05
work; no correctness proving has begun here.
