# e02 ARM inventory — recovered binary; full canonical pipeline partial

This unit recovers the exact Ubuntu ports AArch64 libc and debug package,
inventories its memory/string implementations, verifies six historical lifts'
instruction comments, and runs a restricted real Ghidra → Picinae → Rocq smoke
lift. No functional correctness theorem or port proof was attempted.
The original canonical driver is still incompatible with the available library;
final Dune verification is pending the independent e00-build unit.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

## Provenance and reproduction

Everything downloaded/extracted is under
`/home/charles/code/friends/.toolchains/e02-arm-inventory/`. Shared
`arm-validation/picinae-env` is used read-only. No target executable was run.
Python is a unit venv based on the existing isolated Miniconda Python 3.12.9;
Ghidra, JDK, Java preferences, project, temporary files and Python packages stay
in the unit directory. Nothing was installed on the host.

`artifacts.lock.json` pins exact download URLs and SHA256 for runtime/debug
packages, Ubuntu source archives/descriptor, Ghidra, JDK and CPython 3.12 x86-64
Python wheels. The Ghidra release archive also pins its bundled PyGhidra wheel.
`bootstrap.py` verifies cached files, downloads missing files, extracts packages
without installing them, and installs only pinned wheels into the unit venv.
Its cached-environment replay was actually run successfully; a second empty-root
bootstrap was not performed. System Python's missing ensurepip was bypassed
using the existing isolated Miniconda interpreter, without host installation.

The exact packages are from the [Ubuntu ports glibc pool](https://ports.ubuntu.com/ubuntu-ports/pool/main/g/glibc/):

| Artifact | SHA256 |
|---|---|
| `libc6_2.35-0ubuntu3.15_arm64.deb` | `dd88cc85dcfbac19c0c9b606676b7b1b87f851d75afa5c830fc5ba1293a30833` |
| `libc6-dbg_2.35-0ubuntu3.15_arm64.deb` | `2044236bcf9efd6a19b62099d349b5680eb3f55cd303c6ffac15f4b45e97d745` |
| Extracted `root/lib/aarch64-linux-gnu/libc.so.6` | `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06` |

Package metadata confirms both packages are `arm64`, version
`2.35-0ubuntu3.15`. Runtime and separate debug ELF both contain build ID
`977c021c364ee3c495c0e5f2375bf6ba2124a6da`. The debug file is
`root/usr/lib/debug/.build-id/97/7c021c364ee3c495c0e5f2375bf6ba2124a6da.debug`.
Its SHA256 is in `evidence/inventory.json`. The descriptor's source archive
hashes match the pinned lock; `dpkg-source --no-check -x` applied the Ubuntu
patch series in unit storage. The package signing key was not independently
verified. Patched resolver/source hashes are in `evidence/provenance.json`.

Ghidra is the [official 11.4.2 release](https://github.com/NationalSecurityAgency/ghidra/releases/tag/Ghidra_11.4.2_build),
tag commit `0b61b34bb9c98108eefd9404f45446dae6a1c5eb`, archive SHA256
`795a02076af16257bd6f3f4736c4fc152ce9ff1f95df35cd47e2adc086e037a6`.
The isolated JDK is Temurin `21.0.8+9`; Python packages are PyGhidra 2.2.1,
JPype1 1.6.0 and packaging 25.0. The initially tried JRE was insufficient for
Ghidra; the final reproducible script uses the pinned JDK.

From this worktree root, run:

```sh
/home/charles/miniconda3/bin/python3 Examples/claude/inventory/e02-arm-inventory/bootstrap.py
/home/charles/code/friends/.toolchains/e02-arm-inventory/venv/bin/python Examples/claude/inventory/e02-arm-inventory/inventory.py --toolchain /home/charles/code/friends/.toolchains/e02-arm-inventory --repo "$PWD" --out Examples/claude/inventory/e02-arm-inventory/evidence
bash Examples/claude/inventory/e02-arm-inventory/run-ghidra.sh
bash Examples/claude/inventory/e02-arm-inventory/probe-canonical.sh
bash Examples/claude/inventory/e02-arm-inventory/validate.sh
```

## Inventory and existing lift verification

`evidence/inventory.json` and `memory-string-symbols.tsv` inventory 351 defined
memory/string-related debug symbols, including exact ELF/Ghidra addresses,
types, sizes, byte SHA256 and same-entry symbols. Alias records preserve names;
they do not count aliases as separate implementations. `ports` compares all
existing amd64 lift filename candidates and the assigned ARM target list with
this exact binary and ARM files: 47 have symbols but lack ARM lifts, 6 have
lifts without proof files, 23 have proof files (not audited), and 20 require
variant/name resolution. These counts describe files/symbols, not proven work.
Examples needing lifts include memory/string families, signal TLS helpers,
termios setters, PRNG, search/list and mutex functions. An absent exact amd64
variant spelling is a naming-resolution item, not evidence its ARM equivalent
is absent.

`copy-string-disassembly.txt` contains actual isolated GNU objdump output for
47 selected symbol extents. ELF addresses have no load bias; historical
Ghidra addresses add `0x100000`. The debug symbol extents match every address
and 4-byte instruction slot in the six lifts. Ghidra 11.4.2 then independently
decoded all 85 instruction comments exactly, with instruction bytes recorded
in `ghidra-audit.json`. This also avoids GNU/Ghidra alias spelling differences
such as GNU `bfi` versus historical `bfm` in `div`.

| Lift | ELF entry | Ghidra entry | Bytes | Instructions |
|---|---|---|---:|---:|
| div | `0x3d840` | `0x13d840` | 28 | 7 |
| ldiv | `0x3d860` | `0x13d860` | 16 | 4 |
| ffs | `0x94aa0` | `0x194aa0` | 100 | 25 |
| ffsl | `0x94b10` | `0x194b10` | 72 | 18 |
| ffsll | `0x94b10` | `0x194b10` | 72 | 18 |
| swab | `0x95eb0` | `0x195eb0` | 52 | 13 |

`ffsl`/`ffsll` share the same entry and byte extent. Their duplicate lifts
are not distinct machine implementations. The ffs table is a static-data
dependency for a later proof; instruction verification alone does not prove
its contents or result contract.

## IFUNC bodies, wrappers and shared paths

The binary's actual IFUNC families are `memcpy`, `memmove`, `memset`, `memchr`
and `strlen`. Resolver addresses are respectively `0x94f30`, `0x94810`,
`0x94950`, `0x945f0`, `0x935e0`. They are dispatch code, not copy/string
implementations. Patched Ubuntu `sysdeps/aarch64/multiarch/*.c` and the actual
resolver disassemblies support the following inventory; runtime CPU/tunable
selection was not executed.

| Family | Present bodies (ELF entries) |
|---|---|
| memcpy | `__memcpy_generic` `0x9ab40`; `__memcpy_simd` `0x9adc0`; `__memcpy_thunderx` `0x9b000`; `__memcpy_thunderx2` `0x9b2c0`; `__memcpy_falkor` `0x9b9c0`; `__memcpy_a64fx` `0x9bc40` |
| memmove | `__memmove_generic` `0x9acd0`; `__memmove_simd` `0x9af00`; `__memmove_thunderx` `0x9afc0`; `__memmove_thunderx2` `0x9b280`; `__memmove_falkor` `0x9bb40`; `__memmove_a64fx` `0x9be70` |
| memset | `__memset_generic` `0x9bfc0`; `__memset_falkor` `0x9c1c0`; `__memset_emag` `0x9c300`; `__memset_kunpeng` `0x9c400`; `__memset_a64fx` `0x9c500` |
| memchr | `__memchr_generic` `0x9c6c0`; `__memchr_nosimd` `0x9c7c0` |
| strlen | `__strlen_mte` `0x9c8c0`; `__strlen_asimd` `0x9c940` |

Copy/move dispatch prioritizes ThunderX, Falkor/Phecda, ThunderX2/ThunderX2PA,
Neoverse N1/N2/V1 (SIMD), A64FX with SVE, then generic. Memset chooses
Kunpeng920, Falkor/Phecda with 64-byte ZVA, eMAG with 64-byte ZVA, A64FX/SVE,
then generic. Memchr selects nosimd for eMAG, otherwise generic. Strlen selects
MTE versus ASIMD. The source implementation-enumeration helper has additional
availability conditions (e.g. ThunderX2 `!bti`), which should not be confused
with the resolver's selection order.

`mempcpy`/`__mempcpy` are aliases at `0x94a50` (36 bytes), not IFUNCs: they
call `__memcpy_generic` and add length to the returned pointer. Checked
wrappers are `__memcpy_chk` `0xf7b30`, `__memmove_chk` `0xf7b50`,
`__mempcpy_chk` `0xf7b70`, `__memset_chk` `0xf7ba0`. Their success paths
target the generic implementations directly; failure calls `__chk_fail`
`0xf8440`. Do not invent architecture variants of these wrappers.

Every copy-family memmove entry has direct branches into its corresponding
memcpy extent. The small ThunderX/ThunderX2 symbol sizes especially must not
be interpreted as complete independent bodies. `external-direct-edges.json`
records 27 out-of-extent direct branch/call edges across the selected ranges,
with exact target entries or containing extents. This is evidence for shared
entry adapters and closed lift boundaries, not a complete CFG analysis.
`memcmp`, `strcpy`, `strcmp`, `strchr`, `strspn`, `strcspn` and the other hot
string symbols in the manifest are ordinary functions, not extra inferred
IFUNC families.

## Driver compatibility and blockers

The historical driver names upstream pcode2coq `b7f0122`, only an abbreviated
revision. The README explicitly says the actual `claude/amd64-fixes` checkout
had uncommitted modifications. The old `git-softseclab.utdallas.edu` hostname
did not resolve even with network access; no full modified revision or patch
archive is available here. Neither Desktop checkout nor old Flatpak projects
were assumed or used. The pinned in-repository library was introduced by
`8f83c87501dbd6f183ecefe991abc8639e0671a4`; its Git blob IDs and SHA256 are
saved in `provenance.json`.

Actual `probe-canonical.sh` result: the unchanged historical driver logs
`FAILED toascii: 'LiftInfo' object has no attribute 'prependProgName'`, writes
no lift, and exits **0** at the launcher. The probe asserts the diagnostic and
missing output. Source inspection also finds no implementation of
`canonicalTemps` or `staticMemory=False`, a dictionary `typctx` versus the
multi-function driver's string expectation, and legacy `LZCOUNT`/boolean
handling. Therefore this library is not accepted as a drop-in replacement.
No existing lift or shared lifter was changed.

`ghidra_audit.py` uses a documented, hash-guarded **restricted smoke adapter**:
only `and w0,w0,#0x7f; ret` from the pinned binary is accepted. It calls the
repository `proc_insn` under `strictFailure=True`, resets unique varnode IDs
per instruction in first-use order, and emits only a typing theorem. The
generated `e02_toascii_smoke.v` contains canonical temporary 0. Unknown
instruction shapes fail. The script imports a fresh exact binary into a unit
project without autoanalysis, rebases to `0x100000`, and checks fresh output
artifacts because launcher exit alone is insufficient. This validates a small
real path through the tooling, not general restoration of canonical lifting.

TLS instructions are confirmed in this binary: `sigaddset` ELF `0x3b2f4`,
`sigdelset` `0x3b354`, `sigismember` `0x3b388` read `TPIDR_EL0` for errno paths.
That state is absent from `Picinae_armv8`; e09 must model it explicitly.
NEON/AdvSIMD string operations still require strict opcode coverage and later
instruction lemmas. The smoke lift tests neither. A64FX additionally uses SVE
predicates and scalable vector operations; the current fixed-width register
model is insufficient. Memset uses `dc zva` and system-register-dependent
block sizes. MTE, SVE, ZVA and BTI need separate coverage/specification work;
none may silently become an empty instruction.

ABI differences must remain explicit when porting: AAPCS64 integer arguments
are X0–X7, LR is X30, SP is 16-byte aligned at public interfaces, and W writes
zero-extend into X registers. LP64 uses 32-bit int and 64-bit long/pointers;
32-bit ARM7 contracts cannot be copied. `div_t` returns two packed 32-bit
fields in X0 in this binary, while `ldiv_t` uses X0/X1; x86 return-register
specifications differ. Long double follows `ieee754/ldbl-128` in AArch64's
source `Implies`, unlike amd64's extended precision. Floating arguments use
the SIMD/FP registers. Data references keep absolute Ghidra addresses while
relative code addresses are rebased; calls/shared interior entries need a
closed, globally addressed lift. Later termios/signal/list ports must confirm
their exact source layouts and frame conditions rather than reuse amd64 or
ARM7 offsets by assumption.

## Validation and handoff

All five reproduction commands above ran and exited 0 in this environment.
`evidence/validation-commands.log` records every actual bounded Make/Rocq
command, exit and log. Core: `rocq makefile -f _CoqProject -o Makefile.coq`,
`make -f Makefile.coq -j1 -B Picinae_armv8.vo` (forced rebuild). Existing lifts: sequential
`rocq c -R . Picinae Examples/claude/<fn>_arm8.v`. Smoke: the same compiler
against `evidence/e02_toascii_smoke.v`. Memory cap: `ulimit -v 8000000`.
`versions.log` records Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2, GNU objdump 2.42.
No Dune files are present at the pinned base; Dune verification is pending e00.

Binary inventory assumptions: N/A. No new semantic theorem. The smoke typing
theorem and all six historical typing theorems were checked with `Qed` and
`Print Assumptions`; verbatim output is in `smoke-typecheck-assumptions.log`
and `existing-assumptions.log`. Each reports the existing core dependency:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This dependency comes from the existing Picinae/Stdlib functional-extensionality
imports, not a new declaration in this unit. Typing and matching disassembly
do not establish functional correctness or lifter soundness.

Suggested follow-ons: recover/version the historical modified lifter or review
an explicit replacement in a separate engineering unit before e08's general
lifts; use this inventory to split one unit per actual implementation/shared
body; add SVE/ZVA/MTE engineering coverage beyond the planned NEON and TLS
units. The six existing leaf lifts are available to later proof units once
e00 is validated. Do not infer a proof dependency on unavailable new lifts.

Branch: `llm-proofs/e02-arm-inventory`. Worktree:
`/home/charles/.t3/worktrees/Picinae/t3-0672c15b`. Parent and merge-base are
`49956416928e5b6bb3928b54ae33e3b81091f006`; no prerequisite commits were
imported. The required read-only fork-name collision check succeeded with
empty output before the prepared local branch was renamed. No fork branch
was used as base and no push, PR, remote mutation or shared plan/status edit
was performed. Before/after audits accompany the handoff; final local commit
SHA is returned separately to avoid a self-referential commit hash in this file.
