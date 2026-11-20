# e25: Strict AMD64 scalar driver

This unit supplies a separate x86-64 raw-pcode backend, supervised extraction,
and full Rocq typing facts for **exact pinned glibc** `toascii`, `isascii`, `abs`,
`labs`, `pthread_equal`, plus an explicitly synthetic CALL/RET fixture. These are
engineering artifacts and regression checks. There is no new glibc functional
correctness theorem and no claim that typing proves lifting soundness.

Branch: `llm-proofs/e25-x86-scalar-driver`. Worktree:
`/home/charles/.t3/worktrees/Picinae/t3-83d5497b`.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No packages were installed. The e02 Ghidra 11.4.2/JDK 21.0.8+9/PyGhidra venv and
existing Rocq wrapper are read-only dependencies. Mutable Ghidra home, config,
cache, logs, temporary files, projects, output, lock and assembler object/link
state live in `.toolchains/e25-x86-scalar-driver`. JVM heap is `-Xmx1G`, with no
small JVM virtual-address cap. All compiler phases use `ulimit -v 2000000`,
`ulimit -s 65536`, `PROOF_MEMORY_KB=2000000`, Dune `--cache=disabled -j1`.

## Provenance and supported boundary

Runtime is e01's Ubuntu amd64 glibc **2.35-0ubuntu3.12**, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`. Debug SHA256 is
`10e200b6bb67e1697e1c924d7fe65f55d358e9e049c6bf9ec1e0151e5e25f450`.
No host libc is used. The supervisor checks the entire reviewed e01 target
manifest and e02 archive pins before launching. `isa-pins.json` additionally
pins the installed compiled x86-64 SLEIGH decoder and language/spec files.
`check-artifacts.py` reads the actual e01 source files, verifies six selected
files byte-for-byte against the pinned glibc source archive, and checks exact
debug symbol extents, every instruction byte, all artifact hashes and decoder
pins. Outputs: `logs/16-artifact-source-audit.log` and final
`logs/26-artifact-complete.log`, both exit 0.

| Exact symbol | Global entry (ELF + 0x100000) | Bytes | Instructions |
| --- | --- | --- | --- |
| toascii | 0x13a170 | 10 | 4 |
| isascii | 0x13a180 | 13 | 5 |
| abs | 0x145dd0 | 12 | 5 |
| labs | 0x145de0 | 15 | 5 |
| pthread_equal | 0x195c70 | 13 | 5 |

Each selected symbol gets a module; its global program contains the union of
the selected exact extents. Direct machine branches, call destinations and
fallthrough/return sites must be selected instruction boundaries. RET obtains
its external return address from memory, rather than inventing a callee contract.
Calls accept only the verified direct near E8/rel32 shape: subtract 8 from RSP,
store the actual global next instruction address, then jump to the selected
callee. CALL-to-next special Ghidra BRANCH shapes, indirect calls/jumps, far calls,
RET-immediate, unresolved callees and unclosed fallthroughs reject.

All five pinned public functions start with `ENDBR64`. Default extraction rejects
it. The explicit `--cet-disabled` profile admits only exact bytes `f3 0f 1e fa`
with empty raw pcode as Nop, under **IBT and shadow-stack disabled** execution.
This restriction is in CLI help, receipt metadata and every generated module.
The ELF's IBT/SHSTK capability notes do not establish that execution disables CET;
that is an explicit model boundary, not a verified property of an environment.
No CET-enabled extraction/proof is supplied. Other CET/RTM/hint/system forms fail.

The backend handles 64-bit GPRs, zero-extending r32 writes, merging r16/low8/high8
writes, exact varnode widths, one-bit architectural flags through byte-sized
pcode, BOOL_NEGATE as xor1, carry/signed overflow, popcount/parity, and 64-bit
global/RIP-relative memory. Raw SLEIGH omits defined AF for ADD/SUB/CMP/NEG; this
backend derives bit4 of `a xor b xor (a +/- b)` before operands change. AF after
logical operations is architecturally undefined; the IL retains an arbitrary
previous AF value. No exact undefined-flag, fault, timing or concurrency claim
is made. This uses the existing sequential Picinae AMD64 state.

The explicit mnemonic allowlist and independent per-op/register/width checks
both apply. Architecture-independent pcode names do not establish instruction
support. Unsupported SIMD/vector aliases, userops, REP, BSF/TZCNT/LZCOUNT,
LOCK/segment/address-size prefixes, invalid slices, overlapping unique storage,
unknown opcodes/registers and backward/out-of-region internal branches reject.
Instruction-local temporaries are canonicalized by first use, checked for
initialization along every surviving path, and reset each instruction. Forward
internal pcode skips and machine-address conditional suffixes (actual CMOV)
are distinct. No decoder/library partial-merge or LZCOUNT shortcut is copied.

The synthetic `fixture/scalar.S` is assembled using existing GNU binutils 2.42
into a pinned ET_DYN ELF. Its caller/callee have actual direct CALL/RET, AH/AX/EAX
writes, ADD AL/SUB AX, memory loads/stores, RIP-relative data, CMP/JE and NEG.
It is never presented as glibc code. Fixture SHA256:
`fbc4ef542d199d81f98f0c1a19ff339694a6a6ac0ef509653d12d75bec5f7576`.

## Publication and validation

`tools/ghidra-lifter/lift-x64.py` launches one fresh project at a time, with a
nonblocking state lock and a fresh nonce. It requires the exact requested symbol
list, source/profile/language/addressing receipt, exact output names/set and
hashes of both `.v` and raw/structured `.pcode.json`. Only a completely validated
directory is atomically published. Existing destinations (including broken
symlinks) reject. Failure removes staging and projects. Launcher exit 0 alone
never counts as success. Actual swallowed exceptions and their launcher exits
are retained byte-for-byte as gzip files in `logs/ghidra/` (raw `.log` files
also remain in the assigned isolated state directory).

Reproduce from the repository root (commands and actual exits are in logs):

```sh
bash notes/e25-x86-scalar-driver/fixture/build.sh
bash notes/e25-x86-scalar-driver/reproduce.sh --check
python3 tools/ghidra-lifter/test_x64.py
python3 tools/ghidra-lifter/test_x64_publication.py
python3 notes/e25-x86-scalar-driver/check-failures.py
python3 notes/e25-x86-scalar-driver/check-artifacts.py
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000; dune build --cache=disabled -j1 --display short @x64-scalar-lifter'
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash notes/e25-x86-scalar-driver/print-assumptions.sh
```

`reproduce.sh --check` compares every fresh output byte (including receipts and
implementation/decoder hashes); `--update` explicitly refreshes unit fixtures.

- Full Dune `@x64-scalar-lifter`: exits 0, `logs/07-dune.log` (initial complete
  seven-module kernel build), `logs/11-dune-final.log` (final arithmetic fixture).
- All seven explicit Print Assumptions queries: exit 0,
  `logs/12-assumptions.log`. Each reports exactly the inherited
  `FunctionalExtensionality.functional_extensionality_dep`, with its full type
  saved verbatim. It is inherited via Picinae's typing tactic/program equality;
  no new assumptions were introduced. There is no function-correctness theorem.
- Backend tests: `logs/10-backend-final.log`, exit 0, 12 tests including exhaustive
  65,536 byte pairs for each of carry/signed addition overflow/signed subtraction
  overflow, full-width randomized pairs, partial writes, actual glibc arithmetic
  oracles (including integer-min machine results), 64-bit stack/data addressing,
  actual arithmetic flags and strict invalid input checks. Final recheck `logs/25-backend-complete.log` exits 0 and includes
  initialized RIP-relative data and both outcomes of actual JE.
- Publication adversarial receipt checks: `logs/09-publication-tests.log`, exit 0;
  missing/stale/incomplete receipt, wrong output names/hashes/profile/source,
  missing pcode and unexpected partial files all reject.
- Real negative matrix: seven Ghidra batches exit 1 as expected; existing
  destination and broken symlink exit 2; unknown userop/register and malformed
  branch subprocesses exit 1. Harness exit 0: `logs/21-final-negatives.log`.
  Includes missing-only, mixed supported+missing, default ENDBR rejection,
  mixed supported+SIMD, indirect call, REP, and missing call closure. No partial
  artifact is published even when the launcher swallows the exception (exit 0).
- Final fresh-project deterministic generation/replay: exits 0,
  `logs/19-final-regeneration.log`, `logs/20-final-replay.log`.
- Fixture rebuild/cmp: exit 0, `logs/15-fixture-rebuild.log`.
- Source audit: `logs/22-proof-source-audit.log`, exit 0, zero new or current
  forbidden assumption/admission declarations in all seven new `.v` files.
  Existing programs/proofs/ARM driver and core AMD64 state remain unchanged;
  root Dune has only the seven additive module entries and one new alias.

Earlier failed attempts are retained honestly in logs 01/02/06: default ENDBR
rejection, discovery of the CMOV suffix shape, and a corrected test setup error.

## Local ancestry and handoff

Prepared HEAD was reviewed e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The exact fork branch collision check succeeded with empty stdout before local
rename (after a sandbox DNS failure; read-only network retry exited 0). It was
saved again in `logs/18-fork-collision.log`. The newly prepared branch alone was
renamed; no fork branch was used as a base. HEAD was fast-forwarded to reviewed
e11 `378fe1b57514b9af3f017a72b4ca665910156cc7`, then reviewed e01
`131ad4b86cf4abcbd392048297038f3f219423bb` was imported by the explicit local
merge `Import reviewed x86 inventory prerequisite`. e11 contains e02 provenance
`081d023` and its explicit import. Only these prerequisite commits and e25's
local merge/implementation are above origin base
`49956416928e5b6bb3928b54ae33e3b81091f006`; timing
`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` was not imported. Before/imported/final
merge-base, log and diff-stat evidence is in this directory.

No remaining blocker for this bounded scalar subset. e26 should add actual
SSE/AVX forms with explicit alias/upper-lane semantics; e27 REP and e28 bit scans
must remain separate. e16/full CET/fault/timing work is required for CET-enabled
claims. e06/e07 still need their listed SIMD/REP/scan prerequisites; these five
smokes do not unlock arbitrary copy/string extraction. No new function proofs
were begun. There was no push, PR, remote comment/mutation, shared plan/status
edit, worktree creation, host install or shared environment mutation. Future PR
publication requires Charles approval and the assigned fork-to-origin direction.

## Primary instruction/pcode references

- [Intel SDM Volume 1, section 3.4.1.1](https://www.intel.com/content/dam/develop/external/us/en/documents-tps/253665-sdm-vol-11.pdf):
  r32 zero-extension and partial-register behavior.
- [Intel SDM Volume 2A](https://cdrdv2-public.intel.com/812383/253666-sdm-vol-2a.pdf)
  and [combined SDM](https://cdrdv2-public.intel.com/868137/325462-089-sdm-vol-1-2abcd-3abcd-4.pdf):
  ADD/SUB/NEG flags, CMOV, near CALL/RET stack behavior, and ENDBR64's disabled-IBT
  no-op boundary. CET-enabled state/side effects are outside this profile.
- [Ghidra pcode operation reference](https://ghidra.re/ghidra_docs/languages/html/pcodedescription.html):
  byte booleans, BOOL_NEGATE, carry/overflow, memory-space/varnode sizes,
  machine-address versus relative pcode branches, and CALL as the final branch
  only. The surrounding raw pcode supplies the actual stack push.
- Pinned Ghidra `ia.sinc`: explicit comments that AF is unimplemented; the local
  backend corrects defined AF for its supported arithmetic profile. Compiled
  decoder and source-file hashes are retained in `isa-pins.json` and receipts.
