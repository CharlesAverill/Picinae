# e28: Guarded AMD64 bit-scan lowering

Completed bounded engineering subset, local-only. Branch
`llm-proofs/e28-x86-bitscan-lowering`; worktree
`/home/charles/.t3/worktrees/Picinae/t3-09baf102`.
Actual assigned model: gpt-6.1-sol, xhigh, default. No agents were started.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

Nothing was installed. Shared Ghidra/JDK/PyGhidra and Rocq environments were
reused read-only. Every project, Java home/config/cache/temp/log, assembler object,
replay destination, Dune build and assumptions query object is under
`/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering/`.
Java uses `-Xmx1G`. All Dune/Rocq/assumptions processes use `ulimit -v 2000000`,
`ulimit -s 65536`; Dune uses `--cache=disabled -j1`. The cap was never raised.

## Exact scope and model boundaries

The separate e25 AMD64 backend now dispatches BSF, BSR, TZCNT and LZCNT to
`pcode2coq_bitscan.py`. Only exact register-source 32/64-bit encodings are
accepted. Operand-size 66, memory-source, LOCK/segment/address-size prefixes,
extra/reordered/duplicate prefixes, unexpected opcodes and unknown pcode graphs
reject. Generic backward pcode branches still reject. REX.W/R/B and ModRM select
exact widths and GPRs independently of the raw graph. The complete graph must
match: every varnode/width/constant, initialization, test, defined flag write,
relative edge and exit, destination and 32-bit zero extension. Unique addresses
may change without changing canonical first-use identities; overlap rejects.
No generic loop truncation or instruction Nop substitution was added.

One common scan kit snapshots the source, initializes a cursor and count, and
uses `Rep width (If (... count < width ... cursor bit is zero ...) ... Nop)`.
Trailing scans shift right; leading scans shift left. The bound is 32 or 64,
with no possible machine branch from this instruction kit. BSR converts the
leading-zero count into position `width - 1 - count`. Source/destination aliasing
cannot destroy the original input used by CF. Defined 32-bit results zero-extend
into the canonical 64-bit GPR; 64-bit results replace the full register.

- BSF/BSR: ZF means original source is zero. For zero input the **full canonical
  destination is Unknown 64**, deliberately conservative, including its upper
  half. Do not infer a defined destination, preserved old value or zeroed upper
  half from this case. This discards Ghidra's deterministic zero/width-minus-one
  assignment. CF/OF/SF/AF/PF are Unknown 1. DF and unrelated state are preserved.
- TZCNT with `--bmi1 present`: zero input returns width; CF means zero input;
  ZF means zero count. `--bmi1 absent` explicitly lowers the F3 alias as BSF,
  including undefined-zero destination/flag boundaries.
- LZCNT with `--abm present`: zero input returns width; CF means zero input;
  ZF means zero count. `--abm absent` explicitly lowers the alias as BSR.
  The option denotes CPUID.80000001H:ECX[5], called LZCNT/ABM, independently of
  BMI1. OF/SF/AF/PF are Unknown 1 in both count instructions.
- Unspecified required features reject. These options are **caller-declared
  execution assumptions**, not host CPUID detection or a verified IFUNC choice.
  No unconditional mnemonic semantics are claimed. CET-enabled execution,
  instruction faults/timing/concurrency and full SIMD/REP/string functions remain
  outside this subset. Real glibc ffs extraction requires `--cet-disabled`;
  e25's exact ENDBR64 and disabled IBT/shadow-stack requirement is preserved.

Pinned Ghidra LZCNT assigns DST before calculating CF from SRC. Its raw graph is
retained verbatim, but literal replay would calculate the wrong CF for aliased
operands (e.g. nonzero high-bit input gives count zero then CF=1). The guarded
replacement computes CF from the snapshot. This is an explicit lifting repair,
not a theorem asserting equivalence to that erroneous raw determinization.

## Provenance and evidence

Before implementation, `inspect.sh` read actual pinned e01 bytes and fresh
Ghidra raw pcode. `pinned-raw.json` contains 28 distinct hot-string encodings
and the real ffs/ffsl/ffsll instructions; `scan-inventory.json` maps representatives
back to named inventory extents. The inventory contains 691 scan sites, including
BSR, and no LZCNT sites. LZCNT support is tested using explicitly synthetic
32/64-bit fixtures, never passed off as observed glibc LZCNT code.

Runtime: Ubuntu amd64 glibc **2.35-0ubuntu3.12**, ELF SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`; debug SHA256
`10e200b6bb67e1697e1c924d7fe65f55d358e9e049c6bf9ec1e0151e5e25f450`.
Real ffs entry: `0x1a9910`, 19 bytes, six instructions; ffsl/ffsll alias entry:
`0x1a9930`, 21 bytes, six instructions. All addresses include image base 0x100000.
No host libc was used. The synthetic ET_DYN fixture is reproducibly assembled
with existing as/ld, SHA256
`4e44c4c19f2432684f42dd2737e6198be20647ffa0775fda02f97eea9af45481`.
`fixture-raw.json` includes the rejected 16-bit/memory cases as raw evidence.

The supervisor verifies the full reviewed e01 target manifest, e02 dependency
archives and e25 x86 decoder/language pins. Receipts bind source, feature/CET
profile, scope, requested symbols, output set, raw-pcode and IL hashes, and
implementation hashes including the new scan helper. Fresh nonce and atomic
directory publication remain mandatory even if Ghidra swallows an exception.
The hot-scans artifact is explicitly an **instruction sample map with open
fallthroughs**, not a closed function lift. Its receipt lists each sampled extent.
The real ffs family and synthetic function maps retain the e25 closure checks.

The 24 new typing targets are: three ffs-family modules, one hot-scans kit,
16 synthetic forms (four scans, two widths, aliased/distinct extended GPRs),
and four feature-absent alias forms. They contain engineering `welltyped` facts
only. No function proof or instruction semantic lemma was begun.

## Actual verification

All commands below ran from the worktree root. Exact arguments, stdout/stderr
and real exits are saved in `logs/`; raw launcher/application output is retained
byte-for-byte as gzip under `logs/ghidra/`. All listed final checks exited **0**.
Expected rejected extraction commands exited 1, existing/symlink outputs exited 2.

```sh
bash notes/e28-x86-bitscan-lowering/fixture/build.sh --check
bash notes/e28-x86-bitscan-lowering/reproduce.sh --check
bash notes/e28-x86-bitscan-lowering/check-e25-replay.sh
PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_bitscan.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_bitscan_publication.py
PYTHONDONTWRITEBYTECODE=1 python3 notes/e28-x86-bitscan-lowering/check-failures.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_x64.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_scalar.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_x64_publication.py
PYTHONDONTWRITEBYTECODE=1 python3 notes/e28-x86-bitscan-lowering/check-artifacts.py
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000; export TMPDIR=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering/tmp; dune build --build-dir=/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering/dune --cache=disabled -j1 --display short @x64-bitscan-lifter @x64-scalar-lifter'
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash notes/e28-x86-bitscan-lowering/print-assumptions.sh
python3 tools/audit-proof-source.py --base 328088263ebba11786a03448808e584231504fe1 \
  Examples/claude/lifter/x64_bitscan_fallback Examples/claude/lifter/x64_bitscan_fixture \
  Examples/claude/lifter/x64_bitscan_glibc Examples/claude/lifter/x64_bitscan_hot
PYTHONDONTWRITEBYTECODE=1 python3 notes/e28-x86-bitscan-lowering/check-ancestry.py
```

- Full `.vo` Dune build: `06-dune.log`, all 24 new and seven preserved e25 modules.
- Assumptions: `11-assumptions.log`, **31/31** explicit transitive queries report
  only the inherited typing/program-equality dependency shown verbatim below.
- Scan finite tests: `08-finite-tests.log`, five tests, **17,832** finite
  input/profile/havoc checks including zero/all bits/every single bit/random
  values, both widths, aliased and distinct GPRs, high32 clearing, both feature
  outcomes and all defined flags. **2,136** mutated-node/constant checks, plus
  deletion of every raw operation, changed opcodes, appended suffixes,
  prefix/encoding mismatch, unknown loops and invalid feature declarations.
  Real ffs-family execution samples include zero under several arbitrary
  destination/undefined-flag choices. This finite interpreter evidence is not
  a proof, native CPU execution, or exhaustive nondeterministic exploration.
- Publication: `07-publication-tests.log` and `09-negatives.log`; six actual
  failed Ghidra batches include mixed supported+unsupported selections and
  leave no published directory or staging files. Missing/stale/wrong profile,
  wrong scope/hash/set, partial receipts and existing/broken-symlink outputs reject.
- Fresh generation/replay: `12-final-generation.log`, `13-deterministic-replay.log`.
  All output bytes including receipts reproduce. `14-e25-replay.log` confirms
  all seven existing IL/raw-pcode pairs are unchanged (only implementation
  receipt hashes necessarily differ).
- Existing backend/parser/publication regressions: logs 10, 15, 18, all pass.
- Source/artifact audits: logs 19/20. Zero new/current forbidden declarations
  in the 24 files; exact bytes, debug extents, pins and protected source checks pass.
- Earlier failures are retained: log05 contains a negative-test filter mistake
  that included RET, fixed in log08; log16 omitted the audit tool's required
  `--base`, corrected in log19. Neither was accepted as successful verification.

Raw assumptions output, repeated for each of the 31 facts:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

## Ancestry and handoff

Initial prepared HEAD was clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`. The required pre-rename
`git ls-remote --heads fork refs/heads/llm-proofs/e28-x86-bitscan-lowering`
returned exit0/empty after a sandbox DNS failure and read-only network retry.
Only the new prepared branch was renamed; Git metadata writes required a sandbox
escalation because the prepared worktree's administrative directory is outside
its writable root. The exact authorized `git merge --ff-only
328088263ebba11786a03448808e584231504fe1` succeeded. No fork branch was imported.
`allowed-prerequisites.txt` records the exact seven base..checkpoint commits.
The imported set includes only reviewed e00/e01/e02/e11/e25 history and their
explicit prerequisite-import commits. `check-ancestry.py` requires this exact
set plus only linear e28 commits with explicit unit subjects. The merge base
remains `49956416928e5b6bb3928b54ae33e3b81091f006`; timing
`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` and active e26/e27 branches were not
imported. Before/after merge-base, complete log and diff-stat evidence is retained.

No blockers remain for this bounded register kit. Follow-on semantic proof work
must establish scan/count/flag/frame lemmas under these explicit undefined-state
and feature boundaries. e07 still needs its vector/REP/string-operation units,
actual IFUNC/CPU-feature obligations and whole-function extraction/proofs.
Memory-source/16-bit scans require a separate tested extension if encountered.
No implicit correctness claim follows from typechecking or finite fixtures.

No shared plan/status edits, host installs, shared environment changes, other
branch changes, pushes, PRs, remote comments or remote mutations occurred.
Publication of this unit still requires Charles approval; future direction is
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.

Primary instruction references: [Intel SDM Volume 2B](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf)
(TZCNT flags, zero case and BMI1/BSF fallback),
[Intel SDM Volume 1](https://www.intel.com/content/dam/develop/external/us/en/documents-tps/253665-sdm-vol-11.pdf)
(register writes and CPUID bits), and pinned Ghidra `ia.sinc`, `bmi1.sinc`,
`lzcnt.sinc` (exact graphs). Charles's required undefined BSF/BSR zero-destination
boundary is retained conservatively, regardless of particular CPU determinization.
