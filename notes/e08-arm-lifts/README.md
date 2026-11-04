# e08 ARM scalar extraction baseline

This unit adds generated missing-port artifacts and a naming/closure/coverage
harness around the unchanged e11 strict AArch64 scalar replacement. This is
engineering validation of generated IL and typing. No function correctness,
termination, binary-to-IL soundness, or equivalence to historical lifts is proved.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

## Provenance and scope

Branch `llm-proofs/e08-arm-lifts`, prepared worktree
`/home/charles/.t3/worktrees/Picinae/t3-746dec47`.
The assigned campaign plan and e08 row were read before implementation.
Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The exact fork branch-name check returned exit 0 with empty output before the
prepared local branch was renamed. The initial sandboxed read-only network
check could not resolve GitHub; the escalated read-only check succeeded.
Git metadata outside the writable worktree required escalation for the local
rename/fast-forward. No remote write, push, PR, comment, branch deletion,
worktree creation, or shared campaign plan/status edit occurred.

The local branch fast-forwarded to reviewed e11
`378fe1b57514b9af3f017a72b4ca665910156cc7`.
The only allowed prerequisite history above pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006` is:

- e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`;
- partial e02 artifact gate `081d0233cd6667803b3907343b2fea6dc9eba714`;
- e11's import merge `052521a753adbda077843ec7b259801282a7b1e9` and implementation `378fe1b`.

No fork branch was used as a base or imported. Timing
`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` is context only, not ancestry.
Logs 00/01 preserve prepared/imported merge-base, logs, and diff statistics.
The final full-SHA audit and after-stat are exported to this unit's unique
external evidence directory after commit. The original broad e02 remains
partial; this unit consumes its accepted pinned-binary artifact gate only.

All exact binaries, debug symbols, Ubuntu source, Ghidra 11.4.2, Temurin JDK
21.0.8+9 and Python venv are reused READ-ONLY from
`/home/charles/code/friends/.toolchains/e02-arm-inventory`.
Every driver invocation verifies the complete existing archive lock plus the
runtime/debug hashes. No dependencies were installed and no shared environment
was changed. All mutable projects, home/config/cache/logs/output are private
under `/home/charles/code/friends/.toolchains/e08-arm-lifts`; Java uses
`-Xmx1G` and the driver lock enforces one invocation at a time.

- Ubuntu ARM64 glibc 2.35-0ubuntu3.15 runtime SHA256:
  `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
- Debug ELF SHA256:
  `c95b2118b5ea5ed12db5c745fb95af4dd696ce07d3ce966a60124519a443e9e7`.
- Build ID `977c021c364ee3c495c0e5f2375bf6ba2124a6da`.
- ELF address + `0x100000` = Ghidra/model address throughout.
- Shared read-only Rocq wrapper verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2
  (log 02). Every Dune/Rocq invocation uses virtual memory 2,000,000 KiB,
  stack 65,536 KiB, `PROOF_MEMORY_KB=2000000`, and Dune `-j1 --cache=disabled`.

## Generated naming and closure

`extract.py` invokes `tools/ghidra-lifter/lift-scalar.py` with explicit
`--state`, `--global-addressing`, and new output directories. It preserves
all e11 archive checking, nonce receipt validation, atomic publication,
failure diagnostics, and stale-output refusal. Unsupported decoder/pcode gates
are unchanged. Failed symbol groups contribute diagnostics, never published
programs. The e08 output directory is itself published by atomic rename only
after collecting supported groups. An empty set cannot publish success.

The sole program adaptation replaces exactly two occurrences of its generated
identifier, `e11_<symbol>_arm8` -> `e08_<symbol>_arm8`. It does not rewrite any
machine statement, instruction boundary, address, or theorem body. Every
manifest retains the original hash and naming operation; `check-artifacts.py`
reverses it and verifies the original hash. New files live in
`Examples/claude/lifter/scalar_ports/`. Historical programs, div/ldiv/ffsl
proofs, all e11 fixtures, and all lifting implementation files are unchanged.
Only explicit new modules and the `@e08-arm-lifts` alias are added to Dune.

Adjacent JSON files retain every instruction's exact runtime bytes, Ghidra
assembly, and raw pcode. Each function manifest identifies its entry, aliases
at the same exact extent, selected symbol extents, instruction/implementation
hashes, complete direct/fallthrough edges, CALL continuation sites, and RETURN
sites. The e08 checker additionally rejects indirect nonreturn transfers and
fallthrough beyond the map. RETURN remains the actual caller ABI boundary;
finite-map closure does not establish well-bracketed return behavior, a memory
frame, or total correctness.

## Memory requirements

`staticMemory=False` remains unchanged. Programs do not initialize global data
or invent hypotheses. All raw memory-access instructions are listed per map.
ADR/ADRP+ADD references are matched to actual debug OBJECT extents and record
file bytes/hashes or ELF zero-fill. This conservative address scan is manually
reviewed for the accepted maps; it is not a verified general dataflow analysis.

- Copy maps use actual argument buffers and stack where their wrapper requires
  it. Size thresholds are immediate instruction operands; no threshold global
  or fake constant is supplied.
- `a64l_table`: 77 actual bytes at ELF `0x1494c8`, model `0x2494c8`, recorded
  verbatim in the manifest. The source is `stdlib/a64l.c` in the exact patched
  Ubuntu source tree. A future proof must state real initial-memory contents.
- `seed48`/`seed48_r`: mutable 24-byte `__libc_drand48_data` at ELF `0x1a34d8`,
  model `0x2a34d8`; `__old_x` starts at +6. ELF zero-fill describes loading,
  not a permanent all-zero runtime assumption. Argument and stack memory remain
  real input requirements.
- Signal-description lookup tables are pointer-bearing memory. Manifests keep
  actual table bytes, each ELF relocation, required rebased pointer for
  R_AARCH64_RELATIVE, and pointed bytes through the first NUL. They do not
  substitute unrelocated ELF bytes for a loaded pointer table. Remaining
  loader symbol bindings, if any, remain explicit requirements.
- Existing e11 `ffs` (not regenerated under an old theorem name) reads the
  256-byte `table.0` at ELF `0x14e738`, model `0x24e738`, SHA256
  `14a5d850c255623f9472e3c650abce0c78d32f0276b315b3a276a0462d97a1ac`.
  `ffs-reference-data.json` records those actual bytes and accesses for future
  proof work. This is reference data, not a new ffs proof or assumed axiom.

## Validation and handoff

The supported baseline has **15 artifacts** from 13 successful explicit symbol
scope invocations. Across the initial complete inventory scan and expanded
memmove closure there were 66 driver invocations: 13 exit 0 and 53 strict exit 1.
The 53 failed scopes include the standalone generic memmove scope, subsequently
resolved by selecting its actual shared memcpy extent. They are scope diagnostics,
not a claim that 53 distinct final functions are unsupported.

All 96 exact e02 port rows are accounted for: 29 historical lifts preserved,
20 exact names absent, four IFUNC resolver entries explicitly distinguished
from implementations, ten newly generated port targets, and 33 strict-rejected
missing port targets. Five additional exact helper/implementation targets bring
the artifact count to 15. `COVERAGE.json` retains all attempted selections and
first rejection reasons; `HASHES.json` covers every published file except itself.
Versioned names for pthread_mutex_lock/unlock are recorded as exact resolutions,
not invented spellings or silently accepted aliases. No x86 variant name is
invented for ARM.

| Actual symbol | ELF entry | Extent bytes | Instructions in published closed map |
|---|---|---|---|

| `__drand48_iterate` | `0x3e7c0` | 108 | 27 |
| `__memset_emag` | `0x9c300` | 224 | 56 |
| `a64l` | `0x477f0` | 76 | 19 |
| `cfmakeraw` | `0xe1500` | 60 | 15 |
| `insque` | `0xe45e0` | 32 | 8 |
| `lcong48_r` | `0x3e770` | 72 | 18 |
| `mempcpy` | `0x94a50` | 36 | 108 |
| `__memcpy_generic` | `0x9ab40` | 396 | 108 |
| `remque` | `0xe4600` | 24 | 6 |
| `seed48` | `0x3e540` | 36 | 30 |
| `seed48_r` | `0x3e710` | 84 | 30 |
| `sigabbrev_np` | `0x9aaf0` | 32 | 8 |
| `sigdescr_np` | `0x9aad0` | 32 | 8 |
| `srand48_r` | `0x3e6d0` | 52 | 13 |
| `__memmove_generic` | `0x9acd0` | 220 | 154 |

The mempcpy and memcpy maps each contain the 9-instruction wrapper plus the
99-instruction memcpy body. The memmove map contains its 55 instructions plus
the same 99-instruction body; its cross-symbol branches target actual interior
memcpy instructions. Seed48 maps each contain the 9-instruction wrapper plus
21-instruction seed48_r body. These duplicate maps are entry-specific artifacts,
not separate copies of a function-correctness proof. Code aliases share one
manifest entry/extent; no hand-written machine semantics or alias theorem was
introduced.

### Commands and actual exits

Commands below run from the worktree root. The full exact commands, diagnostics
and real exit codes are in numbered logs and per-invocation subdirectories.

- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/extract.py --run baseline01 --out /home/charles/code/friends/.toolchains/e08-arm-lifts/baseline01-published`
  (log 03): e11 raw extraction ran 65 scopes, with 12 successful raw groups and
  53 strict rejections. This **initial e08 adapter output is not acceptance
  evidence**: its closure parser missed Ghidra's printed ` --- ` prefix and
  rejected all successful groups; its old empty `PASS` message was invalid.
  No artifact from that empty publication is counted. The parser was repaired,
  empty success was forbidden, and logged fresh e11 receipts were independently
  rechecked by `collect.py` (log 16, exit 0). The final fresh replay below checks
  the repaired complete naming/closure pipeline without reusing raw outputs.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/extract.py --run move01 --selection notes/e08-arm-lifts/select-memmove.json --out /home/charles/code/friends/.toolchains/e08-arm-lifts/move01-published`
  (log 15): exit 0, actual generic memmove/memcpy union.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/collect.py --out /home/charles/code/friends/.toolchains/e08-arm-lifts/rechecked01-published baseline01 move01`
  (log 16): exit 0, 15 rechecked artifacts, copied exactly into scalar_ports.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/check-harness.py`
  (log 11): exit 0; actual global copy map passes, missing callee, missing
  fallthrough, missing call continuation and indirect transfer are rejected.
  Initial log 04 expected seven returns where the actual union has eight;
  that test expectation was corrected, with passing logs 05/11.
- `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_scalar.py`
  (log 07): exit 0, all ten unchanged e11 translator tests pass.
- Shared read-only wrapper, `export PROOF_MEMORY_KB=2000000; ulimit -v 2000000;
  ulimit -s 65536; dune build --cache=disabled -j1 --display short @scalar-lifter`
  (log 09): exit 0, all eight unchanged e11 fixtures built as full .vo.
  Original `notes/e11-canonical-lifter/check-artifacts.py` passed (log 10,
  exit 0). Initial log 08 had run its exact-eight selection assertion before
  building that alias; the later selection check removes only disposable e08
  objects before checking e11. Historical sources/fixtures were never edited.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/check-artifacts.py`
  (log 17): exit 0, all 15 artifact hashes, reverse naming hashes, exact bytes,
  model map keys, closure graphs and file-backed data bytes match.
- Shared read-only wrapper with the same cap/stack/environment,
  `dune clean; dune build --cache=disabled -j1 --display short @e08-arm-lifts`
  (log 18): **exit 0**, all 15 new .vo files checked from a clean build.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e08-arm-lifts/replay.py --run replay01`
  (log 19): **exit 0**, fresh accepted-scope replay; all 15 generated .v,
  .pcode.json and .manifest.json files reproduce byte-for-byte. The unchanged
  e11 global fixture outputs and SUCCESS receipt also reproduce exactly.
- `python3 tools/audit-proof-source.py --base 378fe1b57514b9af3f017a72b4ca665910156cc7 Examples/claude/lifter/scalar_ports`
  (log 20): exit 0, 15 sources, zero new admission/axiom/parameter tokens.
- Logs 25/26: the remaining six original e11 relative scalar fixtures, raw
  pcode and SUCCESS receipt freshly reproduce exactly in private e08 state
  (both commands exit 0). Together with log 19, all eight original e11 fixtures
  and both receipts were independently replayed without changing e11 state.
- Log 21 verifies 271 historical/prerequisite source and fixture hashes are
  unchanged, including all e11 lifting implementation and output files.
- `/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash notes/e08-arm-lifts/print-assumptions.sh`
  (log 22): **exit 0**, 15 separate fully qualified `Check`/`Print Assumptions`
  queries. Every generated typing theorem ends with `Qed`.

Verbatim assumptions for **every** new typing theorem (also printed during
the full builds) are:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited core/Stdlib functional-extensionality dependency through
existing typing automation. No new assumption declaration was added; no
additional admitted theorem appears in these transitive assumptions. Binary-only
extraction assumptions are N/A. Functional correctness assumptions are N/A
because no new function-correctness theorem was attempted.

### Reproduction and remaining work

No installation is needed. For a new complete scan use `extract.py --run NEW
--out /home/charles/code/friends/.toolchains/e08-arm-lifts/NEW-published`.
For just the accepted exact closed maps use `replay.py --run NEW_REPLAY`;
this fresh replay compares all generated .v, .pcode.json and .manifest.json
bytes and also the unchanged e11 global fixture files and SUCCESS receipt.
Existing run/output paths deliberately fail. Keep Java state/output under the
private e08 toolchain directory. The committed Dune list is explicit; build
`@e08-arm-lifts` with the recorded cap, then run `print-assumptions.sh`.

There is no blocker within the supported baseline after final validation.
This does not claim that all ARM variants lift, that e02's broader recovery is
complete, or that any IL has a functional proof. First rejection reasons are
precise boundaries, not exhaustive unsupported-instruction inventories: ZVA/MTE
families may reject on an earlier vector instruction before reaching their
family-specific operation. All original strict gates remain intact.

Suggested follow-on engineering units:

- A small reviewed scalar alias kit for REV (`inet_makeaddr`), UBFIZ (`rand_r`),
  ORN (`__memchr_nosimd`) and BICS (`strcmp`/`__strlen_asimd`); use actual raw
  pcode fixtures, not gate bypasses or approximations.
- A separate CCMP kit for `wcschrnul`, signal helpers and `memcmp`, followed by
  e09's real TLS state/error paths where required.
- e10 NEON, e12 ZVA, e13 SVE, e14 MTE and an explicit ARM prefetch/hint boundary
  remain feature work; no unsupported operation was replaced by Nop.
- Complete checked wrappers need their actual failure-path callees and closure,
  not just the successful memcpy/memmove body. Indirect comparator calls in
  bsearch/lfind/lsearch require separate call-boundary work.
- Existing proof units can consume the supported insque/remque/srand48_r,
  seed48/a64l and copy maps with real static-data/ABI/memory/frame contracts.
  Function proofs remain separate Astra-to-Sol units; no such proof began here.
