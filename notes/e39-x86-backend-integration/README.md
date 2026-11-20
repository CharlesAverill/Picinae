# e39: compose the reviewed AMD64 backend profiles

Local engineering subset: explicit scalar/copy256/REP/guarded-scan extraction.
Model/effort/tier assigned: gpt-6.1-sol / xhigh / default. Work performed by this
single implementation child; no subagents, remote writes or publication.
Branch `llm-proofs/e39-x86-backend-integration`;
worktree `/home/charles/.t3/worktrees/Picinae/t3-95c58422`.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

Nothing installed. Native existing as/ld assemble the fixture; pinned shared
e01/e02 Ghidra/JDK/Python data and the verified Rocq wrapper are read-only.
Mutable environment/cache/project/build state stays under
`/home/charles/code/friends/.toolchains/e39-x86-backend-integration/`.
Java uses `-Xmx1G` without a tiny virtual limit. Every Dune/Rocq/assumptions
process inherits `ulimit -v 2000000; ulimit -s 65536`; Dune uses
`--cache=disabled -j1`. No cap increases or host process killing.

## Ancestry and provenance

Read the shared plan and assigned row before implementation; did not edit plan
or status. Followed repository `Examples/claude/SKILL.md` provenance/typing
conventions with Charles's no-admission/resource/commit overrides. No function
proofs or instruction semantic lemmas were started.

Prepared clean HEAD was exactly e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, with merge-base
`49956416928e5b6bb3928b54ae33e3b81091f006`. The read-only
`git ls-remote --heads fork refs/heads/llm-proofs/e39-x86-backend-integration`
returned exit0, empty output before branch rename. Initial Git mutations were
sandbox-denied because worktree Git metadata is outside the writable root;
explicitly authorized local operations then succeeded with tool escalation.
No branch or HEAD changed in the denied attempt.

Renamed only the prepared branch, fast-forwarded exactly e28
`e6c578dbaa0fd59910b170dde8ea90902c9a00e4`, then imported only e26
`bcdd924bec65111aeb9244de21e5dba6286da845` and e27
`9f5b4498a8dd5129ec8c710c524ac61dc9234a71` in two local merges. Only `dune`
conflicted. Resolved its explicit module and alias lists by union, with no globs.
`allowed-prerequisites.json` records each exact base..prerequisite set and their
11-commit union BEFORE integration. `check-ancestry.py` checks the merge-base,
all assigned ancestors, own continuation subjects and protected source/evidence.
Timing `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` was reference-only.
e37/e38/e40/e16/e34 and unrelated/fork/active-unit history were not imported.
Before and staged ancestry/log/diff-stat evidence is under `logs/`. The final
commit audit and handoff are saved separately under the assigned external
`units/e39-x86-backend-integration/` directory to avoid a self-referential SHA.

Actual x86 source remains Ubuntu glibc 2.35-0ubuntu3.12,
SHA256 `9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
build ID `085164b7e9093b36e3be17226f0d94a35b818c55`, image base 0x100000.
No host-libc substitution. The fixture is separately tagged synthetic, with ELF
and source pins. Fresh Ghidra11.4.2 raw SLEIGH pcode is used, never decompiler IR.

## Composition and trust boundary

`IntegratedLifter` inherits the reviewed helpers, but its instruction entry point
calls the authoritative validators explicitly: e26 for copy-family mnemonics,
e27 for exact REP encodings, e28 scalar/guarded-scan otherwise. It does not rely
on cooperative `super()` dispatch. Helpers' fallback paths are never reached
when explicitly selected. No catch-and-retry broadening occurs. All instruction
local temporary/range/initialization state resets before dispatch and in a
`finally` block, including failure. Original five backend/helper sources remain
byte-identical to their assigned prerequisite commits.

CPU BMI1 and ABM/LZCNT declarations are independent. Missing declarations reject
F3 scans; `absent` selects reviewed BSF/BSR semantics. Undefined outputs and
flags remain nondeterministic `Unknown`; source snapshots preserve scan aliases.
Copy keeps exact prefix/encoding/raw-DAG/source-byte/alignment/upper-lane gates,
REP keeps its exact precheck/body/self-backedge, DF and ordered alias behavior,
and scalar keeps its own prefix/control rejection rules. CET remains explicit.

The new headless/supervisor path checks exact pinned ELF/debug bytes, all
selected instruction extents, direct edges and machine fallthroughs (including
REP self and exit edges), and publishes only a complete nonce/hash-validated
output set by directory rename. A RET is a dynamic ABI boundary, not a statically
enumerated return target. The new mixed fixture has a CLOSED selected CFG under
that boundary: vector self aliases, scalar setup, MOVSB, aliased BSF, conditional
branch, TZCNT/LZCNT or STOSQ+BSR, jump, VZEROUPPER and RET. Both branch paths are
selected. “Closed” here describes selected instruction boundaries; typing
assumptions are reported separately below.

`x64_provenance.py` walks imports anywhere in the AST, including the e28 import
inside `X64Lifter.instruction`, recursively resolves local modules, and rejects
unresolved dynamic import APIs. The receipt covers all backend/helpers,
supervisor/headless, ELF parser and its retrieval helper, provenance helper,
fixture binary/source/build/pins, e01 source manifest, e02 archive lock and x86
SLEIGH pin source. Exact enabled/absent/unspecified features, semantics/scope,
archive/SLEIGH pins, source hash and output/raw hashes are also bound. Supervisor
snapshots the closure before launch and compares it to headless and post-launch
closures before publication. Existing standalone receipts are never accepted
as current combined receipts.

## Regressions and preserved historical evidence

All original e25/e26/e27/e28 notes, raw captures, programs and receipts are
unchanged. Compatibility adapters import the unchanged historical supervisors
and override only their private mutable state roots. Original real-negative
scripts run with those path substitutions; fixture choices/assertions stay
unchanged. The original REP receipt unit test hardcodes a shared tmp directory;
`run-tests.py` redirects temporary directories to e39 without modifying the test.

`replay-deltas.json` records fresh historical-format Ghidra replay separately:
all 38 programs and 38 raw captures byte-identical, with these expected metadata
deltas inherited from e28 (no profile or program/raw deltas):

* e25: changed `pcode2coq_x64.py`, changed `lift-x64.py`, newly listed
  `pcode2coq_bitscan.py` implementation hashes.
* e26/e27: changed `pcode2coq_x64.py` implementation hash only. Their historical
  receipt format omits the transitive scan helper; the combined format fixes it.
* e28: no receipt delta.

The replay adapters' receipts remain explicitly historical-format replay data,
not claims that old accepted implementation hashes describe the current backend.
New combined receipts have a different profile/schema, complete dependency map,
features, semantics/scope and output names; their expected differences are
separate from the byte-identical old program/raw replay.

`validate.sh` contains exact reproducible commands. `tools/record-command.sh`
logs CWD, command, stdout/stderr, actual exit status. Exploratory failed runs are
retained: initial inherited suite hit the read-only hardcoded shared tmp; two
replay adapters initially needed the known e25 metadata allowlist and e26 output
root constraint. Final logs supersede those adapter failures; no old evidence
was rewritten and no semantic gate was relaxed to pass a check.

## Final verified results

All commands run from the worktree root. Exact CWD/commands/output/exit codes
are retained in the named logs; `run-build.sh` and `print-assumptions.sh` record
the mandatory resource setup in tracked source.

| Check | Log under `logs/` | Actual result |
| --- | --- | --- |
| Original suites with private tmp adapter | 13-original-final-tests.log | exit0,45 tests |
| Copy/REP/scan suites through composition | 14-integrated-final-tests.log | exit0,45 tests |
| All four scalar/copy/REP/scan suites through composition | 20-full-dispatch-tests.log | exit0,45 tests |
| All four original real-negative/atomic suites | 03-old-negatives.log | harness exit0, expected launcher1/CLI2 |
| Fresh historical Ghidra replay | 08-old-replay.log | exit0,38 programs+38 raw captures identical |
| Actual pinned copy census | 07-copy-frontiers.log | exit0,67 extents |
| Mixed real-negative/atomic/feature cases | 09-combined-negatives.log | harness exit0, six expected1/five expected2, absent-feature success0 |
| New mixed generation and byte-identical replay | 10-combined-generate.log,11-combined-replay.log | exit0 each |
| Full selected Dune build from empty private build tree | 12-dune-full.log | exit0 |
| Fixture ELF rebuild/cmp | 16-fixture-rebuild.log | exit0 |
| Toolchain versions | 17-toolchain.log | exit0,Rocq9.1.1/OCaml4.14.2/Dune3.22.2 |
| New source admission/axiom audit | 18-source-audit.log | exit0,no suspicious tokens |
| All39 separate Check/Print Assumptions queries | 22-assumptions-exact.log | exit0,39 FE-only |
|39 compiled objects,receipt hashes,mixed closure | 23-final-artifact-audit.log | exit0 |

Actual Dune invocation (inside capped `run-build.sh`):

```
ulimit -v 2000000
ulimit -s 65536
/home/charles/code/friends/.toolchains/arm-validation/picinae-env dune build --root . --build-dir /home/charles/code/friends/.toolchains/e39-x86-backend-integration/dune --cache=disabled -j1 @all
```

Actual assumptions invocation (inside the same caps):

```
rocq compile -q -R /home/charles/code/friends/.toolchains/e39-x86-backend-integration/dune/default Picinae /home/charles/code/friends/.toolchains/e39-x86-backend-integration/assumptions.<run>/Assumptions.v
```

The exact generated run directory appears in the logged compiler invocation;
the tracked script reproduces it with `mktemp`. `Assumptions.v` saves the complete
query source. The saved
verbatim output names all39 queried modules. `typing-targets.json` explicitly
lists seven scalar,five copy,two REP,24 scan and one mixed target. The complete
selected project also built inherited core,AArch64 scalar and baseline smoke
modules. There is no pending Dune verification for this unit.

Finite suites cover6560 vector reference comparisons,2720 REP raw/IL/oracle
cases,3346 REP graph mutations,17832 scan/profile/input/Unknown comparisons,
2136 scan node mutations,plus scalar tests and320 mixed whole-program reference
comparisons. These are finite regression results, not universal correctness
proofs. Mixed tests cover both branch paths,memory source/destination overlap
and self-alias,DF0/1,modulo64 wrap,both independent BMI1/ABM choices,and two sampled
Unknown values. Interleaving tests additionally cover missing CPU declarations,
failed instructions followed by successful reuse and all instruction-local resets.

All39 typing queries print exactly this existing dependency:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Provenance: existing Picinae static typechecking soundness/compute machinery uses
Stdlib functional extensionality; the same output was accepted for e25-e28.
No new Axiom/Parameter,admit/Admitted or function correctness theorem was added.
The mixed `welltyped` theorem is kernel-complete Qed but FE-dependent. Closed
CFG coverage does not mean axiom-free typing. No function proof was attempted.

## Remaining actual copy gates and follow-on units

`inspect-copy-frontiers.py` recomputes the census from the pinned e01 disassembly
for all67 distinct copy extents and checks it against accepted e26 evidence.
`copy-frontiers.json` saves actual bytes/sites/owners. Counts are disassembly
occurrences, not claims of reachable coverage or a complete rejection frontier.

* The actual AVX unaligned ERMS attempt still first rejects Ghidra `JC` at
  global0x2a084b (objdump `jb`): e37 branch spelling/condition audit. Equivalent
  aliases are not granted by the combined path.
* LDDQU572, no VLDDQU in this copy census: e38 exact family gate.
* CLD1/STD1 remain rejected even though MOVS/STOS compose: e40 DF controls.
* PREFETCHNTA76, PREFETCHT0152, PREFETCHT164, SFENCE20, LFENCE4: e16 explicit
  hint/order/fault boundary; not translated as Nops.
* PALIGNR720 (PSHUFB0 in these copy extents): e34 separate shuffle family.
* EVEX VMOVUPS128, VMOVDQU64218, VMOVNTDQ44, VMOVDQA6432 remain rejected,
  including low-width forms; e15/e17 wide state/lowering.
* VZEROALL1, XTEST1, and scalar INC/DEC/padding/XCHG and branch-hint/notrack
  encodings still need separately scoped checks. String vector operations e35
  also remain separate. Do not infer full support from an objdump mnemonic.

This is a validated composition subset, not whole-copy lifting, hardware or
lifter refinement, instruction/function semantic correctness, or glibc correctness.
Low256/sequential/undefined-output projections remain explicit. Faults,
interrupt/restart, MMIO, ordering/cache/timing, state above256 bits, CPUID/XCR0
and CET-enabled execution remain outside the model. Functional proofs and e06/e07
whole-body extraction must wait for their actual prerequisites.

LOCAL ONLY: no push, PR, comment, reviewer request, remote merge or branch deletion.
Future publication needs Charles's explicit approval and would go
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.
