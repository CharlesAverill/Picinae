# e36-arm-cneg

Validated guarded CNEG engineering kit. Canonical memcmp remains rejected at
its actual vector frontier; no new function map is delivered. Finite execution
and typing do not establish universal instruction or function correctness,
termination, hardware refinement, DIT/timing, faults or an ABI contract.

Branch: `llm-proofs/e36-arm-cneg`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ff05d511`.
Prepared HEAD: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, clean.
Reviewed prerequisite: `bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9`.
Origin/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing pin, not imported: `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
Engineering producer: assigned gpt-6.1-sol, xhigh/default. No delegation.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No installation occurred. Shared arm-validation wrapper and e02 runtime,
debug ELF, Python venv, Ghidra and JDK were read only. All mutable Ghidra state,
assembly intermediates and subprocess artifacts use only
`/home/charles/code/friends/.toolchains/e36-arm-cneg/`.
Repository evidence is only in this unit's notes and scalar_cneg fixture folder.
The existing wrapper is Rocq 9.1.1 / OCaml 4.14.2 / Dune 3.22.2 (log12).
Every compiler, Dune build and assumptions query uses `ulimit -v 2000000`,
`ulimit -s 65536`, one compiler and disabled Dune cache. JVM heap is <=1 GiB,
without the compiler's small virtual limit. No limits were raised, shared
plan/status edited, host-wide processes killed, other branches changed,
worktrees created, dependencies installed or remote writes performed.

## Encoding, raw control and exact scope

`ScalarLifter.check_cneg` adds only CNEG to the separate scalar frontend.
It checks all fixed/reserved encoding bits against mask `0x7fe00c00` /
value `0x5a800400`, requires Rn=Rm, restricts source/destination to W0..W30
or X0..X30, and excludes AL/NV. The encoded CSNEG condition is inverted for
CNEG. Fourteen alias conditions EQ/NE/CS/CC/MI/PL/VS/VC/HI/LS/GE/LT/GT/LE
are admitted; CS/CC are the HS/LO condition encodings. Zero-register operands,
unequal CSNEG sources, altered reserved/shift-like bits, unsupported widths
and other conditions do not enter this CNEG path. Other CSEL-family gates
are unchanged, and no family-wide whitelist was added.

The complete raw Ghidra 11.4.2 DAG is matched: exact opcode order/arity,
register slices, condition flag inputs, unique-node identity and widths,
INT_2COMP into an instruction-local temporary, CBRANCH by precisely +2 pcode
operations, original-source COPY and final X COPY / W-to-X INT_ZEXT. Unique
initialization and overlapping-range rejection remain enforced. The existing
bounded forward-branch translator handles this already-supported control shape;
there is no general CFG/suffix relaxation. Machine CBRANCH suffix gates remain
unchanged, as confirmed by the scalar/CCMP and closure regressions.

CNEG snapshots the condition before the only architectural destination write;
NZCV and scratch flag bytes are preserved, including when source=destination.
The result is modular negation when the alias condition holds, otherwise the
old source. INT_MIN negates to itself; W inputs use low32 and every W output
zero-extends to X, including the non-negating path. X forms retain full64.
All other GPRs, SP, PC and scratch flags are compared in every finite snapshot.
Inputs use normalized 0/1 NZCV cells, matching the inherited byte-flag model;
dirty scratch bytes and dirty upper X halves are explicitly exercised.

Primary Arm semantics are the e30-pinned official A64 ISA PDF, SHA256
`89973c3d41fe5f45cc8581ff41db7c8736d3f2b6d7bb6568112a3c3ac81cb845`:
CNEG p107, CSNEG p121/122 and shared ConditionHolds. This existing local PDF
and its text were read unchanged. `arm-reference.json` and log09 retain the
reviewed locations, exact commands, hash and output.

## Pinned fixtures and actual memcmp frontiers

Ubuntu ARM64 glibc 2.35-0ubuntu3.15 libc SHA256:
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
Pinned Ghidra 11.4.2 / AARCH64:LE:64:v8A / image base0x100000.
The unchanged supervisor validates the e02 runtime/debug and dependency archive
pins. GNU AArch64 assembler2.42 from the existing isolated environment produces
168 encodings: two widths, fourteen conditions and six source/destination
pairs (0/0,0/1,1/0,30/30,29/30,30/29). Ghidra independently decodes them.
`fixtures.s`, RAW.json and PROVENANCE.json retain source, exact bytes, raw
pcode, implementation hashes and the final fixture/.vo hashes. Fresh collection
reproduced RAW.json byte-for-byte (logs02/11). Target instructions were also
checked individually against pinned runtime ELF bytes.

Canonical memcmp is entry0x194640, 114 instructions /456 bytes. Both actual
`cneg w0,w0,cc` sites at0x1946e4 and0x194800 are accepted. Complete supervised
extraction exits1, first at0x194780 `ldr q0,[x0,#0x10]`; there is no accepted
output directory or staging residue. A separate diagnostic pass runs the same
strict backend on every instruction without emitting any partial program:
97 instructions accept and17 reject. The complete address/encoding/reason list
is `memcmp-instruction-audit.json`. All rejected shapes are:

- Q loads at0x194780,0x194784,0x19478c,0x194790,0x19479c,0x1947a0,
  0x1947a8,0x1947ac (the last two write back their base register).
- Vector EOR at0x194794,0x194798,0x1947b0,0x1947b4.
- UMAXP16-byte reductions at0x1947a4,0x1947b8,0x1947bc,0x1947c0.
- FMOV X6,D0 at0x1947c4.

These are diagnostics of currently rejected instructions, not an assertion that
supporting them suffices for a verified complete vector lift. The memcmp NEON
prerequisite stays in place. Follow-on units should separately cover coherent
vector state/load/writeback and EOR, UMAXP byte-lane reduction, and FMOV D-to-X,
with exact encodings/raw pcode and fixtures, followed by a new complete map,
closure and full .vo check. Universal CNEG soundness and memcmp functional
correctness are separate future proof units.

`TARGETS.json` records all ten actual target results. The three existing e30
closed scalar maps (__memchr_nosimd56,strcmp77,wcschrnul9 instructions) still
reproduce. __strlen_asimd still rejects at0x19c9e0 vector LDP; sigandset,
sigorset,sigaddset,sigdelset,sigismember still reject at their unchanged TLS MRS
frontiers. No vector/TLS/prefetch instruction was approximated or added.

## Validation and assumptions

Every numbered log records exact argv, CWD and actual exit status. Important
successful commands (all exit0 unless the expected failure is stated):

- `env PYTHONDONTWRITEBYTECODE=1 python3 tools/ghidra-lifter/test_cneg.py`
  (logs05/21):168 exact encoding/raw shapes,40320 independent Arm-equation/IL
  architectural snapshots,13716 malformed encoding/DAG/control/width/arity/
  output rejections, temporary reset/alpha-renaming and overlap rejection.
- The same command with `--generate` (log18):29568 full-Cartesian finite Rocq
  executions (168 encodings x16 flags x11 operands), split into231 closed
  facts, plus full fixture typing. All41 defined GPR/SP/PC/NZCV/scratch cells
  are compared and interpreter exit must have no memory-access events. Bounded
  continuation exhaustion fails; no missing branch is counted as successful.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e36-arm-cneg/validate.py --run validate01`
  (log06):fresh ten-target extraction and all e11/e08/e29/e30 program/pcode/
  record content reproduced. REFERENCE-DELTAS.json records solely justified
  pcode2coq_scalar.py implementation-hash changes. No old manifest/receipt,
  generated program or evidence was overwritten. Eight whole-batch publication
  failures and unsupported-op subprocess exit1 and leave no output/staging.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e36-arm-cneg/replay.py --run replay01`
  (log14):fresh deterministic three-map replay and seven exact frontiers, with
  nonzero no-output failure. Logs preserve all actual Ghidra diagnostics.
- `env PYTHONDONTWRITEBYTECODE=1 python3 notes/e36-arm-cneg/check-atomic.py`
  (log10):five malformed raw/encoding subprocesses each exit1 with no IL;
  deterministic unique renumbering and overlapping-unique rejection.
- Unchanged `test_scalar.py`, `test_bitforms.py`, `test_ccmp.py` (log08):
  ten scalar tests;12800 bitform snapshots/1549 rejections;81360 CCMP
  snapshots/65336 rejections. Old fixture IL statements also reproduce
  byte-for-byte (25 bitform/339 CCMP shapes,log25).
- Original e08 closure negatives and all15 artifact/hash/byte/data/closure
  checks (log24); new fixture/hash/byte/no-map checks (log20); source/ancestry
  audits and1043 protected file hashes (logs15/16 and final26).

Full selective Dune build, log19, exit0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'export PROOF_MEMORY_KB=2000000; ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short @all'
```

The initial @all built all selected dependencies; its own fixture exhausted
memory because each snapshot repeated41 state cells as source literals. The
final fixture shares the frame and snapshot constructors, retaining every
frame check and increasing the finite matrix. The successful retry kernel-
checked the final full .vo with all prerequisites built. Dune verification is
complete, without .vos shortcuts, admissions or cap increases.

Explicit Print Assumptions, log23, exit0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash notes/e36-arm-cneg/print-assumptions.sh
```

All232 new facts were queried against the final .vo. For each
`e36_cneg.finite_execution_0` through `finite_execution_230`, verbatim:

```text
Closed under the global context
```

For `e36_cneg.welltyped`, verbatim:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Picinae typing-automation/Stdlib dependency, as in e30.
No new assumption declaration or admitted transitive lemma was introduced.
Binary extraction assumptions: N/A. Universal instruction/function correctness:
N/A; no such theorem is introduced. Full raw query output is in log23, with
an exact assumption summary in ASSUMPTIONS.txt.

Development failures are preserved honestly: log03's overlap-negative test
initially placed two unique slots adjacently rather than overlapping; the test
was corrected and rerun in05. Log07 exhausted the fixed compiler cap; log19
passes with shared source snapshots. Log22 used a nonexistent old script name
and exited2; the correctly named unchanged check-harness.py and artifact checks
passed in24. There is no success claim for those failed invocations.

## Ancestry, local commit and publication

The required read-only fork-name collision check returned exit0 and empty
output after the initial sandbox DNS failure. Prepared HEAD and ancestry were
verified before renaming only the prepared branch, then fast-forwarding only
reviewed e30. Git metadata writes required sandbox escalation because the
linked worktree's Git metadata is outside this writable checkout.
The exact allowed base..e30 set, recorded before implementation in log01, is:

```text
71470bffba65392adf1873a3df9f0cf0ca4f1ac9 e00
081d0233cd6667803b3907343b2fea6dc9eba714 e02
052521a753adbda077843ec7b259801282a7b1e9 reviewed e02 import
378fe1b57514b9af3f017a72b4ca665910156cc7 e11
9ae8e6800fa044797efd98372857e6ac89b18e1b e08
9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b e29
bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9 e30
```

Only own e36 commit(s) may follow this set; audit.py enforces exact branch,
merge-base, prerequisite set, own scope and all1043 protected hashes. Before
and final after merge-base/log/diff-stat audits are preserved; the exact final
full commit SHA and clean-worktree audit are under the unique external path
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/e36-arm-cneg/`.
No fork history was imported. Verbatim raw Ghidra/reference logs are excluded
from whitespace cleanup. No push, PR, comment, remote mutation, branch deletion
or shared plan/status edit occurred. Future publication requires Charles's
explicit approval for this unit, and would be CharlesDardaman/Picinae ->
CharlesAverill/Picinae:llm_generated_proofs. Other units' approvals do not apply.
