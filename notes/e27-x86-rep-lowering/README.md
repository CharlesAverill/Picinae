# e27: Strict AMD64 REP MOVS/STOS loop lowering

Local engineering unit on `llm-proofs/e27-x86-rep-lowering`, worktree
`/home/charles/.t3/worktrees/Picinae/t3-4ff7b03c`. Implemented by the assigned
single Sol child (launch metadata supplied by coordinator: gpt-6.1-sol,
xhigh, default). No subagents. No function proofs were begun.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

Nothing was installed. Existing e02 Ghidra 11.4.2/JDK21/PyGhidra and the verified
Rocq wrapper are reused read-only; existing GNU as/ld build the synthetic ELF.
All additional mutable tool/project/cache/build/assumptions state is under
`/home/charles/code/friends/.toolchains/e27-x86-rep-lowering/`.
JVM heap is `-Xmx1G`. Every Rocq/Dune/assumptions invocation used
`ulimit -v 2000000; ulimit -s 65536`, one compiler, Dune
`--cache=disabled -j1`; no cap was raised and no process was killed.

## Deliverable and exact gate

`tools/ghidra-lifter/pcode2coq_x64_rep.py` is a separate opt-in subclass of e25.
The e25 backend, supervisor, headless script, tests, seven scalar artifacts and
all existing core/proof files remain unchanged. Its scalar fallback retains
e25's rejection rules. The root Dune change adds only two modules and one alias.

The REP profile accepts exactly these eight byte strings, in 64-bit address
mode. Other prefix orderings, even equivalent ones, deliberately reject.

| Width (bytes) | MOVS | STOS |
| --- | --- | --- |
| 1 | `f3a4` | `f3aa` |
| 2 | `f366a5` | `f366ab` |
| 4 | `f3a5` | `f3ab` |
| 8 | `f348a5` | `f348ab` |

Bytes, mnemonic, instruction length, every raw opcode/arity, varnode width,
register alias, memory space, constant, def-use edge and control destination
must all agree. Unique temporaries can be alpha-renamed but cannot overlap.
The graph requires exactly RCX==0 precheck to the real next instruction;
RCX-=1; snapshots and DF updates of RDI and (MOVS only) RSI; one element load
and store for MOVS or accumulator read and one store for STOS; then the exact
self-address BRANCH. Mutations, extra/deleted/dead operations, alternative
branches, missing prechecks, different steps or body orders reject.

The **actual pinned decoder uses a machine-address self-backedge**, not a
constant relative internal pcode branch. This unit folds that exact graph;
it does not broadly accept backward branches. Relative pcode-loop variants,
address-size32, segments, duplicate/extra/LOCK/REX prefixes, unprefixed strings,
F2 MOVS/STOS, REPE/REPNE CMPS/SCAS, and other instruction families reject.
There is no arbitrary loop dispatcher or unsupported-operation Nop fallback.

## Sequential semantics and partial-progress boundary

Picinae_core.v's `Rep` evaluates its bound once (`XRep`) and repeats the body
that many times. The emitted bound is the full **64-bit entry RCX**, including
zero and up to 2^64-1; there is no fixed unrolling or truncation. With zero
RCX no body operation occurs, no memory is accessed and no pointer changes.
Each nonzero iteration reuses e25's raw scalar statement emitter for the
original ordered body, decrements RCX once and uses old-pointer snapshots for
its memory operation. DF=0 advances by element bytes; DF=1 subtracts them.
All pointer arithmetic and each byte address wrap modulo 2^64. STOS reads
AL/AX/EAX/RAX without changing RAX; MOVS reads the complete element before its
store. Later iterations read the updated memory. No nonoverlap or original-
source snapshot assumption is imposed. All architectural flags, including DF,
are preserved. Temporaries are instruction-local implementation storage.

After k **completed internal bodies**, the architectural recurrence is
RCX=entry_count-k, RDI=entry_RDI +/- k*width modulo 2^64, and RSI has the same
update only for MOVS. Memory is the ordered composition of k element transfers,
so harmful overlap can propagate overwritten bytes exactly as sequential MOVS
does. This recurrence describes the engineering model and tested oracle; this
unit does not provide a new semantic-equivalence theorem.

The folded instruction exposes successful completion as one Picinae machine
step. Intermediate self-reentry machine traces/interrupt points and iteration
costs are abstracted. There is **no hardware fault, partial-fault progress,
page permission, canonical-address, alignment, interrupt/restart, concurrency,
atomicity, or ERMS microarchitecture/timing guarantee**. In particular the raw
SLEIGH order updates count/pointers before LOAD/STORE and must not be interpreted
as Intel's precise fault/restart state. Picinae total modular memory has no such
faults; wrap tests validate that abstraction, not successful hardware accesses
across noncanonical/unmapped addresses. No memmove/nonoverlap correctness or
whole-function result follows from these typed instruction fragments.

## Provenance and fixtures

Runtime is the exact e01 Ubuntu amd64 glibc **2.35-0ubuntu3.12**, SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`.
The driver checks the full reviewed target manifest, Ghidra/JDK archives and
e25 compiled x86 decoder/spec pins. The headless script checks the loaded ELF
hash and compares every Ghidra instruction byte against the ELF and e01's
reviewed `generated/disassembly.txt`, with image base 0x100000.

`x64_rep_pinned` contains **all 26 REP MOVS/STOS instruction sites in e01's
selected disassembly**: 11 MOVSB, 10 STOSB, 5 STOSQ. For example the existing
AVX ERMS copy sites at ELF0x1a0ae4/0x1a0b4a appear at global0x2a0ae4/0x2a0b4a;
SSE ERMS sites include ELF0xc48ff/0xc490d. These are not claimed to enumerate
all REP instructions anywhere in libc. Their surrounding functions contain
unsupported SIMD/control forms and are not regenerated or proved here.

`x64_rep_synthetic` contains eight actual decoded forms from `fixture/rep.S`,
including word/dword/qword copy and fill cases absent from the pinned site set.
Its ET_DYN ELF SHA256 is
`d7a43cba073f6aced58af05e8d31498a0a31cdcaafcda8316f1507fee0d59234`.
The same assembly includes unsupported-prefix/comparison forms for real failure
batches. It is synthetic, never substituted for pinned glibc.

Each directory has a complete `.v` module, structured/raw `.pcode.json`, and
hash/selection/profile/decoder/implementation receipt. These are deliberately
**open program fragments**: next-instruction fallthrough addresses are explicit
receipt frontiers, not fabricated return stubs or closed function maps.
Both entire modules have full kernel-checked `.vo` objects in the isolated Dune
build. No `.vos`/quick compilation substitute was used.

The raw sources inspected as templates are Picinae_core.v's bounded Rep/XRep,
Picinae_finterp.v's repeat interpreter, existing memmove_avx_amd64.v's exact
self-reentering MOVSB loop, and pinned Ghidra ia.sinc's MOVS/STOS, rep/reptail,
DF pointer constructors. Existing older lifts were templates only; actual
pinned Ghidra pcode and instruction bytes drive the new output.

## Verified commands, exits and logs

Run from this worktree root; no dependency installation is required. The final
logs record exact expanded commands and exit codes. Initial logs retain the
first full build and diagnostic raw inspection. Commands 04/05/06/07 initially
used shell redirection; their outer sequence completed with exit0 and the real
failure harness records each expected/actual subprocess exit.

| Command | Exit | Evidence under `logs/` |
| --- | --- | --- |
| `python3 tools/ghidra-lifter/test_x64_rep.py` | 0 | `08-backend-final.log` |
| `python3 notes/e27-x86-rep-lowering/check-artifacts.py` | 0 | `09-artifacts.log` |
| `python3 tools/ghidra-lifter/test_x64.py` | 0 | `10-e25-regression.log` |
| capped Dune command below | 0 | `03-dune.log`, `11-dune-final.log` |
| wrapper + `bash notes/e27-x86-rep-lowering/print-assumptions.sh` | 0 | `12-assumptions.log` |
| `bash notes/e27-x86-rep-lowering/fixture/build.sh` (rebuild/cmp) | 0 | `13-fixture-rebuild.log` |
| `bash notes/e27-x86-rep-lowering/reproduce.sh --check` | 0 | `14-replay-final.log` |
| `python3 tools/ghidra-lifter/test_x64_rep_publication.py` | 0 | `15-receipts-final.log` |
| `python3 notes/e27-x86-rep-lowering/check-failures.py` | 0 | `05-real-failures.log` |
| `python3 tools/audit-proof-source.py --base 328088263ebba11786a03448808e584231504fe1 Examples/claude/lifter/x64_rep_pinned Examples/claude/lifter/x64_rep_synthetic` | 0 | `17-source-audit.log` |
| `git diff --check` | 0 | `18-whitespace.log` |

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000; dune build --build-dir /home/charles/code/friends/.toolchains/e27-x86-rep-lowering/build --cache=disabled -j1 --display short @x64-rep-lifter @x64-scalar-lifter'
```

The initial Dune build compiled core dependencies and both REP modules from an
empty isolated build directory. The final command also compiled all seven e25
scalar modules. The 12 existing e25 tests passed with unchanged fixtures.
The 7 REP tests exercise **2,720 raw-pcode/IL/independent-oracle cases** across
all 34 actual instruction sites: counts0/1/2/3/9, both DF values, 1/2/4/8-byte
elements, disjoint/identical/overlapping pointers, large addresses, arithmetic
and intra-element byte wrap, all architectural registers/flags and complete
memory frame. A no-access memory object checks zero count. A separate structural
check verifies the maximum64-bit bound remains untruncated (not brute-force
execution of 2^64-1 iterations). **3,346 graph mutations** reject, plus explicit
prefix/mnemonic/relative-backedge variants. Alpha-renaming remains accepted.

Real mixed supported+unsupported batches reject with exit1 for addr32, segment,
F2, CMPS, SCAS, duplicate F3, and missing symbol. Every batch has no accepted
output, staging directory or leaked fresh project. Existing destination and
broken symlink reject with exit2 and preserve contents. Missing/stale/incorrect
receipt, wrong semantic profile/hash/set and partial files also reject. Raw
Ghidra launcher logs retain swallowed exceptions with launcher exit0; a fresh
validated receipt, not that exit, controls acceptance.

## Assumptions and ancestry

Both `welltyped` queries, saved verbatim in `logs/12-assumptions.log`, report:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is inherited from the existing Picinae typing/program-equality machinery
and Stdlib FunctionalExtensionality (the e00 evidence records its source/hash).
No new axiom or admission was added; source audit reports zero forbidden tokens
in the two new Rocq files. These facts establish typing only, with that inherited
assumption, not functional correctness or binary/lifter soundness.

Origin base remains `49956416928e5b6bb3928b54ae33e3b81091f006`;
timing pin `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6` was not imported.
Prepared clean HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The fork collision query returned empty before renaming only the prepared local
branch, then `git merge --ff-only 328088263ebba11786a03448808e584231504fe1`
succeeded. `allowed-prerequisites.txt` records the exact seven authorized
base..checkpoint commits **before edits**, including only reviewed e00/e01/e02/
e11/e25 prerequisite history. `check-ancestry.py` enforces that exact set plus
the one own implementation commit and an unchanged origin merge-base. Before,
imported and final ancestry/diff-stat evidence is saved here. No e26/e28 or fork
branch was imported, and no other branch/worktree was changed or created.

## Feature gates and handoff

No blocker remains for this exact instruction-fragment subset. Follow-on e06/
e07 work must explicitly opt into `X64RepLifter` and close real scalar/vector
function maps using independently reviewed prerequisites. This unit does not
integrate active e26/e28 work. Other prefix orders, addr32/segments, comparison
strings, alternative raw loop graphs, faults/restarts, CET-enabled/full hardware
semantics and semantic instruction equivalence require separate scoped units.
Function-level correctness proofs remain future proof units.

All work is local-only: no push, PR, remote mutation/comment, fork-branch change
or deletion, host installation, shared environment mutation, or shared plan/
status edit. Publication requires Charles's separate approval; future direction
would be CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.
