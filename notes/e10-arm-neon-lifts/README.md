# e10-arm-neon-lifts

Local engineering: opt-in Q128 load foundation over the existing coherent
Z256 register cells. No universal instruction or function proof is delivered.
Scalar defaults, ISA/core, prior programs/proofs, raw traces and receipts are
unchanged. No complete memcmp or strlen map is published.

Branch: `llm-proofs/e10-arm-neon-lifts`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-0fa60739`.
Prepared clean HEAD: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
Assigned source forest: `a3a80d011dc91d51b163b9d68c33ef92ea40635b`.
Origin and merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Timing pin, not imported: `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
Producer launch metadata: gpt-6.1-sol / xhigh / default. No subagents.

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No dependencies were installed. Shared e02 Ghidra/JDK/Python/runtime/debug
and arm-validation Rocq/assembler dependencies were read only. All mutable
projects, caches, binaries, logs and Dune compiler products are private under
`/home/charles/code/friends/.toolchains/e10-arm-neon-lifts/`.
Compiler/Dune/assumptions limits: `ulimit -v 2000000`, `ulimit -s 65536`,
`--cache=disabled -j1`, one compiler. No cap raises. Java heap <=1 GiB with
no compiler virtual limit. No host installation, sudo, global package edits,
shared environment/plan/status edits, worktrees or remote mutations occurred.
Git metadata writes needed escalation outside the linked writable checkout.

## Exact engineering gate

`pcode2coq_neon_loads.NeonLoadLifter` is a separate opt-in subclass.
`lift-neon-loads.py` and `neon_loads_headless.py` provide a separate supervised
entry point, fresh nonce/hash checks, atomic directory publication, and a
profile receipt hashing all four transitive translator/supervisor helpers.
Existing scalar code is byte-identical. Scalar fallback uses a fresh
`ScalarLifter`, so a generic scalar mnemonic cannot acquire vector acceptance.
There are no new generic vector opcode, userop, prefix or Nop whitelists.

The gate checks four-byte length and all fixed/reserved machine bits, decoded
registers, displacement sign/scale, index extension/scale and the entire raw
Ghidra 11.4.2 DAG, including every temporary, exact opcode/order/arity/width,
RAM-space token, load order, source snapshot, effective address, pair increment,
base writeback and each of the two explicit upper64 zero writes.

Accepted Q128 forms (no D load instruction is added):

- LDR unsigned immediate, imm12*16, offsets0..65520.
- LDR pre/post indexed signed imm9, offsets-256..255 bytes.
- LDR register offset: X index with LSL/SXTX, W index with UXTW/SXTW;
  shift0 or4. Index zero-register forms reject. Base X0..X30 or SP.
- LDP Q pairs with distinct destination registers, signed imm7*16 offsets
  -1024..1008, signed-offset/pre/post addressing. Base X0..X30 or SP.

Destination Q0..Q31 are exactly low128 of existing `R_Z0..R_Z31`.
D0..D31 are the same cells' low64; no independent D/Q state exists.
Pinned Ghidra bases are z0 at0x5000, stride32 bytes through z31 at0x53e0,
width256. Upper64 slices at byte16/24 are unnamed by Ghidra; their enclosing
named Z256 metadata is explicitly checked. Actual raw Q loads write low128,
then zero bits128..191 and192..255. Dirty upper Z bits therefore clear,
while all non-destination Z cells, GPRs, flags, PC and memory stay framed.
Register indices/bases are read from the old state; post-index snapshots
retain the old base after the modeled early writeback.

Strict rejects include overlapping LDP destination pairs (constrained
unpredictable), D loads, LDUR Q, literal Q, stores, NEON arithmetic/reductions,
other arrangements, zero indices, invalid extension bits and any mismatched
encoding/raw DAG. Scalar instructions retain exactly their earlier gates.

This is a **fixed256 model/profile**, matching the pinned Ghidra and existing
Picinae state. It is not general scalable SVE, a CPU-feature/trap model or a
claim about unmodeled bits above256. Primary ISA is the unchanged e30/e36 Arm
A64 PDF SHA256 `89973c3d41fe5f45cc8581ff41db7c8736d3f2b6d7bb6568112a3c3ac81cb845`;
exact source sections and review commands are in arm-reference.json/log10.
Hardware correspondence additionally needs enabled AdvSIMD, canonical ordinary
readable addresses, appropriate alignment/SP alignment and stable memory.
The IL uses total little-endian bytewise modular memory, including deliberate
unaligned and wrapping finite fixtures. No fault, alignment-fault, tag check,
partial-progress, timing, concurrency or atomic-pair guarantee follows.
In particular, raw SLEIGH pre/post writeback occurs before loads; this unit
only compares completed nonfaulting sequential IL executions, never fault
state ordering against hardware.

## Pinned evidence and remaining frontiers

Runtime: Ubuntu ARM64 glibc2.35-0ubuntu3.15, ELF SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
Ghidra11.4.2, AARCH64:LE:64:v8A, image base0x100000. GNU assembler uses
existing isolated arm-validation dependencies. fixtures.s/RAW.json retain
exact source/encodings/register metadata/raw pcode. collect01 and fresh
collect02/collect03 raw outputs are byte-identical; collect02/collect03 also lower actual Ghidra
instruction objects. All126 finite-case encodings reproduce identical IL
between actual Ghidra and offline raw replay. Old e36 target raw evidence is
byte-identical, checked against the same pinned ELF by existing artifact tests.

`OPEN-FRAGMENTS.json`, IL.json and the main Rocq map are explicitly open
isolated instruction fragments. They are not function maps. The separate
closed synthetic fixture has real instruction boundaries0,4,8, exact assembled
LDR Q0 / post-index LDR Q31 / RET words and explicit return boundary12.
Its finite composed execution checks frames and that return. No new libc
function map is offered for publication.

FRONTIERS.json records per-instruction diagnostics across all ten old targets.
All eight actual memcmp Q loads now accept, including both pre-writeback loads.
Its remaining nine rejections are four EOR, four UMAXP, one FMOV; complete
supervised extraction rejects first at0x194794 EOR. The strlen first Q-pair
load at0x19c9e0 accepts, but complete extraction rejects at0x19c9e4 UMINP.
Its18 remaining rejections include UMINP, CMEQ, FMOV, BIC, UMAXP, LD1, DUP,
AND and ADDP. Supporting only EOR/UMAXP/FMOV will not complete strlen.
Other TLS MRS frontiers are unchanged. No partial function map survives a
rejected batch.

Follow-on work: e41 EOR, e42 UMAXP, e43 FMOV; separate strlen UMINP/CMEQ/
mask/structured-load/reduction units based on the exact frontier list;
a-neon-lemmas for universal accepted-load/view semantics; only afterward
fresh complete-function extraction and separate functional PROOF units.

## Validation records

`run.py` records exact argv, CWD and actual exits in numbered logs.
Key final checks (exit0 unless explicitly expected):

- log29:126 exact encodings,4536 independent byte-array/register oracle
  executions, all74 architectural cells including memory framed, ordered
  read width/address checks, every emitted temporary compared to a separate
  small raw evaluator, coherent post-load D/Q reads, dirty upper Z bits,
  index/base aliasing, negative extensions, unaligned/modular addresses;
  10794 malformed encoding/DAG/width/order rejections, alpha renaming,
  unique overlap rejection, wrong Z metadata and unchanged scalar vector gate.
- logs02/07/22: fresh Ghidra projects and exact raw/IL replay, assembler exits0.
  The deliberate equal-register LDP rejection fixture produces an assembler
  warning and is rejected by the lowering gate.
- logs09/21: fresh supervisor scalar smoke plus complete memcmp/strlen and both
  mixed-batch orders; expected unsupported exits1, no output/stage residue,
  transitive helper hashes and unchanged scalar raw trace. Raw launcher logs
  are retained in logs/supervisor/.
- log13: eight malformed subprocesses each exit1 and emit no IL.
- log08: all earlier scalar/bitform/CCMP/CNEG oracle regressions pass.
- log19: earlier bitform/CCMP IL and Rocq statements unchanged; original e36
  hashes/ELF diagnostics pass; protected baseline files and ancestry pass.
- Source audit in log18 adds no admission/axiom tokens; original e08 closure
  negatives and all15 published artifacts pass. That combined command then
  exits1 at an old e29 helper-hash assertion: the e29 historical receipt
  predates e30/e36 changes. INHERITED-RECEIPT-DELTAS.json/log19 explicitly
  compare current source against assigned-base source and retain the existing
  differences. No historical receipt is rewritten and e10 changes no helper
  hash used by any earlier artifact.

The first finite Rocq build (log06,exit1) exposed a harness memory-width
mistake: memory snapshots used None, interpreted as untyped. The corrected
snapshots use `Some (8*2^64)`, exactly arm8typctx. The translator and oracle
were unchanged. Initial mock test failures in log03 were corrected before
final tests; that early shell ended with cat and did not capture unittest's
exit, so it is not a success record.

The full high-address kernel harness attempt (log17,exit130) was stopped
by SIGINT to only the verified e10 Dune PID665732. The existing Stdlib
N.shiftr is defined as Pos.iter div2 and makes actual getmem shifts near
2^64 impractical to reduce. No other process was signaled. Final Rocq
fixtures use882 low-effective-address cases, retaining wrapped/high GPR
base/index inputs and negative writeback. Python's4536-case IL/byte-array
matrix still covers nonzero memory across modular wraps and high addresses.
The final compile makes no kernel-certification claim for those Python-only
high-effective-address cases. Final source still has the full raw-derived IL.
Log20 failed because stricter named-slice metadata checking exposed a missing
D64 entry in the fake language; the adapter was corrected, actual Ghidra
metadata replay and final log23 pass. No IL changed in that correction.

Log25 completed all882 isolated finite cases but failed the final synthetic
RET check because its expected frame omitted the raw RET copy into PC. That
expected PC value is now12, matching the separately retained raw RET DAG.
The loads and earlier finite results were unchanged.

Final Dune/assumptions results and exact full local commit are recorded below
and in the final external unit audit. No finite result, typing fact or
successful lift is a universal instruction/function correctness proof.

## Local ancestry and publication

Before edits, prepared HEAD was clean, merge-base was the pinned origin, and
`git ls-remote --heads fork refs/heads/llm-proofs/e10-arm-neon-lifts` exited0
with empty output. Only the new prepared branch was renamed; the only import
was `git merge --ff-only a3a80d011dc91d51b163b9d68c33ef92ea40635b`.
ALLOWED-ANCESTRY.json records all eight exact prerequisite commits before
implementation. Logs01 and final audits retain full origin..HEAD logs and
diff stats. Only this unit's scoped commit may follow the assigned forest.
No fork branch ancestry, other branch changes, push, PR, comment, remote
mutation or branch deletion. Future publication needs Charles's explicit
unit approval and would be CharlesDardaman/Picinae ->
CharlesAverill/Picinae:llm_generated_proofs. Other units' approvals do not apply.

## Final full build and assumptions

Final full .vo build (log28), exit0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'export PROOF_MEMORY_KB=2000000; ulimit -v 2000000; ulimit -s 65536; dune build --build-dir=/home/charles/code/friends/.toolchains/e10-arm-neon-lifts/build --cache=disabled -j1 --display short @all'
```

This covers every selected earlier core/scalar/proof target and the new
`Examples/claude/lifter/neon_loads/e10_neon_loads.vo`; full .vo mode, no
.vos shortcut, cap raise or pending Dune verification.
Rocq9.1.1, OCaml4.14.2, Dune3.22.2, assembler2.42 verified in log30.

Raw Print Assumptions (log31), exit0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env bash notes/e10-arm-neon-lifts/print-assumptions.sh
```

All31 new facts queried. Twenty-nine finite facts (`finite_execution_0`
through `_27`, `finite_closed_execution`) each print verbatim
`Closed under the global context`. Both typing facts (`welltyped`,
`closed_welltyped`) print verbatim:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Inherited FE is the existing Picinae typing-automation dependency. No new
admission, Axiom or Parameter declaration was added. Assumptions for universal
instruction/function/hardware correctness: N/A, no such theorem was attempted.
See ASSUMPTIONS.txt and full unabridged log31. All1175 protected baseline files
match assigned forest bytes; final source/protection/ancestry checks pass in
log32. Partial **function** coverage is intentional; this load-only engineering
gate is validated. Publication remains local-only.

Staged source whitespace check passes in log33. Unmodified raw Ghidra and
Print Assumptions logs are deliberately excluded: their native formatting
contains trailing spaces. The initial all-file staged whitespace check
returned2 for those raw logs; their original bytes are retained.
