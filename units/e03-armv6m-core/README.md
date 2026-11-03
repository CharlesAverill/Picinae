# e03-armv6m-core

Engineering import and regression validation; final Dune verification is pending
integration with e00-build. No function correctness proof or binary-to-IL
refinement theorem is claimed.

## Isolation rule from Charles (unchanged)

HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

The shared wrapper was reused read-only, including its isolated Ubuntu ARM
binutils 2.42 overlay. The final test run used Python 3.12.3 in the new per-unit
venv `/home/charles/code/friends/.toolchains/e03-armv6m-core/venv`, created with
`/usr/bin/python3 -m venv --without-pip` at that path. No Python packages were
installed. Earlier successful regression runs used the preexisting isolated
Miniconda Python 3.12.9; final evidence uses the per-unit venv.

## Provenance and ancestry

- Worktree: `/home/charles/.t3/worktrees/Picinae/t3-7a4e751d`.
- Assigned branch: `llm-proofs/e03-armv6m-core`; renamed only the delegate's new
  `t3/7a4e751d` branch after the read-only collision check below.
- Exact parent/base: `origin/llm_generated_proofs` at
  `49956416928e5b6bb3928b54ae33e3b81091f006`.
- Exact source: `origin/timing` at
  `4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`.
- `git ls-remote --heads fork refs/heads/llm-proofs/e03-armv6m-core` returned
  exit 0 and empty stdout before rename. The first sandboxed attempt failed DNS
  (128); the authorized unsandboxed read-only retry succeeded.
- Initial HEAD and merge-base both equaled the exact base. Initial
  `git log --oneline origin/llm_generated_proofs..HEAD` and
  `git diff --stat origin/llm_generated_proofs...HEAD` were empty. See
  [ancestry-before.log](logs/ancestry-before.log).
- No prerequisites. Only this unit's local commit is allowed above base. No
  timing merge, fork ancestry, remote mutation, push, PR, or remote comment.
- Final SHA/log/diff audit is returned with the deliverable, and saved externally
  only in the assigned `units/e03-armv6m-core/` evidence directory.

| Source path | Upstream Git blob | Upstream SHA256 |
|---|---|---|
| Picinae_armv6m.v | `8e039f4baeec1b2e6f4b67775be4749e746ca666` | `5522ac2c857b2a046a2ff6282111e7144601e21b78806a1207044cbed56fa652` |
| armv6m_lifter.sh | `0f43b052c0ae779eef409b28c3b798eafcb76055` | `12b8a82bad6c2fea16c5be697dc85e2c528ddf86ba08b5eca1c882f98de44a38` |

The two files were read using `git show <source>:<path>`. The unmodified upstream
ISA and existing main welltyped proof compiled on the current core; see
[import-compile.log](logs/import-compile.log). **No upstream core dependency hunk
was necessary.** Its dependencies are already present: core, theory, statics,
functional interpreter, simplifier base/v1_1, ISA automation, and Rocq Stdlib.
No timing proof library or data was imported.

Each change from the source ISA is recorded in [isa-upstream.patch](isa-upstream.patch):

1. Replace the broad architectural coverage claim with provenance and the
   explicit model/trusted-boundary limitation.
2. Qualify five Stdlib imports to match the base's Rocq 9 convention.
3. Omit `armv6m_cond_val` and its evaluator theorem, used only by timing models.
   Keep the ordinary condition expressions, decoder, symbolic step automation,
   lifter, and all typing proofs. No instruction semantics or typing proof was
   changed.

The source shell lifter is recorded in [lifter-upstream.patch](lifter-upstream.patch)
relative to the small replacement wrapper. Its disassembly-column extraction
and zero defaults did not establish byte coverage, relocation resolution,
complete out-of-function literal pools, or successful decoding. The new stdlib
Python helper reads actual ELF section bytes and mapping symbols, cross-checks
objdump instruction bytes, applies conservative encoding checks, and emits a
finite instruction-entry program plus kernel-checked decode and typing facts.
It supports linked ELF32 little-endian ARM ET_EXEC with preserved symbols;
unsupported/unknown instructions, ARM-state code, missing bytes, relocations,
and stripped inputs fail without any Coq stdout. System approximations have no
opt-in switch.

## Build and validation

Commands below ran from the worktree root. Every Rocq check had
`ulimit -v 8000000` (8,000,000 KiB virtual memory), and Make used `-j1`.
`E` denotes `/home/charles/code/friends/.toolchains/arm-validation/picinae-env`;
`P` denotes `/home/charles/code/friends/.toolchains/e03-armv6m-core/venv/bin/python`.
These are command abbreviations for documentation, not shell environment setup.

| Exact command (expanding E/P as above) | Exit | Evidence |
|---|---|---|
| `E bash -c 'ulimit -v 8000000; make -j1 Picinae_ISA.vo'` | 0 | [base-make.log](logs/base-make.log) |
| `E bash -c 'ulimit -v 8000000; make -j1 Picinae_simplifier_v1_1.vo && rocq c -R . Picinae Picinae_armv6m.v'` (unmodified source ISA) | 0 | [import-compile.log](logs/import-compile.log) |
| `E bash -c 'ulimit -v 8000000; make -j1 all'` | 0 | [make-all.log](logs/make-all.log) |
| `PYTHON=P E bash -c 'ulimit -v 8000000; make -j1 check-armv6m'` | 0 | [check-armv6m.log](logs/check-armv6m.log) |
| `E bash -c 'ulimit -v 8000000; rocq check -silent -R . Picinae Picinae.Picinae_armv6m'` | 0 | [rocq-check.log](logs/rocq-check.log) |

The harness records actual assembler, objdump, Python versions/executable, and
ELF SHA256. It runs these commands without installing anything:

```sh
arm-linux-gnueabi-as -mcpu=cortex-m0 -mthumb -o tests/armv6m/generated/snippets.o tests/armv6m/snippets.s
arm-linux-gnueabi-ld -Ttext=0x1000 --entry=fixture -o tests/armv6m/generated/snippets.elf tests/armv6m/generated/snippets.o
arm-linux-gnueabi-objdump -d -s -t tests/armv6m/generated/snippets.elf
./armv6m_lifter.sh tests/armv6m/generated/snippets.elf fixture_bytes fixture
./armv6m_lifter.sh tests/armv6m/generated/snippets.elf all_bytes
rocq c -R . Picinae tests/armv6m/generated/fixture.v
rocq c -R . Picinae tests/armv6m/generated/all_bytes.v
rocq c -R . Picinae tests/armv6m/Checks.v
"$PYTHON" tests/armv6m/rejections.py tests/armv6m/generated
rocq c -R . Picinae tests/armv6m/generated/Assumptions.v
```

The independently assembled ELF SHA256 is
`e5dea01f8ec2db2a02d2430c3cca463a7bebbec66ade6f1433164ca8dfee7091`.
See [snippets.objdump](logs/snippets.objdump) and the generated-output snapshots
[fixture-output.v.txt](fixture-output.v.txt) / [all-output.v.txt](all-output.v.txt).
The reproducible generated directory is ignored; source assembly and harness
are tracked. The literal word at 0x1010 is deliberately outside the function's
0x10-byte STT_FUNC range and is included in full by function-scoped extraction.
Both the literal pool and the second halfword of BL are excluded as instruction
entries. Missing low/high literal bytes and writable literal sections fail.

Twenty concrete Rocq regression examples cover decode, literal folding,
boundary masking, ADD/SUB/ADC/SBC flags, register shifts at 0/32/255, forward and
backward BL/link values, BX Thumb/fault behavior, and PUSH/POP order/SP/return.
The test-only bounded evaluator uses the existing functional IL interpreter;
its memory access propositions are deliberately not discharged. These are
value regressions, not general execution, memory-safety, ABI/frame, or function
correctness theorems. The shell harness additionally checks 33 strict rejection
cases, each with nonzero exit and zero Coq stdout.

Two early harness attempts failed (Make exit 2) because the test BL offset used
N notation without the required ZArith import; both logs are retained. A
mistyped `rocq chk` command failed (exit 1); the correct `rocq check` succeeded.
The intermediate passing logs are retained separately from the final log.

## Assumptions and trusted boundary

[assumptions.log](logs/assumptions.log) contains verbatim `Check` and
`Print Assumptions` output for every imported ARMv6-M theorem/lemma and every
regression/generated theorem. Each reports `Closed under the global context`,
including:

```text
welltyped_lift_armv6m
     : forall binary : addr -> N,
       welltyped_prog armv6mtypctx (lift_armv6m binary)
Closed under the global context
```

The raw source core has preexisting abstract interfaces/assumptions, untouched
by this unit. None appears in these reported transitive theorem dependencies.
Typing does not establish decoder correctness or architectural fidelity.

- Use the emitted `<name>_prog`, which returns None outside known instruction
  starts. The inherited `lift_armv6m` is total and ignores execution permission,
  alignment, and presence; calling it directly on the raw halfword map bypasses
  the finite boundary and can decode the zero default as MOVS. Similarly,
  `armv6m_prog`/the raw decoder are lower-level models, not strict ELF validators.
- Literal folding assumes pool bytes retain their ELF values throughout use.
  The frontend refuses writable pool sections; ELF flags alone do not prove
  runtime immutability or correct loading. Runtime permissions, address layout,
  and absence of code modification remain caller obligations.
- ELF byte extraction, mapping symbols, symbol sizes, binutils, conservative
  Python acceptance checks, and the ISA translation remain in the binary-to-IL
  trusted base. The generated decoder check rules out T_Invalid on emitted
  entries; it is not a proof that the decoder follows the ARM manual.
- No asynchronous interrupts, exception entry/return stacking, NVIC, MMIO device
  behavior, privilege levels, CONTROL, PRIMASK, PSP/MSP banking, or scheduling
  interleavings are modeled. The inherited CPS instructions are Nop and MRS/MSR
  only approximate APSR/MSP/Thread-mode state (other reads Unknown or zero,
  other writes Nop). The strict frontend rejects **all** CPS and MRS/MSR.
- Barriers are Nop in the inherited sequential IL; memory ordering and device
  effects are absent. DMB/DSB/ISB and SEV/WFE/WFI/YIELD are rejected. Only a real
  NOP is accepted; unallocated hints are rejected.
- SVC/BKPT/invalid decode use coarse Raise exceptions in the raw model; no
  handler execution or fault escalation is supplied. The strict frontend
  rejects these encodings. BX/BLX/POP may still encounter EXC_RETURN at runtime:
  callers must exclude exception-return tokens and require ordinary Thumb
  destinations. These paths cannot justify a FreeRTOS PendSV/SVC handler proof.
- Aligned normal RAM/stack access, valid permissions, valid branch targets and
  well-formed register operands remain preconditions. The IL does not reproduce
  all ARM alignment, bus-fault, SP alignment-bit, or unpredictable behavior.
  The frontend conservatively rejects known empty-list, high-CMP and STM
  base-in-list unpredictable cases. Raw STM stores the original base even in
  the architecturally UNKNOWN case; it is not safe to bypass these checks.

## Follow-on work

- e00/e05 integration: add this ISA, generated finite programs and the regression
  target to the reviewed Dune setup; run actual `dune build -j 1` targets. There
  are no Dune files at this exact base; this unit edits none of the shared Dune
  files being established by e00. Final Dune verification remains pending.
- e05: consume e04's fully linked Cortex-M0 ELF, preserve mapping symbols/sizes,
  manifest immutable pool bytes, real call edges, data layout and ABI/frame
  obligations. Strict system-instruction failures are blockers to model, not
  instructions to silently skip.
- Separate engineering/proof units: architecture refinement and broader
  differential instruction validation; explicit privilege/PRIMASK and banked-SP
  model; exception entry/EXC_RETURN and interrupt boundaries; barriers/MMIO.
  Critical-section and context-switch proofs require these before correctness
  claims about FreeRTOS port handlers.
