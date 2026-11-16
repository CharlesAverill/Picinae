# Codex i386 verification

This directory follows [the CoqEtTu assignment](../README.md). Function lifts,
specifications, proofs, and shared Rocq libraries are under `x86/`.
The completed set contains 23 function proofs with correctness and ABI-return
contracts; 25 functions have reproducible lifts. See [ROADMAP.md](ROADMAP.md)
for coverage, assumptions and outstanding work.

Build with Rocq 9.1.1 from the repository root:

```sh
make -C coqettu/codex core   # if the Picinae prerequisites are not built yet
make -C coqettu/codex
make -C coqettu/codex check # independently recheck compiled proof terms
make -C coqettu/codex smoke # execute checks against the exact 32-bit musl ELF
```

Each Rocq compiler/checker process has an 8 GB virtual-memory limit. No changes to
the repository-wide `_CoqProject` are needed. The default target also typechecks
the preparatory lifts for functions whose correctness proofs are still open.
`check` also verifies the binary hash, global instruction addresses and sizes,
and coverage of every instruction reachable in the disassembly of each lift.
It writes an inventory to `.build/lift_manifest.json`. These checks do not
establish semantic correctness of the lifter.

`x86/audit.v` prints the logical assumptions of the completed correctness and
return theorems. The audit inventory must cover both contracts for every
function proof source. They use Picinae's existing functional-extensionality axiom;
they do not depend on admitted function proofs.

`smoke` requires a compiler with i386 code generation and permission to execute
i386 system calls. It uses musl itself as the program interpreter, disables
compiler builtins, and checks the completed function families, alignment cases,
boundary values, signed wide-character ordering, string mismatch positions,
backwards byte searches, the 32/64-bit first-set-bit functions, and wide fills
with canaries around the destination. The native checks passed
in this workspace; they complement the proofs.

To reproduce the lifts:

```sh
bash coqettu/codex/lift.sh
```

Set `GHIDRA_INSTALL_DIR` to use another Ghidra installation, and optionally set
`COQETTU_GHIDRA_PROJECT_DIR` / `COQETTU_GHIDRA_PROJECT_NAME`. Set
`COQETTU_LIFT_OUTPUT_DIR` to reproduce into a fresh directory for comparison.
The script checks the binary hash, uses strict global-address lifting, and verifies
that every expected
function was freshly emitted, and rejects Ghidra post-script exceptions.
The default project is under `/tmp`; its loss does not lose any proof source.

The shared lifter's committed source is pinned in `lifter_base/` with commit and
file hashes, so concurrent changes elsewhere do not change these lifts. The
Codex-local adapter recognizes Ghidra's exact register-to-register BSF32 graph
and replaces its backward branch with 32 guarded iterations. Other backward
branches remain rejected. `make -C coqettu/codex adapter-check` checks recognition,
rejection cases and scan behavior. The `ffs` family lifts use this adapter;
their functional proofs are tracked separately in the roadmap.

For each completed function, `*_correct` gives the invariant-based partial
correctness theorem for any containing program; `*_returns` states the result,
memory/register frame, saved return address, and ESP adjustment after RET.
Neither theorem claims termination or successful access to concrete machine
memory. The lifted IL and Ghidra's instruction semantics remain trusted inputs.
