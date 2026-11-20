# Selective Rocq builds

The Dune build uses **Dune 3.22**, the **Rocq build language 0.12**, and
**Rocq 9.1.1**. It checks full `.vo` proofs (`mode vo`); it does not use the
proof-skipping `.vos` mode. The existing Makefiles and `_CoqProject` files
remain available and unchanged. Keep Make outputs out of Dune's source tree
when switching build systems; Dune writes its outputs under `_build/`.

Use an existing isolated environment. Do not install dependencies on the host
or modify a shared environment. The campaign's read-only wrapper is:

```bash
env_runner=/home/charles/code/friends/.toolchains/arm-validation/picinae-env
"$env_runner" bash --noprofile --norc -e -c '
  ulimit -v 8000000
  ulimit -s 65536
  dune build --cache=disabled -j1 --display short @core @smoke-x86 @smoke-arm8
'
```

Run commands from the repository root. `@core` builds the fourteen active core
modules listed in `_CoqProject`. `@smoke-x86` builds the existing AMD64 `abs`
lift/proof and its helpers; `@smoke-arm8` does the same for ARM8 `abs`.
`@smoke` combines all three. The explicit module list contains these baseline
files plus the extensions below. `dune build` selects only those modules.
Requesting a single `.vo` builds only its dependency closure, for example:

```bash
"$env_runner" bash --noprofile --norc -e -c '
  ulimit -v 8000000
  ulimit -s 65536
  dune build --cache=disabled -j1 Examples/claude/arm8_abs_proof.vo
'
```

The e15 companion is selected by `@e15-vector-state`. It checks finite state
fixtures, including coexistence with the old ISA. `@smoke-ymm` selects the
existing `strlen_avx2_amd64` lift and its typing theorem; it does not select a
functional correctness proof. The combined e15 validation is:

```bash
"$env_runner" bash --noprofile --norc -e -c '
  ulimit -v 2000000
  ulimit -s 65536
  dune build --cache=disabled -j1 --display short @e15-vector-state @smoke-x86 @smoke-ymm
'
```

The standalone register-layout checks and exact e01 operand inventory replay
are documented in `notes/e15-x86-vector-state/README.md`; they use only Python's
standard library and are separate from Rocq compilation.

For a clean check, run `dune clean` before the capped build command. Disabling
Dune's shared cache avoids importing build results or writing an external
cache. Raise `PROOF_MEMORY_KB` to `13000000` only for a known-heavy file when
using the assumptions helper below. Never work around an unfinished proof by
adding an admission.

## Extending the build for one unit

1. Add the lift, proof, and any missing shared prerequisites to the explicit
   `modules` list in the **root `dune`** file. Use dotted paths, for example
   `Examples.claude.foo_amd64` and `Examples.claude.amd64_foo_proof`.
   Add a new ISA's root module there too when required. Do not use `:standard`
   for the module list or a glob of proof files.
2. Build the exact `.vo` path with `-j1` and a memory cap. `rocq dep` determines
   the order; listing a prerequisite does not certify it has no admissions.
3. Optionally add a root alias whose `deps` list names the exact `.vo` file:

   ```lisp
   (alias
    (name x-foo)
    (deps Examples/claude/amd64_foo_proof.vo))
   ```

   Then build `@x-foo`. Keep expensive units out of `@smoke`.
4. Audit source changes and every exported main theorem's assumptions; save
   both logs under that unit's notes. Review imported helper assumptions too.

There is deliberately one `Picinae` theory with `include_subdirs qualified`.
Its recursive `-R . Picinae` mapping preserves the existing file names,
logical names such as `Picinae.Examples.claude.amd64_abs_proof`, and unqualified
imports such as `Require Import Picinae_amd64`. Splitting the examples into a
second theory makes Dune use `-Q` for the dependency and breaks these imports.
Do not rewrite existing modules' imports merely to extend the selective build.

## Source and assumptions audits

```bash
base=49956416928e5b6bb3928b54ae33e3b81091f006
python3 tools/audit-proof-source.py --base "$base"
python3 tools/test-proof-audit.py

"$env_runner" bash tools/print-assumptions.sh \
  Picinae.Examples.claude.amd64_abs_proof \
  abs_correct abs_preserves_memory abs_preserves_callee_saved
"$env_runner" bash tools/print-assumptions.sh \
  Picinae.Examples.claude.arm8_abs_proof abs_correct abs_preserves_memory
```

The source auditor inventories all tracked and unignored `.v` files at the
base and in the working tree, masks nested comments and strings, and fails
if a changed source line contains `Admitted`, `admit`, `Axiom(s)`, or
`Parameter(s)`. Optional file/directory arguments restrict its scope. Existing
tokens are printed with paths and line numbers, including module-interface
parameters; those declarations are not automatically unproved dependencies.
This conservative lexical check is not a Rocq parser or an assumptions
certificate. It cannot determine which theorem uses a baseline admission or
detect its reassignment by editing other lines. Review the diff and inspect
transitive `Print Assumptions` output before claiming completion.

The assumptions helper builds the specified `.vo` target and then compiles a
temporary query containing `Check` and `Print Assumptions` for each named
constant. It uses only `_build/default` as the Picinae load path and removes
its temporary query. It fails on a missing theorem or compiler failure.
The output inventories assumptions; it intentionally does not declare an
axiom acceptable. Check each output against the reviewed library baseline.
An imported admitted lemma disqualifies a proof-completion claim even if the
unit's own source contains no suspicious tokens.

To capture an exact command, stdout/stderr, and its real exit status:

```bash
bash tools/record-command.sh notes/my-unit/source-audit.log \
  python3 tools/audit-proof-source.py --base "$base"
bash tools/record-command.sh notes/my-unit/assumptions.log \
  "$env_runner" bash tools/print-assumptions.sh \
  Picinae.Examples.claude.amd64_abs_proof abs_correct
```

The recorder returns the underlying command's exit status, including failures.
The e00 build evidence and the honest baseline inventory are in
[`notes/e00-build/README.md`](notes/e00-build/README.md). These checks establish
build and proof-kernel behavior for the selected IL modules. They do not
establish lifter soundness, termination, ABI completeness, or binary-level
functional correctness.
