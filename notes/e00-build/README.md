# e00-build evidence

Unit: `e00-build` (engineering, no prerequisites). Branch:
`llm-proofs/e00-build`. Worktree:
`/home/charles/.t3/worktrees/Picinae/t3-6b751a59`.

Pinned base: `49956416928e5b6bb3928b54ae33e3b81091f006`, equal to the local
`origin/llm_generated_proofs` at the start. Read the campaign plan and assigned
row before implementation. No commits were imported from a fork or from
`timing` (`4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6`). No function proofs,
lifts, specifications, core lemmas, Makefiles, or `_CoqProject` files changed.

> HARD RULE FROM CHARLES, pass through unchanged in your work: install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

No dependencies were installed. The existing wrapper was reused read-only;
versions and executable locations are recorded in [06-toolchain.log](logs/06-toolchain.log).
The audit scripts use the already available Python standard library and Bash.
Final validation disables Dune's shared cache and uses only this worktree's
`_build` directory. No shared campaign plan/status or toolchain files changed.

## Ancestry and branch audit

Before any implementation, `HEAD`, `origin/llm_generated_proofs`, and
`git merge-base origin/llm_generated_proofs HEAD` all returned the full pinned
base above. `git merge-base --is-ancestor <pinned-base> HEAD` returned 0;
`git log --oneline origin/llm_generated_proofs..HEAD` and
`git diff --stat origin/llm_generated_proofs...HEAD` were empty.

The initial sandboxed `git ls-remote --heads fork
refs/heads/llm-proofs/e00-build` returned 128 (DNS unavailable). The authorized
network retry returned 0 with empty stdout **before** branch rename. Renaming
only the prepared local branch required filesystem escalation because shared
Git metadata is outside the writable workspace. The prepared branch had been
named `t3/6b751a59` on entry and then `t3/selective-dune-build` by the thread
environment before the rename. Its HEAD was rechecked at the pinned base.
`git branch -m llm-proofs/e00-build` returned 0 under escalation. No other
branch was renamed, created, removed, or based on a fork.

[07-base-audit.log](logs/07-base-audit.log) repeats the base audit after the
rename, before the unit commit. [08-fork-collision-check.log](logs/08-fork-collision-check.log)
records another successful empty read-only remote collision check. No remote
mutation, push, PR, or comment occurred. Future publication still requires
Charles's approval; direction would be `CharlesDardaman/Picinae` to
`CharlesAverill/Picinae:llm_generated_proofs`.

## Build and harness

[BUILDING.md](../../BUILDING.md) gives exact isolated build commands, individual
targets, how to extend the explicit module list for a unit, source audits,
and transitive assumptions queries. The root theory preserves the recursive
`-R . Picinae` convention and builds full `.vo` objects. Fourteen core modules
and six selected example modules are listed; there are no proof globs.

All proof compilation used `ulimit -v 8000000`, `ulimit -s 65536`, and Dune
`-j1`. The query helper applies these caps itself. No 13 GB exception was needed.

| Log | Command/result |
| --- | --- |
| [01](logs/01-dune-smoke.log) | Initial extension `rocq 1.0`: exit 1, not supported by the installed binary. Changed to supported `rocq 0.12`. |
| [02](logs/02-dune-smoke.log) | Separate example theory: exit 1; Dune's `-Q` dependency mapping broke existing unqualified imports. Replaced with one explicitly selected recursive theory. Core compilation itself completed in this run. |
| [03](logs/03-dune-smoke.log) | `dune build -j1 --display short @smoke`: exit 0 after the mapping fix. |
| [04](logs/04-audit-tests.log) | Initial four audit tests: exit 0. |
| [05](logs/05-baseline-source-audit.log) | Whole-repo source inventory against pinned base: exit 0; no new suspicious source tokens. |
| [06](logs/06-toolchain.log) | Toolchain versions and paths: exit 0. |
| [07](logs/07-base-audit.log) | Base ancestry audit and empty `.v` diff: exit 0. |
| [08](logs/08-fork-collision-check.log) | Read-only remote branch collision check: exit 0, empty stdout. |
| [09](logs/09-clean-build.log) | `dune clean; dune build --cache=disabled -j1 --display short @core @smoke-x86 @smoke-arm8`: exit 0. All twenty modules compiled from clean outputs without the shared cache. |
| [10](logs/10-harness-tests.log) | Bash syntax and five regression tests, including recorder propagation of exit 23: exit 0. |
| [11](logs/11-x86-assumptions.log) | AMD64 main, memory and callee-saved theorem queries: exit 0. |
| [12](logs/12-selected-objects.log) | `python3 notes/e00-build/check-selection.py`: exit 0; exactly fourteen core and six selected example `.vo` files, no excluded proof objects. |
| [13](logs/13-arm8-assumptions.log) | ARM8 main and memory theorem queries: exit 0. |
| [14](logs/14-missing-theorem-negative.log) | Deliberately missing ARM8 theorem: expected exit 1; compiler failure propagated and recorded. |
| [15](logs/15-extensionality-provenance.log) | Installed Stdlib axiom declaration/hash and existing core imports: exit 0. |

Logs 01 and 02 used the same exact invocation (the Dune source differed):

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -c \
  'ulimit -v 8000000; ulimit -s 65536; dune build -j1 --display short @smoke'
```

Logs 03 onward include shell-escaped exact commands, cwd, combined stdout and
stderr, and the real exit status. Warnings from existing sources are retained.
Raw compiler output is retained verbatim, including Rocq's trailing whitespace
in one printed type; whitespace checks exclude the captured `logs` directory.
The negative audit fixtures are created in a temporary local Git repository
and removed; they are not Rocq source additions to Picinae.

## Baseline inventory and limits

The whole-repo lexical audit selected 313 `.v` files and found the same counts
in base and working tree: **7 `Admitted`, 1 `admit`, 89 `Parameter`, no `Axiom`
or plural variants**. New counts are empty. Exact source locations are saved
in [05-baseline-source-audit.log](logs/05-baseline-source-audit.log).

Existing admissions, all excluded from the selective build:

- `amd64_isinfl_proof.v:107`;
- `amd64_memmove_avx_nt_proof.v:402,693`;
- `amd64_memset_avx2_proof.v:275`;
- `amd64_pthread_mutex_lock_proof.v:785`;
- `amd64_rand_r_proof.v:148`;
- `zz_s85.v:116`, plus its `admit` tactic at line 115.

These files are under `Examples/claude`. Their presence prevents any blanket
claim that the repository is admission-free. The 89 `Parameter` declarations
are preexisting module signatures (architecture, word/list representation,
statics, interpreter, simplifier, and separation-logic interfaces). A signature
declaration is not by itself evidence of an unproved concrete lemma. The
source audit distinguishes baseline from additions but does not decide which
module implementations discharge a signature; transitive assumptions output
is the relevant evidence for the selected theorem.

The existing main theorems
`Picinae.Examples.claude.amd64_abs_proof.abs_correct` and
`Picinae.Examples.claude.arm8_abs_proof.abs_correct` both produce exactly this
`Print Assumptions` output (verbatim):

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Their memory frame theorems, and the AMD64 callee-saved frame theorem, each
produce `Closed under the global context`. See the complete type/assumptions
queries in logs [11](logs/11-x86-assumptions.log) and
[13](logs/13-arm8-assumptions.log). No imported admitted lemma appears in these
outputs. Main-theorem assumptions are **not empty**: functional extensionality
is an existing Stdlib axiom, declared at line 26 of the installed
`Stdlib/Logic/FunctionalExtensionality.v`, already imported by
`Picinae_theory.v:39`, `Picinae_finterp.v:40`, and
`Picinae_simplifier_v1_1.v:39`. Its source SHA256 is
`ab45c777fbdfe93fc961d9d8bdd907a749fb41b783d5eea61bc53144ae3e02da`.
The exact installed declaration, path and hash are in
[15-extensionality-provenance.log](logs/15-extensionality-provenance.log).
This is inherited library trust, not a new e00 admission or axiom.

The smoke proofs and lifts are unchanged sources at the pinned base:

- AMD64: `Examples/claude/abs_amd64.v`, `amd64_abs_proof.v`, `amd64_common.v`.
  The existing proof header identifies glibc 2.35-0ubuntu3.12, `abs` at
  `0x145dd0`, SHA256
  `9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`.
- ARM8: `Examples/claude/abs_arm8.v`, `arm8_abs_proof.v`, `arm8_common.v`.
  The existing proof header identifies AArch64 glibc 2.35-0ubuntu3.15, `abs`
  at `0x13d810`; the campaign records SHA256
  `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.

Those are inherited provenance statements, not fresh binary/hash/lifter
validation. This engineering unit neither adds nor repairs a theorem. It
checks existing IL partial-correctness and frame theorems without expanding
their specifications. It adds no new satisfiability, termination, ABI, lifter
soundness, or binary functional-correctness evidence.

Follow-on: engineering units can add explicit ISA/lift modules and per-unit
aliases as documented; proof units must query each exported main theorem and
review imported assumptions. Retain the baseline distinction and never count
a successful lift/typecheck as a functional-correctness proof.

No build blocker remains for this unit. Dune verification is complete;
preexisting admissions and the library assumption above remain documented
baseline limitations. Only this unit's local commit is allowed above the
pinned base. The final full SHA, post-commit merge-base, origin-to-HEAD log,
diff stat, and clean status are returned in the handoff audit. No remote write
is authorized by this handoff.
