Picinae Ltac2 migration and benchmark report

Scope

The default psimpl entry points and x86_step, x64_step, arm7_step, arm8_step,
and r5_step now execute Ltac2 orchestration. Existing example sources are
unchanged. Classic proof mode is retained explicitly after importing Ltac2.

Picinae_simplifier_base.v retains the original four implementations with
_ltac1 suffixes and adds psimpl_ltac1 notations for all four argument forms.
The default implementation manages the reflective AST lifetime, simplification
stages, expression replacement, hypothesis/local-definition fallback, and
cleanup through Ltac2. Signature conformance uses transparent <:, preserving
the implementation adapters when passed through ISA functor signatures. The PSIMPL_BASE signature retains default Ltac1
implementations for third-party implementations; Picinae_Simplifier_Base
redefines those entries to call its checked Ltac2 implementation bodies.
Rocq rejects Ltac2 definitions inside module types, so these bodies live
in the implementation module rather than in PSIMPL_BASE.

Picinae_ISA.v retains an independent ISA_step_ltac1 call graph. The Ltac2
version owns sequencing, invariant selection, symbolic-execution iteration,
conditional branching, repeated hypothesis cleanup, and per-goal dispatch.
Explicit Control.enter calls preserve Ltac1's semicolon application to each
resulting goal. Each architecture exports its own *_step_ltac1 alias.

This is a hybrid migration. Remaining Ltac1 boundaries are:

- find_containing_term and psimpl_mark_all_in: occurrence-sensitive marking of
  terms inside local definitions, including type unification and pattern
  abstraction. These are retained intact to preserve occurrence selection.
- The PSimplifier higher-order dispatcher and v1.1 AST parsers, bound/context
  annotation, and reflective theorem application. They exchange untyped terms
  with scoped evars, which must be introduced by epose in the original context.
  Keeping the existing dispatcher also preserves user-selected simplifiers.
  A complete port would require restructuring PICINAE_SIMPLIFIER_V1_1, whose
  tactic bodies currently live inside a module type, and changing this untyped
  interface. This is a deliberate compatibility boundary, not a claim that
  Ltac2 cannot implement reflection or scoped evars.
- Functional interpreter setup (populate_varlist), typeability checks, the
  replaceable ignore_vars and simpl_memaccs hooks, and trace generalization.
  The native step_stmt pipeline retains reflective compute and its dependent
  context edits through Ltac1, while handling stage dispatch and unknown-value
  abstraction in Ltac2. Ignored-variable search and memory-access decomposition
  also have native Ltac2 control flow.
- Some primitive context edits (remember with wildcard uconstr, dependent
  destruct/subst/rewrite) are invoked through explicit ltac1 quotations.

The Gallina AST transformation/evaluation code, soundness proofs, and reduction
strategies are unchanged. No new Admitted, admit, or Axiom was introduced.
The code does not replace computation with Ltac2 rewriting; it preserves the
reflective engine and its existing compute/lazy reduction choices.

Build and reproduction

Baseline: a87fc67dd1bafd4eccb35812f6459f51e4d79e3b, the starting master
snapshot. Baseline evidence in baseline/results.json confirms that all six
lifted files and six partial-correctness proofs build. Two examples fail before
migration: riscv_addloop_proof.v:148 (startof_prefix application) and
riscv_cfi.v:490 (missing VaM). Their logs are preserved in baseline/.
The source was unpacked independently using:
  mkdir -p /tmp/picinae-ltac2/baseline-9.1.1
  git archive a87fc67dd1bafd4eccb35812f6459f51e4d79e3b | tar -x -C /tmp/picinae-ltac2/baseline-9.1.1

All final validation uses the user-provided wrapper:
  /home/charles/code/friends/.toolchains/picinae-env
It executes opam exec --switch=picinae --set-switch with OPAMROOT pointing to
/home/charles/code/friends/.toolchains/opam. This is a local opam environment,
not a container. The wrapper preserves the working directory. Rocq is 9.1.1,
OCaml is 4.14.2, and rocq-stdlib is 9.1.0. Matching installed Ltac2 .v sources
were copied to /tmp/picinae-ltac2/Ltac2-9.1.1 and read for API checks.
The wrapper digest is recorded in metadata.json.

The earlier isolated /tmp toolchain builds and partial timing runs were stopped
and excluded after the user's toolchain update. They are not final evidence.

The baseline library build passed via the wrapper in its scratch directory:
  /home/charles/code/friends/.toolchains/picinae-env make -j4
The migrated tree passed from clean:
  /home/charles/code/friends/.toolchains/picinae-env make clean
  /home/charles/code/friends/.toolchains/picinae-env make -j4
This includes Tests/automation.v: all four psimpl forms, wildcard occurrence
selection, local-definition contents, bound-sensitive simplification, store
reads, legacy entry points, invariant handling, and symbolic Nop interpretation
through every ISA. Direct Ltac1 calls passing a hypothesis as a variable term
and tactic notations passing it as an identifier are both supported.

The root _CoqProject does not include Examples. All seven *proof.v files are
therefore compiled separately to establish baseline eligibility, including
memset's functional-correctness proof and the RISC-V add-loop proof.
riscv_cfi.v is a rewriter-safety development rather than an ISA-step partial-
correctness example. Commented _CoqProject references to i386_wcsnlen files do
not correspond to files present in this snapshot.

Machine: TheAlien, Intel Core Ultra 9 285K, 24 logical CPUs, x86_64,
WSL2 Linux 5.15.167.4-microsoft-standard, glibc 2.39.

Final benchmark command, from the migrated worktree:
  /home/charles/code/friends/.toolchains/picinae-env python3 tools/benchmark_ltac.py --baseline /tmp/picinae-ltac2/baseline-9.1.1 --output /tmp/picinae-ltac2/final-bench --runs 3

Each subprocess runs from its source directory, using:
  picinae-env /usr/bin/time -f 'wall=%e user=%U sys=%S rss_kb=%M' rocq compile -R TREE Picinae -Q SOURCE_DIRECTORY '' SOURCE_FILE
metadata.json contains fully expanded commands, version, source digests, and
all compilation outcomes. runs.json records the timed samples and load averages
before/after each compile. The table uses the inner /usr/bin/time compiler wall
clock; outer elapsed time includes opam wrapper startup and is recorded too.

Comparison processes are sequential. Backend order alternates by round. There
are at least three successful samples per backend per eligible file. A backend
with a sample more than 15% from its median is rerun twice; all successful
samples then contribute to the median. No example proof sources are changed.
The scratch Ltac1 copies add only these selectors after the architecture import:
  Ltac psimpl_goal ::= psimpl_goal_ltac1.
  Ltac psimpl_hyp h ::= psimpl_hyp_ltac1 h.
  Ltac psimpl_exp_goal e ::= psimpl_exp_goal_ltac1 e.
  Ltac psimpl_exp_hyp e h ::= psimpl_exp_hyp_ltac1 e h.
  Ltac ISA_step ::= ISA_step_ltac1.
The scratch Ltac2 copies are byte-for-byte identical to the original examples.

Separate instrumented compiles use Set Ltac Profiling and
Set Ltac2 In Ltac1 Profiling before the source and Show Ltac Profile afterward.
The final measurement job will record its selected profile targets. Existing
Time/time instrumentation in the examples also appears in the raw logs. Profile
overhead is excluded from all uninstrumented medians.

Research references

https://rocq-prover.org/docs/metaprogramming-ltac2#what-is-ltac2
https://rocq-prover.github.io/platform-docs/metaprogramming/ltac2/tutorial_ltac2_for_ltac1_users.html
https://rocq-prover.github.io/platform-docs/metaprogramming/ltac2/tutorial_backtracking.html
https://github.com/rocq-prover/rocq/tree/V9.1.1/user-contrib/Ltac2

Changed files and local commits

Picinae_simplifier_base.v: retained Ltac1 interface, native Ltac2 orchestration,
and adapters accepting both Ltac1 hypothesis representations.
Picinae_ISA.v: independent original step call graph and native execution helpers.
Picinae_i386.v, Picinae_amd64.v, Picinae_armv7.v, Picinae_armv8.v,
Picinae_riscv.v: explicit legacy step aliases.
Tests/automation.v, Tests/isa_steps.v, Tests/psimpl_boundaries.v and
_CoqProject: regression checks
included in make.
tools/benchmark_ltac.py: sequential baseline, comparison, and profiling harness.
Benchmarks/ltac2/: report and evidence.

69b9915 Port simplifier and ISA step orchestration to Ltac2
08b91ec Port symbolic interpreter helper control flow and harden Ltac bridges

No push or PR creation was performed. No .github PR template is present in
the starting repository tree; the draft description follows the repository's
sentence-case commit/title style and states scope, validation, and limitations.

The hardened harness also verifies explicit backend routing on all architectures
with poisoned/sentinel entry points before collecting comparisons. It checks
source and library fingerprints between samples, records command outcomes and
full profile flags, prevents concurrent harness processes, and supports
fingerprint-checked --resume. The merged simplifier binding correction is now verified; earlier pre-merge or
fallback-default passes are excluded. Final comparison results are pending.
