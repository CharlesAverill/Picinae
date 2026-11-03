Picinae Ltac2 migration and benchmark report

Scope and compatibility

The four existing forms (psimpl, psimpl in H, psimpl e, psimpl e in H) now
enter Ltac2 orchestration through Classic-mode adapters. Wildcard expression
patterns remain unelaborated until occurrence selection. The architecture
notations i386_psimpl, amd64_psimpl, arm7_psimpl, arm8_psimpl, and r5_psimpl
retain the same forms. Existing Examples sources are unchanged.

The five ISA aliases select their own architecture even when loaded together:
  Architecture   Default       Retained Ltac1      Module suffix
  i386           x86_step      x86_step_ltac1      i386
  amd64          x64_step      x64_step_ltac1      amd64
  armv7          arm7_step     arm7_step_ltac1     arm7
  armv8          arm8_step     arm8_step_ltac1     arm8
  riscv          r5_step       r5_step_ltac1       RISCV

psimpl_ltac1 provides all four simplifier forms. The four psimpl_*_ltac1
implementations and ISA_step_and_simplify_ltac1, ISA_invhere_ltac1,
ISA_invseek_ltac1, and ISA_step_ltac1 retain independent Ltac1 control flow;
the legacy ISA path calls the explicit legacy simplifier entries. These paths
share the existing reflective engine and ISA hooks, not the new controllers.
The modules set Default Proof Mode "Classic" after importing Ltac2.

What moved, and what remains

Picinae_simplifier_base.v moves fresh-name allocation, AST lifetime/stage
sequencing, expression-type dispatch (N/address/memory, bool, store), universal
fallback, hypothesis/local-definition fallback, replacement, and cleanup into
Ltac2. Control.enter handles the multiple or zero goals supplied by Classic
sequencing. picinae_hyp_ident accepts identifiers from hyp notation, variable
constr terms from direct Ltac1 calls, and named introduction patterns; other
terms/patterns fail. This also supports the ISA helper's hypothesis argument.

Picinae_ISA.v moves invariant selection, instruction iteration, conditional
branches, symbolic N.iter stopping, stale-hypothesis cleanup, ignored-variable
search, unknown-value abstraction, and memory-access decomposition into Ltac2.
The statement controller dispatches interpreter setup/reduction side goals.
Explicit Control.enter continuations preserve Ltac1 semicolon behavior after
branching hooks. Duplicate memory facts are projected away; dependent goals
that block projection/clearing stop decomposition as before.

The implementation deliberately retains these Ltac1 boundaries:

- find_containing_term and psimpl_mark_all_in select occurrences inside local
  definition values using type unification, pattern abstraction, and marking.
  Keeping them preserves which nested N/bool/store expression is selected.
- The replaceable PSimplifier dispatcher and v1.1 AST parsers, context/bound
  annotation, reflective theorem application, and reduction remain intact.
  They return untyped terms containing scoped evars, introduced by epose in
  the original proof context. Elaborating these as constr too early changes
  that interface. The v1.1 tactic bodies also live in a module type; a full
  port would require restructuring it. Gallina AST transformations/evaluators
  and their soundness proofs are computation/proofs, not Ltac1 orchestration,
  and are unchanged. Existing compute/lazy/cbv choices remain unchanged.
- populate_varlist and step_precheck retain interpreter context construction
  and typeability checks. Ltac1 quotations perform reduce_stmt application,
  compute, and dependent destruct/subst/rewrite/remember edits. In particular,
  remember accepts the existing wildcard uconstr patterns without early typing.
- ignore_vars, simpl_memaccs, generalize_trace, and the public psimpl_goal /
  psimpl_hyp hooks remain dynamically resolved Ltac1 calls. This preserves
  architecture-specific memory handling and user ::= overrides after functor
  application. Frame-generalization helpers and unrelated tactics are outside
  this migration. Native execution does not call the legacy step_stmt,
  abstract_ignored_vars, or destruct_memaccs controllers.

These are compatibility boundaries, not limitations of Ltac2 reflection.
PSIMPL_BASE retains Ltac1 defaults for third-party implementations. Rocq 9.1.1
does not accept Ltac2 definitions inside module types, so checked Ltac2 bodies
live in Picinae_Simplifier_Base. Its signature check uses <: PSIMPL_BASE IL:
the sealing form : PSIMPL_BASE IL exported signature defaults and silently
bypassed the new adapters through functor parameters. The transparent check
preserves those adapters. Boundary tests and harness default-backend guards
exercise this routing rather than accepting a successful legacy fallback.

Observed regression behavior matches the retained paths: wildcard selection,
local-definition simplification, bound-sensitive simplification, rollback and
cleanup, branching hooks, invariants, unknowns, memory facts, and architecture
aliases. The known local-definition limitation is preserved: if a later local
definition refers to the target, psimpl in target can fail while attempting to
clear/rebuild it. Tests/psimpl_boundaries.v checks failure restores the context.
The six baseline-building proofs remain the compatibility targets without
source edits; final per-backend compilation outcomes belong to the measurement
pass below. No new Admitted, admit, or Axiom is introduced by this migration.

Committed validation and baseline eligibility

Original master: a87fc67dd1bafd4eccb35812f6459f51e4d79e3b.
The wrapper-built snapshot is /tmp/picinae-ltac2/baseline-9.1.1.
baseline/results.json records successful compilation of all six lifted modules
and these six proof files:
  arm7_memset_proof.v       arm7_strlen_proof.v
  arm8_strcasecmp_proof.v   i386_strcmp_proof.v
  i386_strlen_proof.v       i386_wcsspn_proof.v
memset's main theorem is named memset_functional_correctness; the harness
measures complete proof-file compilation, including auxiliary lemmas.

Two examples already fail on original master under this wrapper:
  riscv_addloop_proof.v:148: startof_prefix cannot apply to the hypothesis.
  riscv_cfi.v:490: VaM is absent from the environment.
Their full logs are in baseline/. They are excluded, not repaired by this
migration. CFI is a rewriter-safety development, not a partial-correctness timing
target. _CoqProject excludes Examples, so root make alone cannot establish
example eligibility; the harness checks every Examples/*.v in dependency order.
Commented i386_wcsnlen references have no corresponding files in this snapshot.

Committed validation/clean.log and validation/clean-build.log record a clean
root build, including Tests/automation.v, Tests/isa_steps.v, and
Tests/psimpl_boundaries.v. The last two poison opposite-backend controllers,
exercise signature substitution/dynamic hooks, and check failure boundaries.
validation/harness-tests.log records all 11 bookkeeping tests passing, including
selection/guard failure, sequential ordering, outlier reruns, timeout process-
group cleanup, resume integrity, locking, and separate profiling. The harness
tests use fake compilers; their timings are not performance evidence.

Toolchain and reproduction

Every build, compile, profile, and measurement must run through:
  /home/charles/code/friends/.toolchains/picinae-env <command>
This is local opam, not a container: opam exec --switch=picinae --set-switch,
OPAMROOT=/home/charles/code/friends/.toolchains/opam. The wrapper preserves the
working directory. The required versions are Rocq 9.1.1, OCaml 4.14.2, and
rocq-stdlib 9.1.0. No installation is required. Earlier /tmp toolchain builds,
pre-merge checks, fallback-default passes, and interrupted preliminary timings
were stopped and discarded; none are final performance evidence.

From the merged worktree, recreate/build the baseline if needed, then validate
current sources before collecting measurements (do not run during collection):
  mkdir -p /tmp/picinae-ltac2/baseline-9.1.1
  git archive a87fc67dd1bafd4eccb35812f6459f51e4d79e3b | tar -x -C /tmp/picinae-ltac2/baseline-9.1.1
  /home/charles/code/friends/.toolchains/picinae-env make -C /tmp/picinae-ltac2/baseline-9.1.1 -j4
  /home/charles/code/friends/.toolchains/picinae-env make clean
  /home/charles/code/friends/.toolchains/picinae-env make -j4
  /home/charles/code/friends/.toolchains/picinae-env python3 tools/test_benchmark_ltac.py

Stop other builds/benchmarks and freeze source/library artifacts. An optional
eligibility/routing-only pass uses a fresh output directory:
  /home/charles/code/friends/.toolchains/picinae-env python3 tools/benchmark_ltac.py --baseline /tmp/picinae-ltac2/baseline-9.1.1 --output /tmp/picinae-ltac2/prepare --phase prepare
Use --phase baseline for eligibility alone. A separate fresh output collects
final samples and profiles (all eligible proofs are profiled by default):
  /home/charles/code/friends/.toolchains/picinae-env python3 tools/benchmark_ltac.py --baseline /tmp/picinae-ltac2/baseline-9.1.1 --output /tmp/picinae-ltac2/final-bench --phase all --runs 3
The harness builds neither library. Output must be outside both source trees.
Baseline .v files and _CoqProject must match --baseline-revision (default above),
and original Examples files/inventories must match between both trees.

This compares retained Ltac1 versus Ltac2 orchestration in the same migrated
libraries; original master establishes eligibility, not the timed Ltac1 library.
Ltac2 copies of every example are byte-identical to the originals. Ltac1 proof
copies insert explicit selectors immediately after the architecture import.
For i386 the complete selector is:
  Ltac PSimpl_i386.psimpl_goal ::= PSimpl_i386.psimpl_goal_ltac1.
  Ltac PSimpl_i386.psimpl_hyp h ::= PSimpl_i386.psimpl_hyp_ltac1 h.
  Ltac PSimpl_i386.psimpl_exp_goal e ::= PSimpl_i386.psimpl_exp_goal_ltac1 e.
  Ltac PSimpl_i386.psimpl_exp_hyp e h ::= PSimpl_i386.psimpl_exp_hyp_ltac1 e h.
  Ltac ISA_i386.ISA_step_and_simplify h ::= ISA_i386.ISA_step_and_simplify_ltac1 h.
  Ltac ISA_i386.ISA_invhere ::= ISA_i386.ISA_invhere_ltac1.
  Ltac ISA_i386.ISA_invseek ::= ISA_i386.ISA_invseek_ltac1.
  Ltac ISA_i386.ISA_step ::= ISA_i386.ISA_step_ltac1.
  Ltac x86_step ::= ISA_i386.ISA_step_ltac1.
Other architectures use the suffix/alias mapping above. The CFI scratch copy
also receives selectors, but its baseline failure excludes it. Separate sentinel
probes verify all four psimpl forms, all four ISA entries, and each alias on all
five architectures. Default-backend probes poison retained entry points while
solving simplifier, invariant, and Nop execution goals; they must pass before
any samples. Sentinel/poison definitions never enter measured sources.

All compiles are sequential, including validation and profiling. Backend order
alternates by round: Ltac1/Ltac2, Ltac2/Ltac1, Ltac1/Ltac2. --runs must be >=3.
If an initial sample differs by more than 15% from its backend/file median,
that backend gets two additional samples; the decision is checkpointed. All
successful samples, including outliers, contribute to the final median. CSV
also identifies final outlier runs. Load averages are recorded before/after
each compile, not used to discard samples or wait for a lower load. A global
per-user lock excludes other harness instances across output directories; it
cannot exclude unrelated external compiler activity.

Each compile runs from its generated source directory with this command shape:
  picinae-env /usr/bin/time -o TIME_JSON -f '{"wall":%e,"user":%U,"sys":%S,"rss_kb":%M,"exit_code":%x}' rocq compile -R TREE Picinae -Q SOURCE_DIRECTORY '' SOURCE_FILE
The actual command uses the full wrapper path. Inner compiler wall time supplies
the medians. outer_seconds includes wrapper/opam/process launch and measurement
work; wrapper_and_launch_seconds is outer_seconds minus compile_seconds. This
is an overhead estimate, not isolated opam startup time; GNU time wall resolution
is 0.01 seconds. Percent change is 100 * (Ltac2/Ltac1 - 1); negative is faster.
Whole-file timings include loading, other tactics, reduction, and kernel checks,
so changes cannot all be attributed to the migrated controllers.

Profiles follow all uninstrumented samples in separate directories/artifacts:
  From Ltac2 Require Import Ltac2.
  Set Default Proof Mode "Classic".
  Set Ltac2 In Ltac1 Profiling.
  Set Ltac Profiling.
  ... selected proof source ...
  Show Ltac Profile.
Both flags are required to expose Ltac2 calls through Ltac1. --profile stem ...
selects a subset (e.g. --profile i386_strcmp_proof); a bare --profile disables
profiles. Keep this option identical on resume. Profile compiles never enter
runs.json or medians.csv and never overwrite measured sources/.vo files.
Existing example Time/time commands remain in raw logs on both backends.

metadata.json records full argument arrays, rendered commands/cwd, return codes,
UTC times, load, machine/CPU/platform, versions/packages/config, and wrapper,
executable, harness, source, and library .vo fingerprints. Source/.vo digests
are checked before samples and at completion. Timeouts (default 1800 seconds)
and interruptions kill the entire compiler process group. Migrated compile
failures stop collection immediately; inspect their recorded logs.

Resume the same experiment by adding --resume to the exact original command.
Successful samples/logs are reused after integrity checks; dependency .vo files
are checked/rebuilt if missing/changed. Interrupted work gets new logs and live
previous compiler groups block resume. Changed revisions, source/.vo files,
harness, wrapper/toolchain, paths, or measurement options reject resume and need
a fresh output directory. --phase may advance baseline -> prepare -> all.

Final performance results: PENDING parent completion. The authoritative final
artifacts will be measurements/medians.csv, measurements/runs.json,
measurements/metadata.json, and measurements/RESULTS.txt, relative to this file.
The measurement job retains raw logs/profiles and their provenance. Fill this
paragraph only after the backend guards pass and all six eligible proofs
complete the required samples/profiles on both backends; report medians,
percent changes, load/outliers, and profile-supported interpretation.
No preliminary timings or performance claim are included here.

Changed files and merged history

Picinae_simplifier_base.v: adapters, independent legacy entries, native controller,
hypothesis conversion, and transparent signature check.
Picinae_ISA.v: independent legacy graph and native ISA/interpreter orchestration.
Picinae_i386.v, Picinae_amd64.v, Picinae_armv7.v, Picinae_armv8.v,
Picinae_riscv.v: retained step aliases.
Tests/automation.v, Tests/isa_steps.v, Tests/psimpl_boundaries.v, _CoqProject:
compatibility, routing, hook, and failure regressions wired into root make.
tools/benchmark_ltac.py, tools/test_benchmark_ltac.py: hardened harness/checks.
Benchmarks/ltac2/: report, baseline/validation evidence, and final measurements.
No example, Gallina reflective engine, or soundness-proof source changed.

Implementation and audit commits merged through 602efc7:
  69b9915 Port simplifier and ISA step orchestration to Ltac2
  08b91ec Port symbolic interpreter helper control flow and harden Ltac bridges
  7dded5b Preserve ISA tactic dispatch and memory splitting behavior
  f32d84c Merge ISA-step Ltac2 behavior fixes
  0b2585b Harden sequential Ltac benchmark selection and resumability
  d7b7741 Include ISA behavior regressions in the build
  2510fc3 Merge sequential benchmark harness audit
  c7e8e69 Preserve native simplifier dispatch and hypothesis bridges
  a5caddc Merge native simplifier boundary fixes
  602efc7 Wire simplifier boundary checks and record wrapper validation

No .github PR template exists in HEAD or the original-master snapshot; no other
PR template was found in the worktree. PR_DRAFT.txt supplies a sentence-case
title/body with performance explicitly pending. No push or PR was performed.
This documentation job read sources and committed evidence only; it ran no
builds, tests, package tools, profiles, or measurements during collection.
