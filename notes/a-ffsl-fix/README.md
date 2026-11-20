# a-ffsl-fix — COMPLETE, kernel verified

Author model: **gpt-6-astra**. Repair model: **gpt-6.1-sol / xhigh / priority**.
Final proof model: **gpt-6.1-sol** (full Dune and assumptions validation passed).

Branch: `llm-proofs/a-ffsl-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-28e4e74e`.

## Scope and statement preservation

All 23 original author declarations, including every definition and all 16
original theorem/lemma signatures, are retained exactly. No predicate,
precondition, postcondition, helper statement or public theorem was weakened
or corrected. Three new supporting lemmas prove the RBIT size bound, modular
count arithmetic, and equivalence of the lifted HI flag expression to unsigned
strict comparison. The mathematical RBIT and bit isolation definitions are
unchanged. Both generated lifts are byte-for-byte unchanged against pinned
origin. `statement-preservation.log` and `generated-lift-audit.log` record this.

`check-statement-preservation.py` supersedes the archived author's comparison
script without modifying it: compare declarations individually, ignore proof
terminators, list additional helpers, fail for changed/missing declarations,
and separately reject remaining Abort. The author's original notes, first
failed attempt and diagnostics are all preserved unchanged.

The contract covers every typed 64-bit input, including zero, negatives and
LONG_MIN, at either RET40 or RET68; SP and X30 occur in the postcondition.
Separate frame theorems cover modeled memory and the original callee-saved
register list. ffsll uses an exact equality check of the two generated programs.
The result is IL partial correctness. It does not prove termination,
binary-to-IL soundness, hardware behavior or a complete ABI model.

Provenance remains Ubuntu ARM64 glibc 2.35-0ubuntu3.15,
SHA256 `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`,
ELF `0x94b10`, Ghidra `0x194b10`, 72 bytes. e02's 18 instruction matches and
shared alias entry are provenance evidence only, not a lifting certificate.

## Repair approach and failed-attempt history

The entry witness now calls `vareq`, rather than treating the EqDec instance
as a function. Least-set-bit existence is proved by width induction. RBIT is
proved bitwise with constant-mask pruning before input leaves are visited;
this avoids case splitting irrelevant input bits. The CLZ argument identifies
the largest reversed set bit. Signed ASR is related bitwise to the upper
32-bit word, without a sign restriction. Isolation uses the low-word remainder
and the shared higher quotient of x and x-1. Arithmetic calls in isolation
are restricted to their relevant hypotheses. The value proof handles both
word-selection cases from the actual isolated bit. Symbolic execution then
relates all return cases to that value, with a separate bitwise normalization
check for the simplifier's expanded RBIT expressions and a bounded modular
subtraction check. No AMD64 theory is imported by this proof.

Every failed build/diagnostic is retained. `build-01.log` starts from the
empty local Dune build directory and includes dependency compilation; it
fails on the first attempted equality-call replacement (`eq_dec` is not
available). `build-02.log` reaches the syntax error `intro _` in the archived
proof. `build-03.log` and `build-04.log` were explicitly interrupted while
diagnosing slow proof tactics (session exit 130, noted in each log). Timed
`debug-05.log` and `debug-06.log` likewise record interrupted RBIT diagnostics.
`debug-07.log` confirms RBIT and CLZ, then fails in ASR on unspecified
comparison operands. `prefix-build.log` compiles the unchanged successful
prefix once for faster local experiments; `debug-prefix.v.txt` is its exact
source. Debug modules are scratch artifacts, never imported by the real unit.
`debug-08.log` records a missing transitive notation import in that scratch
harness; `debug-09.log` fixes the harness and reaches the reversed operands
of the pow2 bit equality in isolation. `debug-10.log` and `debug-11.log`
record explicitly interrupted expensive arithmetic calls. `debug-12.log`
confirms all mathematical helpers and reaches a later unsupported tactic
syntax in the archived public proof. `debug-13.log` dumps all four actual
symbolic return goals. `debug-14.log` and `debug-15.log` record the failed
attempt to equate differently simplified RBIT expressions by reflexivity.
`debug-16.log` records a size-bound proof tactic error. All these are proof
script failures or explicit diagnostic interruptions, with no admissions or
replacement assumptions. Corresponding source snapshots are retained as
`attempt-*.v.txt` (05 is the same source as 04; 09 is the same as 08).

## Environment and ancestry

No dependencies were installed and no shared environment was changed. Every
compiler uses the existing read-only isolated wrapper. One compiler at a
time; virtual memory 3,000,000 KiB; stack 65,536 KiB; Dune cache disabled and
`-j1`; assumptions helper `PROOF_MEMORY_KB=3000000`.

The prepared worktree was clean at reviewed e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, directly above pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006`. The required read-only fork
collision check returned success and empty output after a sandbox DNS
failure. Only the new prepared branch was renamed (Git metadata required
approved escalation), then a local `git merge --ff-only` imported exactly
Astra checkpoint `95fec3532babe28cc92926f2a23d6253ce55c69a`. See
`branch-setup.log`, `fork-collision.log` and `ancestry-before.log`.

Allowed ancestry is pinned origin -> e00 -> Astra checkpoint -> local repair
commits only. The original author branch/worktree were not changed. No new
worktree, remote write, push, PR or comment; no shared plan/status edits.
Future publication requires Charles's approval and would be fork
CharlesDardaman/Picinae -> CharlesAverill/Picinae:llm_generated_proofs.

`debug-17.log` records the explicitly interrupted first inline RBIT bridge
attempt. `debug-18.log` records a tactic-parameter scoping error while
restricting that bridge's context. `debug-19.log` checks the revised bridge
with only its input variable retained, so finite-bit arithmetic cannot inspect
the surrounding symbolic state. Its per-bit progress messages are diagnostic;
the final source removes those messages. These are proof-body-only changes.


## Final validation — all exits 0

The actual final `Examples/claude/arm8_ffsl_proof.vo` Dune target compiled in
full `vo` mode with no proof skipping. `build-final.log` records the exact
command through `build.sh`, all stdout/stderr and exit 0. `attempt-final.v.txt`
is the exact source compiled. The initial build compiled the dependency
closure locally with the cache disabled; the final build checks the repaired
unit itself. No clean rebuild was needed to establish these dependencies.
`debug-19.log` is a separate successful diagnostic compile, including both
public Qeds (ffsl_correct kernel check: 66.829 seconds); it is not substituted
for the actual full Dune target.

```sh
bash tools/record-command.sh notes/a-ffsl-fix/build-final.log \
  bash notes/a-ffsl-fix/build.sh
bash tools/record-command.sh notes/a-ffsl-fix/assumptions.log \
  bash notes/a-ffsl-fix/assumptions.sh
python3 tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006
```

`assumptions.sh` sets PROOF_MEMORY_KB=3000000 and invokes the existing
`tools/print-assumptions.sh` inside the isolated environment. The helper
builds the real target and compiles a temporary query against `_build/default`
only. `assumptions.log` preserves all 19 Check/Print Assumptions outputs
verbatim. `ffsl_correct`, `ffsll_correct`, and `ffsl_welltyped` report exactly:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib functional extensionality baseline documented in
`notes/e00-build/logs/15-extensionality-provenance.log`; it is the only
transitive assumption. The other sixteen queries, including both frame
theorems, the inhabited entry/spec, RBIT, CLZ, ASR, isolation, routing and
value arithmetic, each report `Closed under the global context`.
`assumptions-check.log` checks the actual query output against this baseline;
it does not replace the raw certificate.

`final-source-audit.log`: exit 0, NEW totals `{}`. No Abort remains in any
exported theorem/helper, and no new Admitted/admit/Axiom/Parameter occurs.
`statement-preservation.log`: all 23 original declarations unchanged.
`comparator-controls.log`: negative controls pass.
`diff-check.log` and `precommit-diff-check.log`: exit 0.
`toolchain.log`: exact Rocq/Dune/OCaml versions.
`objects.log`: actual `.vo` files and the final proof object hash.

The last resource observation of the Dune compiler was RSS 1,471,828 KiB,
VSZ 1,678,792 KiB, below the fixed cap (not a claim of peak memory). All
compiles remained capped; no concurrent compiler, cap increase or dependency
installation was used.

Post-commit `ancestry-after.log` and `commit.log` are ignored local evidence
so they can record the actual full final SHA and clean worktree. The same
post-commit identity/evidence is copied only to the authorized unique external
`units/a-ffsl-fix/` directory. All failed diagnostics and source snapshots,
final build/assumptions logs, scripts, source audits and original notes are
committed. Parent review and any original-unit fast-forward remain pending.
