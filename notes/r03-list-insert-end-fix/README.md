# r03-list-insert-end-fix

State: DONE for the retained local sequential-IL contracts, subject to the scope
below. author_model=gpt-6-astra; final_proof_model=gpt-6.1-sol. Initial author
ran xhigh/priority; this repair ran xhigh/default. No subagents, installation,
push, PR, remote comment, remote write, or shared campaign/status edit.

Branch: `llm-proofs/r03-list-insert-end-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-75bde600`.
Implementation commit: `a8a1d379ef944da1fb30524394eeaad204bc8ad8`.
Final evidence-only commit follows it; the handoff gives the final HEAD.

Reviewed source checkpoint: `0a0c7ee9ee6ae72177090bfc65404c572c46455b`.
Origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Preparation and exact ancestry

Read the campaign plan (including assigned row), BUILDING.md,
Examples/claude/SKILL.md, original unit README/archive/build diagnostics, r00
model and the generated leaf. Charles's no-admissions/resource rules override
the skill's conflicting advice.

The first inspection found a clean prepared branch `t3/list-insert-end-frame`
at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent the pinned
origin base. Initial sandboxed fork lookup failed DNS; read-only escalated
`git ls-remote --heads fork refs/heads/llm-proofs/r03-list-insert-end-fix`
succeeded with no result BEFORE branch rename. Log `19-fork-collision.log`
records a repeat success/no result. Sandbox metadata writes initially failed;
escalated rename of only the prepared branch and exact `git merge --ff-only
0a0c7ee9ee6ae72177090bfc65404c572c46455b` succeeded. No automatic approval
rejection. No shell worktree, fork branch base, or unrelated history imported.

`ancestry-before.log` records the e00 HEAD/parent and exact base..checkpoint
allowed set before proof edits. Its status includes only this new evidence
directory, created after the initial clean inspection. `02-checkpoint-audit.log`
and subsequent ancestry logs verify exact allowed commit membership. The
reusable `audit-ancestry.sh` compares `base..HEAD` with `base..checkpoint` plus
explicitly supplied own commits. It also verifies origin/merge-base pins and
unchanged ISA, frontend, fixture, generated maps/JSON, r00, root Dune and
original Astra evidence. Original author branch/evidence remain untouched.
Only this unit's own local commits follow the checkpoint.

## Repair and statement retention

Restored `notes/r03-list-insert-end/initial-attempt.v.txt` exactly before
repairing. The only proof changes from that archive are:

- Match each outer byte read/store explicitly and apply `getmem_noverlap`
  with all arguments; normalize membership and the count address `L+0`.
- Normalize cast/eval_binop/boolean encodings and constant addition order
  before `psimpl` in the actual symbolic-execution theorem.
- Normalize `2^(4*8)` to `2^32` explicitly in the fixture pointer bounds.

All other archived proofs now check unchanged. No statement, definition,
invariant, precondition, witness, or IL changed. The original source header's
final-producer pointer was updated to this repair; original author attribution
and evidence are preserved. `16-strict-retention-audit.log` proves identical
non-proof text before that header-only update; `18-final-retention.log` compares
all original non-proof code after stripping comments, retaining all definitions
and all 19 statements exactly. There are 19 Qed blocks, no Abort, admission,
new axiom or parameter in the completed scope. Root Dune already selected this
unit at the checkpoint and needed no changes.

All failed iterations are retained in logs `01`, `03` through `10`, with real
exit codes and compiler stdout/stderr. They are proof-script failures, not
successful validations. `11-fixture-repair.log` is the first successful full
unit build, exit 0; no `.vos` or skipped checking.

## Successful validation

Every Rocq/Dune/assumptions run uses the read-only wrapper
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`,
`ulimit -v 2000000`, `ulimit -s 65536`, one compiler, and Dune
`--cache=disabled -j1`. No cap increase or dependency installation.

Successful full target command (`11-fixture-repair.log`, exit 0):

```sh
ulimit -v 2000000
ulimit -s 65536
dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInsertEnd_proof.vo
```

`20-final-clean-build.log` records `dune clean` followed by this exact target,
checking the complete required dependency closure and all 19 proofs from
source after the header update, exit 0. `12-assumptions.log` contains raw Check/Print
Assumptions output for EVERY retained theorem/corollary, exit 0. The final
query is recorded again after the clean build in
`24-final-all-assumptions.log`, covering all 44 declarations: the 19
theorems/corollaries plus all 25 definitions/fixpoints. Commands/logs use
`tools/record-command.sh`; assumptions use `tools/print-assumptions.sh` with
`PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536`.

`13-source-audit.log`: full repository audit against the pinned base, exit 0,
NEW totals `{}`. Baseline unrelated admissions/interface parameters remain
inventoried; they are not used by these proofs.
`14-unit-source-audit.log`: proof/r00/generated-map scope, exit 0, no suspicious
tokens at all. Transitive assumptions are checked separately, not inferred
from lexical auditing. Final audits also cover the final source.

## Actual contracts and boundaries

`insert_end_exact`: satisfies_all for the unchanged actual 11-instruction leaf,
entry 0x5c, exit cut at BX LR 0x70, with chronological memory effects, scratch
registers R2/R3 and exact modeled NZCV. Requires a typed entry and R0=L/R1=P;
its observed loads intentionally include earlier stores.

`insert_end_at_bx`: under the retained local layout/links/permissions/ordinary
LR precondition and an actual trace from entry to BX with no earlier exit,
relates those effects to ORIGINAL memory. It establishes six words in order:
P.next=I, P.prev=B, B.next=P, I.prev=P, P.container=L, and count increment
modulo 2^32. It preserves L.index, P.value, P.owner and every original byte
separate from the six write words. R0/R1, R4-R12, SP/LR, permissions and
temporaries are preserved; R2=B, R3=new count and flags are specified. The
function is void; no new result is claimed in R0.

`insert_end_trace_returns`: appends the actual modeled ordinary BX step to
that existing trace while retaining the same postcondition.
`insert_end_count_no_overflow`: the mathematical +1 count under original
count < 2^32-1.

Domain: 32-bit nonnull aligned nonwrapping objects L20/P20/I12/B12. P20 is
separate from L20/I12/B12. The nine relevant WORDS are separate (six writes,
L.index, P.value, P.owner); existing objects need not be pairwise disjoint.
I=B=L+8 (empty sentinel), sentinel/ordinary neighbors, and I=B at an ordinary
item remain permitted. Original links are L.index=I, I.prev=B, B.next=I;
no output relation or global sequence/cardinality is assumed. Required
permissions cover precisely three read and six write words. Ordinary LR is
odd and below 0xfffffff0. No stack alignment condition is needed, and there
are no callee/oracle contracts or CPU-tunable assumptions.

`insert_end_memory_fields`, `insert_end_memory_frame`,
`insert_end_original_loads`, `insert_end_nwc`, `insert_end_welltyped`, and
`insert_end_register_frame` supply the pure-memory/typing/frame facts.
`insert_end_fixture_links`, `insert_end_fixture_typed`,
`insert_end_entry_witness`, `insert_end_empty_layout`,
`insert_end_nonempty_layout`, `insert_end_local_empty_witness`, and
`insert_end_local_nonempty_witness` construct typed/readable/writable entries,
including (L,P,I,B)=(4096,8192,4104,4104), count 0 and
(4096,8192,12288,4104), count 1.
`insert_end_return_step` and `insert_end_ordinary_return_nonvacuity` establish
an inhabited ordinary modeled BX step. These witnesses do not establish a
complete entry-to-return trace.

## Transitive trust, verbatim

14 declarations print `Closed under the global context`. Exactly these five
print only the inherited axiom below: `insert_end_exact`, `insert_end_at_bx`,
`insert_end_return_step`, `insert_end_trace_returns`, and
`insert_end_ordinary_return_nonvacuity`.

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is Stdlib's `FunctionalExtensionality.functional_extensionality_dep`,
already documented in e00, not an imported admitted proof. The raw outputs
are retained verbatim; the five results are not closed under the global
context. No additional assumptions or unproved kernel/callee contracts.

This completes the retained sequential-IL PARTIAL-CORRECTNESS scope, not
termination, progress/execution existence, global finite-list representation
or cardinality (r47), hardware IRQ/EXC_RETURN/scheduler behavior, or binary/lifter
refinement. FreeRTOS V11.1.0 ELF and strict generated-map provenance are inherited
unchanged: no correctness claim beyond that trusted lifting/ISA boundary.
