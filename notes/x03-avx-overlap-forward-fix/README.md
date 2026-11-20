# x03 AVX forward overlap repair

Initial author: OpenAI gpt-6-astra, xhigh/priority. Repair/final proof producer:
OpenAI gpt-6.1-sol, xhigh/priority. This is the authorized local continuation
of checkpoint `14bdeb6a8e93bddb2014b9b907e432dbf2b1516d`.

**State: DONE for the preserved signed-dispatch forward-overlap contract.**
Both mains and all 16 helper/frame/witness facts are Qed. Full final-source
`.vo` compilation and all 18 transitive assumptions queries succeeded
(`12-assumptions.log`, exit 0). No remaining proof gap in this unit scope.

Branch: `llm-proofs/x03-avx-overlap-forward-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-be68d06e`.
Allowed ancestry: pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`,
e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, approved author checkpoint
`14bdeb6a8e93bddb2014b9b907e432dbf2b1516d`, then only this unit's scoped fix.
`00-setup.md`, `00-start.log`, and `11-precommit-ancestry.log` record setup.
The final commit/clean audit (`commit.log`, `commit-success.log`, `final-ancestry.log`) is recorded
externally after committing, under
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x03-avx-overlap-forward-fix/`.

## Specification preserved

`audit-declarations.py` compares every original definition, predicate, lemma,
theorem, and corollary declaration with the archived initial script.
All 26 declarations are preserved **verbatim** (`09-declarations.log`).
`13-original-diff.log` shows every change from the restored initial script;
its exit 1 means that the compared files differ, as expected.
The original unread-source and row proofs `ofw_load` and `ofw_store4` are
unchanged, as are all original x03 evidence files. No theorem was corrected,
removed, replaced with an assumption, or weakened. No new contract is used.
All seven checkpoint Abort declarations have been restored as Qed proofs.

The exported main theorems are:

- `memmove_avx_correct_overlap_forward`: `satisfies_all` partial correctness
  from actual normalized entry 0, through actual dispatch and 128-byte rows,
  to the cut before RET at 493, for the unchanged generated IL.
- `memmove_avx_overlap_forward_at_ret`: for an execution reaching 493
  without an earlier exit, all n destination bytes equal the ORIGINAL source
  bytes, every byte outside the destination is unchanged, RAX=d, RSP=rsp
  before RET, and RBX/RBP/R12–R15 retain their initial values.

The exact path domain remains `256<n<2^63`, `d<s<d+n`, `s+n<=2^64`,
and n no larger than both **initial-memory** REP and NT thresholds at
0x31a3f8 and 0x3215a8. Typed System V AMD64 entry: RDI=d, RSI=s, RDX=n,
RSP=rsp, V_MEM64=m. Destination nonwrap follows. There is no NOV premise,
minimum gap, or d>=128 requirement. Every genuine forward overlap distance
in that domain is allowed. The signed-dispatch bound n<2^63 is explicit;
this is not all-width or all-tunable coverage. DF and CPU feature bits are
not tested/assumed on this selected IL path; hardware ISA availability is
outside this IL theorem.

The invariant retains original YMM0/head and YMM5–8/tail values. Its byte
frame proves unread source bytes remain original. Four loads precede each
row's four writes; final saved-tail stores and the saved head complete the
byte coverage, including overlapping rows/tails and gap 1.

`ofw_witness_thresholds`, `ofw_entry_satisfiable`, and
`ofw_critical_distances` provide concrete threshold values and typed ABI
entry witnesses for every gap 1..511 at n=512, including 1/31/32/127.
These establish entry satisfiability, not execution termination.

## Repairs and iterative checking

1. Restore the complete archived initial proof text, preserving the archive.
   Keep `SN` in the arithmetic context when rearranging the wrapped d-s+n;
   natural subtraction needs that nonwrap bound (`01-full-vo.log`).
2. Replace row side-condition patterns that refer to cleared variables with
   direct context-fact selection and the existing arithmetic fallback.
   The complete main proof and RET corollary then kernel checked
   (`03-row-repair.log`, main Qed about 116 seconds); the build subsequently
   exposed the unchecked threshold-witness tactic.
3. Discharge computed witness inequalities with discrimination, avoid
   unfolding globally opaque `memsize`, use the existing proved
   `mp2_gt_0` instead of unavailable `N.pow_pos_nonneg`, and handle all ABI
   model branches without an incorrectly focused bullet.
   `04-witness-repair.log` and `05`/`06` witness logs preserve actual failures;
   `07-witness-check.log` is a successful capped auxiliary witness check.
4. `08-full-vo.log`: full requested Dune target, exit 0. The source header
   was then updated to name the actual Sol repair producer, so the
   assumptions command rebuilds the final attributed source as well.

Every proof-compiler invocation is sequential, with memory cap
6000000 KiB and stack 65536 KiB. Dune uses `--cache=disabled -j1` and full
`mode vo`; no skipped proof checking. The shared isolated wrapper is reused
read-only; no dependency installation or shared-environment edit occurred.

Successful full-target command (`08-full-vo.log`):

```sh
bash tools/record-command.sh notes/x03-avx-overlap-forward-fix/08-full-vo.log \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 6000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_overlap_forward_proof.vo'
```

Raw final-source build and all 18 Check/Print Assumptions queries are in
`12-assumptions.log`, invoked through `check-assumptions.sh`, which sets
PROOF_MEMORY_KB=6000000 and PROOF_STACK_KB=65536 and imposes the same shell
limits. It calls the required `tools/print-assumptions.sh`.

## Transitive assumptions result

`12-assumptions.log` contains the verbatim compiler stdout/stderr and every
Check/Print Assumptions result. `15-assumptions-summary.log` checks all 18
results: **15 closed, three inherited-FE-only**. The latter are
`ofw_welltyped`, `memmove_avx_correct_overlap_forward`, and
`memmove_avx_overlap_forward_at_ret`. Their sole axiom is the inherited
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
already documented in e00 (`notes/e00-build/logs/15-extensionality-provenance.log`).
For each of the two main theorems the raw assumptions output is exactly:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

All frame, original-memory load/row, dispatch, heuristic, and witness
lemmas are closed under the global context, as are the remaining arithmetic
helpers and the no-write-code theorem. No new or imported admitted theorem
appears in any result's transitive assumptions. The interface Parameters
listed by the source scanner do not survive as axioms in these results.
The final-source rebuild inside the assumptions helper succeeded in full
vo mode (main Qed about 106 seconds), before the query compilation.

## Source and trust boundaries

`10-source-audit.log`: required repository-wide
`tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006`,
exit 0, NEW totals `{}`. The baseline still has unrelated admissions and
module-interface Parameters; they are not completion evidence or imported
contracts. The explicit Dune selection is unchanged from the approved
checkpoint; the NT, REP, and nonoverlap-loop proof modules are not imported.
There are no admissions, Abort, Axiom, or Parameter declarations in this
unit's final proof source. Raw transitive assumptions, rather than this
lexical audit alone, determine the assumptions certificate.

Inherited binary identity: Ubuntu glibc 2.35-0ubuntu3.12 amd64 libc,
SHA256 `9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
Ghidra symbol 0x2a0840, image base 0x100000. The generated lift is unchanged.
This is sequential partial correctness of that inherited IL: no termination,
executed RET/caller continuation, hardware faults, ISA availability, cache,
timing, concurrency, or binary/lifter refinement claim. Provenance is not
upgraded to independent binary validation. Broader paths/sizes/tunables
remain outside the preserved contract.

No subagents, installations, pushes, PRs, remote comments/writes, other
branch mutations, or shared campaign edits were performed.

Raw compiler output in `12-assumptions.log` includes Rocq-emitted trailing
spaces on two existential-type lines. They are preserved verbatim.
The first commit precheck consequently stopped before committing
(`commit.log`, exit 2); source/script whitespace is checked separately
from immutable `.log` captures in the successful commit command.
