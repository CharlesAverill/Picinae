# x01-sse2-nt-complete

State: DONE for the assigned NT-strategy IL partial-correctness scope.
This is GPT-6.1 Sol continuing original x01;
original statement author GPT-6 Astra. The original source is archived
verbatim in `original-author.v.txt` (SHA256
370d8cc31a381399cad0994852fa4bcc6083baa7c982b8521f6400e5179ddbb5).
All 16 original statements, 9 original definitions, and every later checked
Sol helper/dispatch declaration remain unchanged. No generated lift changed.

Branch: `llm-proofs/x01-sse2-nt-complete`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-0da1e0be`.
Prepared clean HEAD was e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9.
Allowed ancestry:
49956416928e5b6bb3928b54ae33e3b81091f006 (pinned origin)
-> 71470bffba65392adf1873a3df9f0cf0ca4f1ac9 (e00)
-> c63095989bf5d49153046d2285b3e27580346fde (Astra)
-> bd8890e88451eef3ee9ce382629b8a710b95e3ed (prior Sol)
-> this continuation's own local commit(s).
Only the prepared branch was renamed, after a successful empty read-only
fork-name query. Initial sandbox DNS and Git metadata write failures were
resolved using authorized elevated read-only/name/import operations.
No remote write, dependency install, shared-environment mutation, subagent,
or shared plan/status/campaign edit occurred. The accepted AVX source was
read using `git show cfb65c6:...`; no AVX contract or history was imported.

## Specification and exact domain

Main statement: `memcpy_correct_nt_strategy` in
`Examples/claude/amd64_memcpy_nt_strategy_proof.v`.
It composes the real public entry 0x1c4870 through NT head 0x1c4bad,
two-page loop 0x1c4c25 or four-page loop 0x1c4d45, post-bulk dispatch,
and the real RET cuts 0x1c4d29 / 0x1c4ed1. It states `satisfies_all`
partial correctness of the unchanged lifted IL, not termination.

System V AMD64 input: modeled x64 state, memory m, RDI=d, RSI=s, RDX=n,
RSP=rsp. At either RET cut: RAX=d, RSP=rsp, each destination byte i<n is
original m[source+i] modulo 2^64, and every byte outside destination[0,n)
is unchanged. Callee-saved preservation uses inherited
`memcpy_preserves_callee_saved`; typing and no-write-code use inherited
`memcpy_welltyped` and `memcpy_nwc`. These facts are queried transitively.
RET itself, its stack pop and the caller's return address are not executed
by this cut-point statement.

Hypotheses are n>128, modular nonoverlap `nov d s n`, d+n<2^64,
n>initial m[qword 0x3215a8], and `nt_strategy_domain m d s n`.
The 64-bit size bound follows from MDL and RDX=n. No separate source
nonwrapping premise is used: source loads/pointers follow the model's
modulo-2^64 memory. There is no artificial upper-size cap.

The precise selected-path domain is:

- a = 64 - d mod 64, with 1<=a<=64.
- H = `nt_head_memory m d s`: exactly the four head stores of original
  16-byte source values at offsets 0,16,32,48, not an assumed final result.
- alias means `lnot (msub 12 s d) 12 AND 0xf80 = 0`; the instruction
  proof ties this low-twelve-bit expression to the actual ECX test.
- four-page is selected iff alias OR H[qword 0x3215a8] <= (n-a)>>4.
  The comparison uses UPDATED head memory, including when destination
  overlaps the threshold global. The initial threshold is never silently
  substituted. The witness-only global-frame lemma is not a main premise.
- If four-page is selected, a+16384<=n; otherwise a+8192<=n.
  These are exactly positive bottom-tested counts via `nt_chunk_positive`.

Real SHR/AND instructions derive K=floor((n-a)/8192) or
floor((n-a)/16384) and the respective remainder. Both real DEC ECX/JNZ
loops run over i<64, with 64 bytes on each page per iteration. The proof
handles arbitrary positive outer counts, advances all eight/sixteen
MOVNTDQ stores, and joins the complete prefix a+chunk*K and actual RDX
remainder to direct-final and looping tails. It does not substitute the
AVX i<32 / 128-byte row.

Nonvacuity is explicit: `memcpy_nt_head_nonvacuous`,
`nt_strategy_domain_nonvacuous`, `memcpy_nt_bulk_nonvacuous`, and
`memcpy_nt_strategy_nonvacuous`. Both choices use d=65536, s=131072,
n=16448, with initial threshold 4096 (two-page K=2) or 0 (four-page K=1).
The copied initial head is constructed from stores, and the bulk witness
assumes no completed buffer. Memory/model bounds are proved, not postulated.

## Trust and coverage boundaries

Inherited Ubuntu amd64 glibc 2.35-0ubuntu3.12 libc SHA256:
9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
Generated `memcpy_amd64.v` SHA256 remains
7c981ab264263904273b59b80b83f847644f2a7a2e3174f99ae37a5a43a64c0e.
Binary/lifter provenance is inherited, not revalidated here. The known
PREFETCHT0-as-NOP, MOVNTDQ-as-ordinary-store and SFENCE projection boundaries
remain unvalidated hardware/cache/order/fault/CPU assumptions. No CPU feature,
fault-freedom, concurrency, timing, termination, or binary-soundness claim.
This is the NT strategy only; x05 all-strategy memcpy composition is separate.

## Validation and evidence

Every proof/build/query uses the read-only existing wrapper
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`,
`ulimit -v 8000000`, `ulimit -s 65536`, Dune `--cache=disabled -j1`,
and full `.vo` checking (`mode vo`). One proof compiler at a time; cap was
never raised. Raw commands, real exit codes and stdout/stderr are retained.

- `03-baseline-build.log`: fresh prerequisite closure plus old NT helpers
  and dispatch; exit0, 17:12.41, max RSS3545492KiB, zero swaps.
- `25-head-domain-build.log`: head execution module full .vo succeeds;
  initial witness module error retained. `31-domain-memory-positive.log`
  and `52-bulk-witness-build.log` fully build the corrected witnesses.
- `51-bulk-page-offset.log`: both bulk targets full .vo, exit0,
  10:58.64, max RSS6432092KiB, zero swaps.
- `55-strategy-setup-frame.log`: full public-entry strategy .vo, exit0,
  10:22.76, max RSS7250000KiB, zero swaps. Every main/helper theorem and
  witness in the final source is kernel checked. No Abort/admission remains.
- `check-declarations.py` preserves every checkpoint theorem/definition;
  original-author preservation also uses the inherited statement auditor.
- `check-history.sh` checks the pinned parents, unchanged lift/old proofs,
  branch, merge-base, commit list, diff stat and status.
- `audit-assumptions.py` queries every unit theorem/lemma and the inherited
  typing/nwc/callee-frame facts via `tools/print-assumptions.sh`, serially.

`full-strategy-draft.v.txt`, `strategy-composition.v.txt` and the projection
probe are historical development snapshots, not proof prerequisites or
certificates. The very large eager-reduction diagnostic is retained losslessly
as `46-projection-reduction.log.gz`; the final proof uses restricted lazy
projection reduction instead. Failed build logs document iterative repairs.
No new admission/axiom/parameter was introduced at any point.


## Final assumptions and audits

`57-all-assumptions.log` completes all68 queries with exit0. Raw `Check` and
verbatim `Print Assumptions` output is in the eight `assumptions-*.log` files.
`60-assumptions-review.log` checks every Axioms block:42 constants are closed
and26 have exactly the documented inherited FE assumption, including
`memcpy_correct_nt_strategy`. No imported admitted proof or new axiom occurs.
The main theorem's raw assumption block is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The nonvacuity theorems and all arithmetic/memory staging helpers are closed.
Inherited `memcpy_welltyped` is FE-only; nwc and callee-saved preservation
are closed. This is the e00 baseline assumption, not a unit declaration.

`58-final-source-audit.log` runs `tools/audit-proof-source.py --base
49956416928e5b6bb3928b54ae33e3b81091f006`: exit0, NEW totals:{}.
`59-original-statements.log` preserves all16 Astra statements and9 definitions.
`56-history-precommit.log` and the final postcommit audit preserve the complete
allowed ancestry, old Sol statements and generated lift hash. No old proof
file changed. Only the five new unit proof modules were added to Dune's
explicit selection; no glob, unrelated admitted/heavy module, dependency
installation, remote write or other branch mutation was used.

Remaining gaps within the assigned NT-strategy IL partial-correctness scope:
none. Hardware/lifter refinement, faults/CPU/cache/order/concurrency,
termination and x05 all-strategy composition remain outside this result.
No publication occurred. Full commit identity and clean postcommit status
are recorded in the permitted external unit directory to avoid self-hash edits:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x01-sse2-nt-complete/`.
