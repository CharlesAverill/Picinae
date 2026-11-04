# a-insque-fix: iterative Sol proof repair

State: **PROVED, local wrap-up at Charles’s explicit stop order.** Full vo target and all 19 transitive assumptions queries succeeded. No further compile or check is started after the stop order.
Initial author: gpt-6-astra, xhigh/default. Final proof producer: gpt-6.1-sol,
xhigh/default, established by the successful full kernel builds and assumptions query.

Branch: `llm-proofs/a-insque-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-349ae4c4`.
Author checkpoint: `9e964a2e501899960ba3ad3572239980742b54e7`.
Pinned origin: `49956416928e5b6bb3928b54ae33e3b81091f006`.

The worktree started clean at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is the pinned origin. A read-only network-enabled
`git ls-remote --heads fork refs/heads/llm-proofs/a-insque-fix` succeeded with
empty output before renaming only this prepared branch. The sandbox attempt
failed due to DNS; its retry was successful. The local rename initially
failed on read-only metadata; its authorized retry renamed only the prepared
branch and fast-forwarded to the exact author checkpoint. The complete
preparation logs are retained here. Only the checkpoint's exact prerequisite
history and this unit's own commits are allowed above origin.

Astra's `notes/a-insque/` remains byte for byte unchanged, including the
archived initial proof, first failed build and handoff. Its original branch
is untouched. Initial attempt SHA256:
`bb86f7df7e54c882713539b6522f74acd88c3dfa290ee4539b301dc6a532253c`.
The generated e08 map also remains unchanged, SHA256:
`0d6d574a200f0674353fc00c68f9affb99de3eb33944637d454c7bcbe3056879`.

## Repair and scope

Restored the exact complete archived proof, including all nine aborted
attempts. The first repair explicitly rewrites `N.eqb_refl` in
`insque_empty_links` before simplifying the two null stores. All 19 original
statements and all eight original definitions are retained; no separation,
CPU-feature, tunable, or callee assumption is added. The additional proof-script repairs and actual results are recorded below.

`insque_exact` specifies the original e08 eight-instruction AArch64 LP64 map
at 0x1e45e0 through the pre-RET exit 0x1e45fc. X0 is elem, X1 is prev, SP
and X30 are preserved. There are three actual paths: prev=0; prev nonzero
and original-memory next=0; prev and next nonzero. It loads next before any
store and specifies exact ordered writes to prev, optionally next+8, then
elem and elem+8. Its conditional trace theorem permits all aliases and
modular wrap, with no size or separation premise. It assumes a typed entry
state, the stated input register/memory equalities, and trace start at entry.
It is a `satisfies_all` partial-correctness theorem, not termination.

`insque_links` recovers final next/prev fields under elem+16 <= 2^64,
prev < 2^64, prev nonzero, and separation of elem's 16 bytes from neighbor
writes. The two neighbor fields may coincide (same value written) or be
disjoint; singleton circular prev=next is allowed. `insque_empty_links`
requires only elem+16 <= 2^64. `insque_byte_frame` preserves every byte
outside the writes taken on its path, without global separation.
`insque_preserves_callee_saved` covers X19-X29, SP, X30, modeled Z8-Z15,
and A_READ/A_WRITE for all endstates. The exact generated RET map and
`insque_return`/`insque_return_frame` prove execution to X30 changing PC
alone, separately from the pre-RET invariant theorem.

The empty, tail, and circular witnesses use elem=512, predecessor 0 or 256,
successor 0 or 256, SP=768, X30=4096, and the first 1024 readable/writable
bytes. `insque_access` supplies nonzero/nonwrapping elem[0..15], readable
and writable prev[0..7] when nonzero, and writable next[8..15] when nonzero.
It is a sufficient access predicate for witnesses, not a premise of the
conditional trace theorem. These witnesses establish inhabitation, not
whole-run termination or full-list sequence/cardinality refinement.

Binary provenance is inherited: Ubuntu AArch64 glibc 2.35-0ubuntu3.15,
ELF SHA256 `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`,
32-byte insque body at ELF 0xe45e0, model base 0x100000, strict e08/e11
scalar replacement via Ghidra 11.4.2 raw SLEIGH pcode. The IL proof does
not add lifting/hardware refinement, alignment/fault/lifetime/concurrency
claims, or ABI properties beyond the modeled frame.

## Validation evidence

Every compiler/query uses `build.sh` or `check-assumptions.sh`, the shared
resource gate with unit a-insque-fix, memory 1,750,000 KiB, stack 65,536 KiB,
read-only isolated picinae-env, Dune --cache=disabled -j1, full vo mode.
No host installation, dependency change, extra compiler, shared config
change, other-process signal, remote write, push, PR, branch modification,
subagent, or campaign-file edit is performed. The gate alone writes its
authorized scheduling state. The initial sandboxed gate launch failed before
compilation because the lease directory is read-only; the authorized launch
uses the same mandatory gate. No gate bypass or memory increase is used.

Final validation results:

- `build-06.log`: full `dune build --cache=disabled -j1 --display short Examples/claude/arm8_insque_proof.vo`, resource-gated at the assigned limits, exit 0.
- `assumptions.log`: final attributed source rebuilt successfully, then all 19 serial `Check`/`Print Assumptions` queries via `tools/print-assumptions.sh`, resource-gated, exit 0. Raw output is retained verbatim.
- `source-audit-final.log`: repository-wide audit against pinned origin, exit 0, NEW totals `{}`. No new admission, axiom or parameter. The module contains all 19 Qed proofs, with no Abort.
- `ancestry-precommit.log`: exact allowed origin..author-checkpoint history and unchanged generated map/original notes/root Dune, exit 0. `diff-check.log`: exit 0.
- `statements.log`: all 19 statements and all 8 definitions compared equal to the archive; the later vo-existence assertion raced the active attribution rebuild and failed while Dune had removed its old output. This unsuccessful check is retained honestly. The subsequently completed full-target/19-query assumptions command establishes the final vo exists and exports every fact. No rerun is made after Charles’s stop order.

Actual repairs relative to the archived attempt (no statement/definition changes):

1. Explicit `N.eqb_refl` reduction in the empty branch.
2. Replace unavailable `N.pred_lt` by the existing `N.lt_pred_l` in the mask bound.
3. Guard witness bound applications by syntactic stored-value equality before `exact`, avoiding failed unification against huge memory exponents. The capped `build-03.log` failed with OOM; `diagnostic-01.log` pinpoints the original broad tactic in `insque_witness_typed`, and `build-04.log` gets through typing, access, empty and tail witnesses after this repair.
4. In the circular witness, explicitly `change (0 < 2^(8*2^64))` before the power nonzero lemma. `build-04.log` records the opaque memsize mismatch; `build-05.log` records the unsuccessful direct unfold (memsize is opaque). No global transparency setting is changed. `build-06.log` passes all proofs.
5. Update only the attribution/evidence header after the first successful full build, then rebuild that final source in the successful assumptions command.

`build-02.log` records the first repaired full build’s unavailable-lemma failure. `build-01.log` records the sandbox lease-permission failure before compilation. Each failed attempt has its actual exit code and stdout/stderr. `build-03-source.v.txt` preserves the source used for the capped timing diagnostic; `diagnostic.sh` reproduces it without admissions or extra dependencies.

Transitive assumptions, read from the raw completed output:

- `insque_nwc`: Closed under the global context.
- `insque_welltyped`: inherited FunctionalExtensionality.functional_extensionality_dep only.
- `insque_preserves_callee_saved`: Closed under the global context.
- `insque_exact`: inherited FunctionalExtensionality.functional_extensionality_dep only.
- `insque_ret_map`: Closed under the global context.
- `insque_return`: Closed under the global context.
- `insque_return_frame`: Closed under the global context.
- `insque_halves`: Closed under the global context.
- `insque_lo`: Closed under the global context.
- `insque_hi`: Closed under the global context.
- `insque_empty_links`: Closed under the global context.
- `insque_links`: Closed under the global context.
- `insque_byte_frame`: Closed under the global context.
- `insque_mask_bound`: Closed under the global context.
- `insque_witness_typed`: Closed under the global context.
- `insque_witness_access`: Closed under the global context.
- `insque_empty_witness`: Closed under the global context.
- `insque_tail_witness`: Closed under the global context.
- `insque_circular_witness`: Closed under the global context.

Only the inherited Stdlib functional extensionality axiom occurs; no imported admission appears. The baseline provenance of that axiom is documented in notes/e00-build/README.md. There are no remaining proof obligations in the assigned 19 statements. The scope limitations above remain: sequential IL partial correctness, inherited unvalidated binary-lifting provenance, no termination or hardware/list-refinement claim.

Charles ordered immediate wrap-up after the validation command had already completed. No new proof work, compile, validation retry, push or PR is performed after that order. Current changes are committed locally; the coordinator may perform final independent review/post-commit validation. Original author branch, initial proof/map/evidence and shared campaign files are unchanged.

