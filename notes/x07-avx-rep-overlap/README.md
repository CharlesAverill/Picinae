# x07 AVX REP forward overlap

**State: PARTIAL — one-shot initial full target failed with out of memory.**
Dune exit1, Rocq signal ABRT, under the assigned6000000 KiB virtual-memory
cap. No cap increase and no second Astra proof attempt/compiler run.
All nine statements are retained exactly with Abort; no x07 theorem is
exported or claimed certified. The initial complete attempt is archived.
A NEW gpt-6.1-sol xhigh/default fixer is required from the coordinator.

Initial author: OpenAI `gpt-6-astra`; assigned reasoningEffort `xhigh`,
serviceTier `default`. Final proof producer: unset. No delegated agents.
The service tier is the assigned setting, not an independently queried runtime
attestation. No environment or coordinator settings were changed.

Branch: `llm-proofs/x07-avx-rep-overlap`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-e7e7a9ff`.
Publication: LOCAL ONLY; no push, PR, remote comment or remote mutation.
No installs; existing toolchain reused read-only.

## Exact authorized history

1. origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
2. e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent origin.
3. x03 Astra `14bdeb6a8e93bddb2014b9b907e432dbf2b1516d`.
4. x03 Sol `14ea393f2227bc8bde692b1e70badc61dce80304`.
5. Only x07's own local commit(s) after that checkpoint.

The prepared branch was `t3/x07-avx-rep-overlap-close-gen`, HEAD e00,
with empty `git status --short` on the first inspection. `00-prepared-history`
was captured after creating this notes directory, hence its sole untracked
notes entry. A first fork-name read succeeded empty; the first recorded repeat
failed DNS (exit128), and recorded retry02 succeeded empty (exit0). Only then
was this prepared branch renamed. Sandbox initially denied Git metadata
writes (03, exit128); authorized retry04 succeeded. Fast-forward05 imported
only the explicitly allowed x03 checkpoint. No other branch was changed.

## Intended statements and coverage

`Examples/claude/amd64_memmove_avx_rep_overlap_proof.v` proposes:

- `memmove_avx_correct_rep_overlap`: `satisfies_all` from actual entry0.
- `memmove_avx_rep_overlap_at_ret`: at actual pre-RET cuts493/692/794,
  original-memory byte copy, destination-complement byte frame, RAX=d,
  RSP unchanged, and RBX/RBP/R12-R15 frame.
- `orp_welltyped`, `orp_nwc`, `orp_preserves_callee_saved`,
  `orp_neg_distance`, `orp_witness_globals`, `orp_entry_satisfiable`,
  `orp_critical_distances`.

Domain: typed System V AMD64 entry RDI=d, RSI=s, RDX=n, RSP=rsp, DF=0;
`256<n<2^63`, `d<s<d+n`, `s+n<=2^64`, and
`m qword[0x31a3f8] < n`. No NOV or address lower bound. No minimum gap.
Destination nonwrap follows. Stop threshold and policy are unrestricted:
all below-stop REP alignments, short-distance policy fallbacks and
at/above-stop overlap fallbacks are included in the intended statement.
NT threshold0x3215a8 is not read on this entry branch. Detailed source
inspection and actual store order are in `dispatch.md`.

Architecture-neutral `cpy`, `ofw_load`, and `ofw_store4` are actual proof-script
dependencies; the x03 function-entry theorem is NOT applied outside its two
threshold bounds. New REP byte reasoning uses `ofw_load`, not NOV-dependent
`cpy_load`. Memory frames include overwritten tunable addresses.

Witness statements cover every gap1..8191 at n8192, all valid policy/stop
words; concrete corollary covers gaps1/31/32/63/127/4096, policy0/1,
stop0/16384. This covers both REP alignments, close fallback and stop
fallback states, but claims no terminating execution witness.
No new callee/helper contract or result oracle is introduced.

## Validation protocol and trust boundary

`build.sh` records the single initial full `.vo` attempt in
`10-initial-full-vo.log`. Every compiler inherits `ulimit -v 6000000` and
`ulimit -s 65536`; Dune uses `--cache=disabled -j1`. Only these full targets
are requested, along with their required dependency closure:

```
Examples/claude/amd64_memmove_avx_rep_overlap_proof.vo
Examples/claude/amd64_memmove_avx_rep_proof.vo
```

Root dune explicitly adds only the new target and baseline loop/REP helpers.
No generated map changed (`09-lift-unchanged.log`, exit0). No unrelated
admitted/heavy modules selected. `initial-attempt.v.txt` is the exact initial
source before the first compiler run. `preserve-handoff.py` is a mechanical
Abort conversion for failure; it checks all nine statements stay identical.

Source audit07 (eight selected/helper source files) exit0, baseline/current/
new suspicious-token counts all empty. Full repo audit08 exit0: existing
baseline seven Admitted, one admit and89 module-interface Parameters;
new totals empty. Those repository counts do not certify transitive trust.
The inherited x03 raw assumptions evidence is
`notes/x03-avx-overlap-forward-fix/12-assumptions.log`; its mains report
`FunctionalExtensionality.functional_extensionality_dep`. e00 documents
this inherited assumption. Fresh x07 assumptions are mandatory for DONE;
no inherited log is presented as a fresh x07 query.

This is sequential lifted-IL partial correctness only, with inherited
unvalidated binary/lifter provenance. Total memory does not model hardware
page permissions, CPU availability, faults or concurrent writes. This work
cannot establish termination, execution of RET or hardware/binary refinement.
Sizes n>=2^63 remain x09; entry n<=REP but n>NT remains x10; x03 applies only
below both initial thresholds. Within x07's intended forward-overlap domain,
source inspection finds no NT stores selected, even above stop.

## Actual result and immediate handoff

`10-initial-full-vo.log` contains the exact command and all compiler stdout/
stderr, including `Fatal error: out of memory`, signal ABRT, and EXIT_CODE=1.
The last printed cut was813; a warning locates notation in tactic line125.
These are diagnostics, not proof that the resource failure occurred at a
particular tactic. The current initial main proof was not certified.

The same single invocation successfully produced full `.vo` dependencies:
`amd64_memmove_avx_proof`, `amd64_memmove_avx_overlap_forward_proof`,
`amd64_memmove_avx_loops_proof`, and `amd64_memmove_avx_rep_proof`, plus their
core/memory closure. There is NO successful overall x07 target command and
NO x07 `.vo`. Standard empty `.vos` sidecars from full `.vo` compilation
are not proof-skipping builds; dune explicitly uses `(mode vo)`.

`11-preserve-handoff.log` records mechanical replacement of every proof body
by Abort and equality of all nine original statements. No statements were
weakened. This conservative partial source exports definitions and tactics,
not any new proved helper. The final Abort source was NOT compiled again,
per the one-shot handoff rule. The original attempt remains intact.

Fresh Print Assumptions output for x07: NONE. Its failed `.vo` provides no
main constants to query. `tools/print-assumptions.sh` was therefore not run;
`check-assumptions.sh` records the capped queries the fixer must run only
after restoring and successfully checking proofs. No transitive trust
certificate is claimed for x07 or for newly selected baseline REP helpers.
Inherited x03 FE-only evidence is disclosed above, not silently substituted.

Remaining: finish dispatch/REP/fallback proof checking within6000000 KiB,
validate the actual RET corollary and all witnesses, run fresh transitive
assumptions queries and source/ancestry audits. Static inspection suggests
reviewing impossible800->337 branching and adding explicit cuts before any
unbounded symbolic path, and reviewing generic splitting/unification near
symbolic memory. This is an untested hypothesis, not an OOM diagnosis or a
repair performed by Astra. Keep the intended entry and RET statements;
explain any genuinely necessary statement changes.

The local commit and clean postcommit ancestry record are stored externally
under `/home/charles/code/friends/.refs/picinae-llm-proofs/units/x07-avx-rep-overlap/`.
