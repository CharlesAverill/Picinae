# a-strcmp-complete — Sol continuation

Assigned branch: `llm-proofs/a-strcmp-complete`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-e23fc53c`.
Original author model: `gpt-6-astra`. Continuation model: `gpt-6.1-sol`, xhigh/default.
Final full-proof producer: **none**.
This note does not declare the function complete.

## Protected statement and history

Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose
sole parent is origin base `49956416928e5b6bb3928b54ae33e3b81091f006`.
The exact requested checkpoint `66bb12cfed34143d050f29289e4dc6aabba2cf87`
was imported with `git merge --ff-only`. Its nine commits above origin are
listed in `allowed-prerequisites.txt`; scoped linear commits are the only
permitted additions. No fork head was used as a base.

The first read-only fork check failed sandbox DNS; the escalated check
succeeded with empty output before the local rename. The success is also
rechecked in log 09. The prepared local branch name changed externally from
`t3/e23fc53c` at first inspection to `t3/strcmp-completion` before log 00;
HEAD remained e00. This run renamed only that prepared branch. The first
fast-forward failed because Git metadata outside the worktree was read-only;
log 03 records the successful authorized local retry, followed by log 04's
rename. No other branch was changed, and no remote write occurred.

The initial tool inspection observed a clean prepared worktree; log 00 is
recorded after creating this unit's untracked notes, and discloses that notes
entry. `audit.py` protects all 69 prerequisite definitions/statements,
including the 29 original Astra declarations. It also protects the generated
77-instruction map (SHA256
`2b7b58a310afd013b2dae9e2953786404640796734fc6ae39cf309f0a6568dc3`),
manifest, root Dune and all other prerequisite files.

## Validation rules

No installation or dependency change. The existing isolated environment is
read-only. Every compiler, Dune and assumptions invocation uses the required
`resource-run.py --unit a-strcmp-complete --memory-kib 4000000 --` gate, the
assigned environment wrapper, stack 65536 and serial Dune with disabled
cache. No cap increase, gate bypass, concurrent compiler or signal to another
unit is permitted or used.

Log 05 is an actual successful inherited full `.vo` target, **not** a main
function proof: the prerequisite ends `strcmp_correct` with `Abort`.
The inherited 42 completed facts and their FE-only/closed assumptions are
recorded in `notes/a-strcmp-fix/`. The inherited absence of the main theorem
is explicit in its log 32. New kernel evidence must be read separately.

The diagnostic source is `mask-helpers.v.txt`; the runner imports the checked
inherited module and compiles a temporary full `.vo` query, never `.vos`.
The current runner will save SHA256-named source snapshots on admission.
The earlier `draft-after-first-probe.v.txt` is a draft snapshot after log 06,
not a byte-for-byte record of that complete compiler input. Its first lemma
is identical to the checked prefix. Log 06 checked the first generic borrow
lemma then failed a rewrite in the next lemma. Log 08 was the corrected
probe, which never received admission. Arithmetic sanity log 11 (512 exhaustive byte/borrow cases and 4,101
word cases) is **not a proof certificate**.

## Intended unchanged coverage

The public contract allows all lengths and alignments, aliases, overlap and
high unsigned bytes. It compares the sign of signed32(W0) against the first
stop in the original memory. Its explicit readable, strictly nonwrapping
envelopes are `[down8(p),down8(p+K)+8)` and
`[down8(q),down8(q+K)+16)`. There is no CPU, tunable or disjointness premise.
The memory, SP, X30, X19–X29, Z8–Z15 and access-mask frames remain unchanged.
Sequential IL partial correctness stops before RET192fe4 or RET1930b0;
termination, executed return, fault freedom and binary/lifter refinement
remain outside the inherited claim.

The concrete weak decoder state from the prerequisite is not claimed
reachable. It exposes only the missing common-NUL high-bit fact in the old
internal invariant; it does not refute the public contract. The detailed
remaining general proof obligations are in `REMAINING.md`.

## Final state: PARTIAL, blocked on compiler admission

The main `strcmp_correct : strcmp_full_contract` remains **Abort**, and has
no compiled constant. The generated map and all 69 prerequisite declarations
(including all 29 original Astra statements) are unchanged. No new admission,
axiom, parameter, oracle or callee assumption is added. Only
`strcmp_complete_borrow_digit` is added to the active proof source. It is
identical to the first diagnostic's Qed-checked prefix. Its statement gives
the exact base-256 digit after subtraction in terms of the lower-digit borrow
for `2^n=256*B`, positive B, lower digits a,c<B, b<256 and d<255. These are
auxiliary arithmetic premises, not restrictions added to the public contract.
They are inhabited, for example by n=8, B=1, a=b=c=d=0.

The combined updated proof module has **not** passed a new full target build,
and there is no separate assumptions certificate for the new lemma. Its
`Print Assumptions` directive is present for the next full build. Do not treat
the inherited successful module build as validation of the updated file.

Log 08 ended **143** after stopping only its own unadmitted resource-run
waiter. Under the admission lock, log 12 verified that this unit had no
active compiler reservation before signalling that waiter. It had waited
**1340.53 seconds** with **64** admission-wait messages. At cancellation:

- MemAvailable: 40,345,416 KiB.
- Active reservations: 17,500,000 KiB.
- Required floor: 20,971,520 KiB.
- This unit's required request: 4,000,000 KiB.
- Admission headroom shortfall: **2,126,104 KiB**.

No compiler ran for this corrected attempt, no cap was increased, and no
other unit's process was signalled. All compiler processes previously
admitted for this unit had already exited. There is no pending background
compiler or admission waiter from this unit.

`mask-helpers.v.txt` preserves the remaining UNVERIFIED draft: generic byte
borrow extraction; zero-mask exact byte cases including borrow false
positives; first-zero/no-zero equivalence; strong syndrome and decoder-cut
projection from real word values; prefix and shifted-mask byte relations;
REV expression/byte correspondence; CLZ range/common-NUL high-bit relations;
and original-memory aligned-word progress and local pair formation. These
text snapshots are not imported by any proof target and are not claimed Qed.
The full entry/alignment/lookahead/decoder assembly is still absent. The
explicit remaining obligations are in `REMAINING.md`.

Verification summary:

- `05-inherited-build.log`: exit 0, full inherited target only.
- `06-mask-probe.log`: exit 1, the next byte-extraction rewrite failed after
  the new generic borrow lemma's Qed.
- `08-mask-probe.log`: exit 143, never admitted, no Rocq check occurred.
- `11-arithmetic-sanity.log`: exit 0, finite sanity checks only.
- `12-admission-blocker.log`: exit 0, exact resource evidence/own waiter stop.
- `13-retention.log`: exit 0, all 69 declarations and protected inputs intact.
- `14-source-audit.log`: exit 0 against origin base, `NEW totals: {}`.

Raw inherited assumptions are in `notes/a-strcmp-fix/31-assumptions.raw.log`
and are freshly printed by the inherited target in this run's log 05:
38 of its 42 completed declarations are closed. The four exceptions are
`strcmp_welltyped`, `strcmp_fix_byte_exit`, `strcmp_fix_byte_ccmp`, and
`strcmp_fix_weak_decoder_result`, each using only:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

No new transitive assumptions query executed after the block. The required
`tools/print-assumptions.sh` was read; its previous main-absence result is
preserved in `notes/a-strcmp-fix/32-main-absence.log`. Neither that inherited
absence result nor the finite arithmetic checks certify a new main theorem.
No `final_proof_model=gpt-6.1-sol` completion attribution is recorded.

Only local commits are authorized. Post-commit ancestry, whole-base diff
stat and clean status are recorded outside the checkout solely under
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-strcmp-complete/`.
