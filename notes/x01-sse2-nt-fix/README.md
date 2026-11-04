# x01-sse2-nt-fix — continuation work log

State: PARTIAL. Checked tail/staging/first-page support and public-entry NT
dispatch; no full-entry NT strategy theorem.
Author checkpoint: Astra, c63095989bf5d49153046d2285b3e27580346fde.
Fixer: Sol. Final-proof-model completion attribution is withheld until the
whole assigned unit is complete.

Branch: llm-proofs/x01-sse2-nt-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-010907e3.
Allowed ancestry: origin/llm_generated_proofs pinned
49956416928e5b6bb3928b54ae33e3b81091f006 -> e00
71470bffba65392adf1873a3df9f0cf0ca4f1ac9 -> author checkpoint -> local fixes.
The initial status was clean at e00. The history recorder subsequently sees
only this unit's new untracked notes. The first sandboxed collision query
failed DNS; the elevated read-only query in 01-collision.log succeeded with
empty result. Only the prepared local branch was renamed. No remote writes.

Read plan.md (including effective x01/fix rows and current handoff), BUILDING.md,
Examples/claude/SKILL.md, original README and 07-initial-nt-build.log, and the
new proof file. Charles's instructions override the skill's admission and
resource advice. No new dependency installations or shared environment edits.
All builds/queries use the existing read-only wrapper, memory 8000000 KiB,
stack 65536 KiB, disabled Dune cache, and -j1. One compiler at a time.

## Statement and proof corrections

To be filled with exact checked changes and evidence. Preserve original
predicates/statements unless an error requires an explained correction.

Corrections so far (all author statements and predicates preserved):

- `nt_row_advance`: reduce the predicate application and use propositional
  reasoning (`intuition lia`) for the union of four 16-byte intervals. Plain
  `lia` does not discharge this goal. A braced subproof, instead of the
  original bullet, returns to all outstanding store side conditions.
- `nt_done_initial`: give the two implication directions explicitly; the
  original `try lia` already closed the last branch before `left; exact H`.
- `nt_done_next_chunk`: name the positive-page premise POS, avoiding a later
  `H` binder collision caused by bare `intros`.
- `nt_staged_finish`: handle all four disjunction cases explicitly; the
  original semicolon/bracket script distributed two tactics over four goals.
- `nt_tail_loop`: explicitly convert the destination/source store projections
  to their register arithmetic before applying `lia`/`f_equal`. This unfolds
  only the store updates, without letting arithmetic tactics inspect memory.
- `memcpy_nt_tail_nonvacuous`: remove `unfold madd` (no such definition;
  `+` modulo 2^64 is notation here), and reduce the empty-set application.
- First-page store set reasoning: reduce applied predicates and use
  propositional reasoning, as in the row lemma. Successfully validated in logs 18 and 21.

Logs 05–17 preserve the actual commands, diagnostics, exits and resource
information, including failed intermediate repairs. Log 05 is a fresh full
kernel build of the inherited closure ending at the original line-52 failure:
18:00 elapsed, max RSS 3541916 KiB, zero swaps. Log 16 reached beyond the
successful tail theorem to the witness's missing `madd` identifier. Neither
partial compilation nor source `Qed` text substitutes for a successful .vo.

## Checked helper coverage

`18-witness-bound.log` is the first successful full new `.vo` build (exit 0,
2:14.92, RSS 1892880 KiB, zero swaps). `21-nonvacuity-syntax.log` successfully
builds the expanded helper file (exit 0, 2:44.71, RSS 2049592 KiB, zero swaps).
The temporary syntax failure in log 20 was a missing space between an or-pattern
separator and `->`; log 21 corrects it. No author statement changed.

- `memcpy_nt_tail_correct`: `satisfies_all` partial correctness of the real
  lifted two-page tail at 0x1c4ccb or four-page tail at 0x1c4e73. At the
  respective RET cuts 0x1c4d29/0x1c4ed1, RAX=d, RSP=rsp, and `copied` means
  original-source bytes in [0,n) plus the full outside-destination byte frame.
  Premises: modeled AMD64 state; modular nonoverlap `nov d s n`; n<2^64;
  d+n<2^64; c+64<n; c<=n; n-c<2^32; already copied prefix [0,c);
  RDI=d+c, RSI=(s+c) mod 2^64, RDX=n-c, RAX=d, RSP=rsp. Source addresses
  use the model's modulo-2^64 loads; no separate source nonwrapping premise
  is present. There is no total-size cap below the AMD64 range restriction.
  This suffix reads no threshold or CPU global. It assumes a prefix, not a
  completed copy. The theorem does not establish termination.
- `nt_tail_final` covers the final four actual loads/stores, including direct
  final-block entry when n-64<=c, c<=n, 64<=n and the other tail-state fields
  hold. `nt_tail_loop` checks both real 64-byte loop bodies and their branches.
- `memcpy_nt_first_page_stores`: four real MOVNTDQ instructions, starting at
  0x1c4c6d/0x1c4dcd and stopping at 0x1c4c80/0x1c4de0. Requires modeled
  state, `cpy m M d s W`, W contained in [0,n), n<2^64, o+64<=n, RDI=d+o,
  and four low XMM lanes equal to the original-memory 16-byte source loads
  at s+o+[0,16,32,48]. It adds [o,o+64) and preserves the outside-written-set
  frame. It does not need nonoverlap because the supplied original-source
  values are already loaded. It does not prove the other pages or counters.
- `nt_row_advance` proves the abstract-memory analogue under genuine nov,
  W contained in [0,n), n<2^64, and o+64<=n. `nt_staged_advance` advances
  one page of a row for a in [1,64], i<64, q<pages and a complete next chunk
  within n. `nt_done_chunk`, `nt_done_next_chunk`, `nt_staged_finish` and
  `nt_staged_bound` prove the offset-set bookkeeping, for positive pages
  where required. These are not execution lemmas for the bulk loops.
- `nt_chunk_positive` is the exact arithmetic equivalence between a positive
  floor((n-align)/chunk) counter and align+chunk<=n, for pages>0. The optional
  `nt_chunk_positive_from_threshold` derives positivity for 2 or 4 pages from
  threshold>=16448 and n>threshold, with no artificial size upper bound.
  This optional tunable condition is explicit and is NOT connected to an
  actual initial or updated global load by an execution theorem here.
- Nonvacuity: `memcpy_nt_tail_nonvacuous` exhibits an empty copied prefix
  with d=4096,s=8192,n=128. `memcpy_nt_first_page_stores_nonvacuous` satisfies
  every first-page-store premise with empty W and actual zero-memory lane
  loads. `nt_staged_initial_witness` constructs the initial head relation
  from four real-sized source stores for arbitrary memory contents;
  `nt_staged_advance_nonvacuous` simultaneously inhabits all initial staged
  advance premises for pages=2 and pages=4 (d=65536,s=131072,n=16448,a=64).

Inherited `memcpy_welltyped`, `memcpy_nwc`, and
`memcpy_preserves_callee_saved` remain available unchanged; this continuation
imports only the clean SSE2 helper modules, never the admitted AVX NT module.
The ABI's RSP statement is at the RET cut, before executing RET's stack pop.

## Assumptions already checked

Log 19 uses `tools/print-assumptions.sh` after the successful log-18 .vo.
The tail main theorem, tail execution lemmas and first-page execution lemma
report exactly this inherited baseline, with no admitted imported theorem:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The queried row, set/staging helpers and tail nonvacuity theorem print:

```text
Closed under the global context
```

These are transitive assumption queries, not just lexical source searches.
Final queries for the additional witnesses/dispatch are recorded separately.

## Original scope still outstanding

This is PARTIAL for x01. A successful tail/dispatch helper build is not a
full-entry non-temporal memcpy theorem. Required remaining work:

1. NT head/opposite-overlap/alignment from 0x1c4bad to actual bulk staging.
2. Actual two-page eight-vector and four-page sixteen-vector load/store
   bodies, all 64 inner iterations, 8192/16384-byte outer increments, and
   bottom-tested counters connected to genuine dispatch/tunable conditions.
3. Explicit handling of the second threshold read AFTER head stores. Either
   establish a destination/global frame fact or reason with the changed
   memory; an initial-global value cannot silently stand in for that read.
4. Post-bulk prefix/remainder state and both direct-final and looping tail
   joins, then a full-entry NT strategy invariant/main theorem and witness.
5. x05 all-size composition is separate and is not claimed here.

The generated lift remains unchanged. Binary provenance remains inherited
from exact Ubuntu 2.35-0ubuntu3.12, SHA256
9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
The user-provided e01 inventory reports all 313 boundaries matching and 12
PREFETCHT0 annotations rendered NOP. No e01 branch was imported and this
continuation does not revalidate the binary or claim those lifting findings
resolved. MOVNTDQ is modeled as an ordinary store, SFENCE/prefetch without
cache/order effects; there is no CPU-feature, fault, concurrency, termination
or lifter-soundness result.

## Public-entry dispatch extension

`amd64_memcpy_nt_dispatch_proof.v` adds a separate, deliberately scoped
`memcpy_nt_dispatch_correct` execution theorem. Log 33 successfully kernel
builds its full .vo (exit 0, 0:36.03, RSS 1493380 KiB, zero swaps).

Starting at the real public entry 0x1c4870 with modeled System V AMD64 state,
MEM=m, RDI=d, RSI=s, RDX=n, RSP=rsp, n>128, genuine modular nov d s n, and
initial m[0x3215a8]<n, the state at 0x1c4bad has memory/d/s/n/rsp unchanged,
RAX=d, low XMM0=original source[0,16), RCX=(d-s) mod 2^64. No REP-dispatch
or other threshold global is assumed. This segment requires no destination
nonwrapping or d>=64 premise and has no artificial upper-size cap; register
modeling provides 64-bit inputs. It stops BEFORE NEG RCX and the NT head.
`memcpy_nt_dispatch_nonvacuous` supplies a concrete typed input satisfying
all premises (d=4096,s=8192,n=256, zero memory/threshold). This witness is
for dispatch only, not a claim that a zero NT threshold makes bulk counters
safe. `nt_dispatch_zero_load` proves the zero-memory qword fact symbolically
for arbitrary address.

Dispatch proof corrections and resource findings:

- Log 22: replace an inappropriate `assumption` for the computed RAX=d by
  reflexivity (log 25).
- Logs 25/26: capped OOMs (RSS 7355240/7356192 KiB); no cap increase. Convert
  record projections to their explicit scalar/register goals before solving
  the unchanged-memory/RAX/XMM facts. This avoids conversion searching through
  symbolic state/memory. Log 27 reaches the end of the tactics at 1271604 KiB;
  its temporary final idtac encounters `No such goal` after reflexivity.
- Log 28: removing diagnostics initially left empty `all:` selectors; clean
  those selectors before final proof checking.
- Log 29: the tail target passes, but the dispatch module still reaches OOM
  (RSS 7354284 KiB). Prove the concrete zero-memory global load with the
  symbolic `getmem_spec`/bits lemma rather than kernel reduction at the large
  numeric global address. Log 33 then passes the full module, including Qed
  and the witness. These historical OOMs are resolved for this segment; they
  are not claimed as an outstanding blocker to the unchecked bulk strategy.

Failed source snapshots `dispatch-attempt-26.txt`/`dispatch-attempt-29.txt`
are diagnostics only, not compiled prerequisites or certified Qeds.
The final .v contains only successfully checked declarations.

## Final validation and local handoff

Final full-target command in log 34 (exit 0, 0:33.88, peak RSS 1495356 KiB,
zero swaps; helper source had also rebuilt successfully in log 29):

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    ulimit -v 8000000
    ulimit -s 65536
    /usr/bin/time -v dune build --cache=disabled -j1 --display short \
      Examples/claude/amd64_memcpy_nt_proof.vo \
      Examples/claude/amd64_memcpy_nt_dispatch_proof.vo
  '
```

Both targets have real successfully checked .vo files, using Dune `mode vo`,
not skipped checking. The inherited closure was checked fresh in log 05.
Log 34 recompiles the final dispatch source after diagnostic removal.

Assumptions commands in logs 19, 35, 36 and 37 all exit 0, with
`PROOF_MEMORY_KB=8000000 PROOF_STACK_KB=65536`, the same wrapper and
`tools/print-assumptions.sh`. Every exported main and critical helper is
queried only after its successful full build. The dispatch theorem reports
exactly the functional-extensionality block quoted above. Its concrete
witness and zero-load lemma are closed. Log 36 rechecks the final tail and
first-page execution theorems (functional extensionality only); every new
counter/initial-stage/nonvacuity helper is closed. Log 37 rechecks inherited
welltyped (functional extensionality only), nwc and callee-saved (both closed).
No admitted imported fact occurs in these transitive assumption inventories.
The inherited FunctionalExtensionality assumption is the documented e00
baseline, not a new declaration in this unit.

Source audit with the exact pinned base reports `NEW totals: {}` (exit 0).
No admissions, axioms or parameters occur in either new proof artifact.
The preserved-author-declaration check reports all 16 original theorem/lemma
statements and all 9 definitions unchanged verbatim (exit 0).
Ancestry/lift audit log 30 checks the exact pinned base, sole-parent e00 and
author links, assigned branch, unchanged generated lift (SHA256
7c981ab264263904273b59b80b83f847644f2a7a2e3174f99ae37a5a43a64c0e),
full commit list, diff stat and working status. Final source/statements/whitespace
checks are in logs 38/39. Only the new dispatch module is added to root Dune's
explicit module selection; the author had already selected the tail module
and its required SSE2 dependencies. No glob or unrelated proof is selected.

State remains PARTIAL. There is no main theorem composing the checked entry
dispatch, unproved head/bulk loops and checked tail. No full memcpy-size,
overlap, termination or binary-soundness claim is made. Final-proof-model
completion attribution remains unset. This continuation did not install,
push, publish, create a PR, subdelegate, modify the original author branch,
or edit shared campaign files. Only the assigned local fix branch is committed.

Immutable final commit/hash, clean status and allowed three-commit ancestry
are recorded after commit in the permitted external unit directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x01-sse2-nt-fix/`.
This avoids changing a commit to embed its own hash. Staging/commit commands
are recorded there as well; all compiler, assumptions and source-audit logs
remain under this repository's notes/x01-sse2-nt-fix/.

Log 40 is the last full pair build after clarifying the dispatch header's
partial-correctness wording: exit 0, 0:28.73, peak RSS 1495588 KiB, zero swaps.
A staged whitespace check passes for both proof sources and Dune. Raw compiler,
/proc/limits and Print Assumptions logs retain native trailing spaces verbatim;
a repository-wide whitespace check consequently flags those evidence lines.
They are deliberately not normalized or presented as a source-code failure.
