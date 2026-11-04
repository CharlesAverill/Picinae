# r03-list-insert-end — PARTIAL Astra handoff

Initial author: OpenAI gpt-6-astra, xhigh/priority. Final proof producer: NONE.
A new gpt-6.1-sol xhigh/priority fixer is required. No fixer was delegated.

Branch: `llm-proofs/r03-list-insert-end`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-d0b2e085`.
Prepared HEAD was exact e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole
parent `49956416928e5b6bb3928b54ae33e3b81091f006`. The initial status was clean.
The read-only fork-name check succeeded with no matching head (exit 0).
Only the prepared `t3/prove-list-insert-end` branch was renamed, then
`git merge --ff-only 4ff26413448da4d8f064b0273ac5472cc9de7e5a` succeeded.
The sandbox initially blocked network resolution and Git metadata writes;
network and metadata escalations succeeded. No automatic approval rejection.
No other branch changed, no worktree created, no installation, no publication.

Read the campaign plan and assigned row, BUILDING.md and Examples/claude/SKILL.md.
r01/r02 completed proof files were read through `git show` as templates only;
no source dependency or history was imported. Generated map, ISA, frontend,
ABI manifests and r00 remain unchanged. Root Dune adds exactly one module.

## One-shot result

Full source archived BEFORE build in `initial-attempt.v.txt`, SHA256
`3a16f73db7b594afa54058d6f624e819ff931481598e7cbe42dec49ed5c0d892`.
Exactly one full relevant build was run:

```sh
bash tools/record-command.sh notes/r03-list-insert-end/dune-initial.log \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInsertEnd_proof.vo'
```

**Exit 1**, first error at original line 165, `insert_end_memory_frame`.
`repeat rewrite getmem_noverlap ...` did not remove the six stores; final
`reflexivity` could not unify the untouched byte with the nested-write byte.
See the complete compiler stdout/stderr in `dune-initial.log`. This was a proof
failure, not a reported OOM. No repair/rebuild cycle was attempted.

Dune completed the required core/ISA, r00 and generated-map dependency objects,
but did NOT produce a successful unit `.vo`. There is no successful full unit
target command. No `.vos` or skipped proof checking was used.

Four Qed blocks were processed before failure and are retained verbatim:

- `insert_end_nwc`
- `insert_end_welltyped`
- `insert_end_register_frame`
- `insert_end_memory_fields`

They are not a successful whole-module or transitive-assumptions certificate.
The failing and all later proofs are now `Abort`. Their original attempts are
in the archive. `check-statements.py` proves every statement, definition and
all non-proof text are unchanged. The post-cleanup file was not compiled:
that would be a second Astra cycle. There are no admissions or new axioms.

## Proposed contracts, NOT certified execution results

`insert_end_exact`: satisfies_all for the actual finite map from 0x5c to BX
at 0x70, exact chronological memory and scratch/flag effects.
`insert_end_at_bx`: original-memory insertion postcondition on actual traces.
`insert_end_trace_returns`: append the ordinary modeled BX step, retaining post.
These statements remain aborted, not exported proved constants.

Domain: 32-bit nonnull aligned nonwrapping L20/P20/I12/B12; new item P disjoint
from header and neighbor regions. The nine relevant WORDS (six write targets,
L.index, P.value and P.owner) are separate; the existing objects themselves are
not required pairwise disjoint. In particular I=B=L+8, I=B at an ordinary item,
and sentinel/ordinary neighbor combinations are permitted. The entry has
original L.index=I, I.prev=B, B.next=I. It does not assume desired output links.
Read/write permissions are exactly the three read and six write words.

Post: P.next=I, P.prev=B, B.next=P, I.prev=P, P.container=L, count increments
modulo 2^32. Preserve L.index/P.value/P.owner and every byte outside the six
actual writes. R2=B, R3=new count, exact modeled NZCV; R0/R1, R4-R12, SP/LR,
permissions and temporaries preserved. No new result for void return.
`insert_end_count_no_overflow` uses only original count < 2^32-1.

`insert_end_local_empty_witness` and `insert_end_local_nonempty_witness` propose
typed/readable/writable entry witnesses with (L,P,I,B)=(4096,8192,4104,4104)
and (4096,8192,12288,4104), respectively, and counts 0/1. These are local
contract witnesses, not a finite circular-list representation. Their proof
attempts were not reached. No termination or existence of a complete execution
trace is established. `insert_end_ordinary_return_nonvacuity` proposes an
inhabited ordinary BX step; it too is unchecked. LR must be odd and <0xfffffff0;
no hardware EXC_RETURN, scheduler, IRQ, TCB, CPU tunable or callee contract.

## Audits and fixer obligations

Unit source audit against base: exit 0, no lexical admission/axiom/parameter.
Full repository source audit and exact ancestry audit recorded separately.
Statement preservation: exit 0. This does not establish transitive soundness.
Print Assumptions was NOT run for the incomplete module: the helper first
builds its target, which would violate the stop-after-first-failure rule.
No raw unit assumptions output exists. Existing core functional extensionality
`Stdlib.FunctionalExtensionality.functional_extensionality_dep` is documented
by e00; this is not a claim that these unfinished main theorems have only that
assumption. r00's inherited accepted raw output is in
`notes/r00-list-model-fix/20-final-assumptions.log` (19 closed facts).

The Sol fixer must restore the archived proofs, repair the first frame lemma,
then validate all downstream statements/proofs under the same resource cap.
Keep statements unless genuinely wrong; explain every statement change.
Inspect the fixture and permission witnesses and the exact symbolic execution,
not merely the first failure. Obtain full `.vo`, all main/helper/frame/witness
Print Assumptions through `tools/print-assumptions.sh` with
`PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536`, and inspect transitive imports.
No imported admitted proof qualifies. Full finite-list/cardinality refinement
remains r47; inherited lifter/ISA provenance is not a binary refinement proof.
