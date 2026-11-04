# r27-find-task author handoff

Status: PARTIAL. The single full-target build failed (exit 1). This is not a
completion certificate. Initial author is gpt-6-astra, xhigh, default tier.
Final proof producer is not yet certified. No fixer delegate was launched.

Branch: `llm-proofs/r27-find-task`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-1f7f6596`.
Assigned prerequisite: `4ff26413448da4d8f064b0273ac5472cc9de7e5a`.
Pinned origin: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Prepared HEAD was `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole
parent is the pinned origin. After the successful empty remote-name check,
only the prepared branch was renamed, then fast-forwarded to the assigned
prerequisite. No other branch was changed and no publication was attempted.
The prerequisite includes the disclosed r00 author and Sol repair history;
the permitted ancestry is its entire exact rev-list union, not just e00.

The new file is `Examples/FreeRTOS/armv6m_prvSearchForNameWithinSingleList_proof.v`.
Only this proof is added to root Dune's explicit modules, with the
`r27-find-task` alias. Existing lift and list-kit modules were already selected.
All generated artifacts, ISA, fixture and imported proofs remain unchanged.

## Proposed statements and scope

- `search_correct`: finite-list and inner-byte-loop partial correctness of
  the actual generated finite program, entry 0x5d0 to pre-POP cut 0x60e.
- `search_post_at_pop`: trace-conditioned first-match result and stack image
  at that cut.
- `search_return_step`: actual POP instruction step to the ordinary Thumb
  address in saved LR, with full caller postcondition.
- `search_caller_result`: composition of those obligations.
- `search_result_first_match`: pure specification characterization, separate
  from execution correctness; `search_matchb_spec` relates byte predicates.
- `search_entry_satisfiable`, `search_empty_entry_satisfiable`: arbitrary
  admissible inputs and a concrete empty-list nonvacuity family respectively.
- `search_nwc`, `search_welltyped`, `search_saved_bytes_frame`: ancillary
  generated-program and memory-image properties, not functional correctness.

All 19 author statements and the full initial proof script are saved in
`initial-attempt.v.txt`. `check-statements.py` checks exact statement equality.
The `.v.txt` is archival text, not a Dune module or an assumptions certificate.

The input list is represented by a finite next-link chain ending at the
list+8 sentinel. Its count field equals the chain length. Owners are nonnull
84-byte TCB objects. No name is required to match or contain NUL. The result
is the owner of the first item with equal bytes through a common NUL before
index 16; 16 equal nonzero bytes do not match. Byte mismatch, equal nonzero,
equal NUL and bound exhaustion are all present in the proposed invariants.

The list, items and TCBs are nonnull/aligned/nonwrapping; query has 16
nonwrapping bytes. SP is 8-byte aligned, at least 20, below 2^32. Stack writes
are disjoint from all those input ranges; input/input overlap is otherwise
allowed if representation facts coexist. Permissions cover the read ranges
and the writable/readable 20-byte stack frame. LR is odd and below 0xfffffff0.
These are local ABI/model hypotheses, not hardware or scheduler invariants.

The actual return instruction is `POP {r4,r5,r6,r7,pc}` at 0x60e, whose IL
uses `armv6m_bxwritepc`; there is no standalone `BX LR`. This is why the
return theorem names and steps POP, rather than inventing a BX instruction.
Post-return memory retains saved R4,R5,R6,R7,LR below initial SP. The frame
compares all other bytes to original memory and restores R4-R11/SP/LR.
This unit has no calls, literals or global references. It cannot establish
IRQ/concurrency behavior, hardware/lifter refinement, termination or
whole-kernel/cardinality properties.

## Evidence and reproduction

`01-before.log`, `02-remote-name.log`, `03-prepared.log`: initial clean state,
remote collision check and prerequisite ancestry; `audit-ancestry.sh` accepts
only the exact assigned prerequisite plus explicitly supplied own commits.

`05-build-initial.log` records the sole full `.vo` invocation, compiler output
and true exit status. It goes through the mandatory shared resource helper,
uses the read-only isolated environment, 2500000 KiB address-space cap,
65536 KiB stack, `--cache=disabled -j1`, and this exact target:

```
Examples/FreeRTOS/armv6m_prvSearchForNameWithinSingleList_proof.vo
```

No installation, environment mutation, shared campaign edits, or remote writes.
The resource helper's own admission bookkeeping is the only shared write
outside Git metadata; it is invoked exactly as assigned.

`07-source-audit.log` uses base 4995641 and inventories the entire repository.
No new admissions, axioms or parameters were found. Baseline counts are
7 Admitted, 1 admit, 89 Parameter; lexical absence is not a trust certificate.
`08-provenance.log` independently checks the pinned tasks.c and generated
source hashes, manifest closure and compiler-derived object layout. Source
excerpt and relevant field offsets are saved alongside it.

`assumptions-query.v.txt` is the intended full query list, not raw output.
A complete unit must run `tools/print-assumptions.sh` under the same resource
gate with `PROOF_MEMORY_KB=2500000 PROOF_STACK_KB=65536` and inspect every
transitive assumption. The accepted baseline contains
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
no claim about this unit's actual transitive assumptions is made before its
full target succeeds. Any admitted dependency disqualifies completion.

## First-attempt outcome and required handoff

The gate admitted the job after 26 wait messages. Dune built the core, ISA,
list model and unchanged generated lift, then failed in the new proof at
initial source line 241, characters 39-48, in `search_skip_prefix`:

```
Error: Found no subterm matching
```

The full expanded Boolean expression and compiler diagnostics are preserved
verbatim in `05-build-initial.log` (exit 1). In this initial script,
`cbn in B` expands `search_name_matchb` while the goal still contains the
folded predicate, so `rewrite B` fails. No memory-limit failure was reported.
The compiler accepted the preceding seven Qed commands in this invocation:
`search_nwc`, `search_welltyped`, `search_saved_bytes_frame`,
`search_matchb_spec`, `search_match_at_zero`, `search_mismatch`,
`search_exhausted`. This does NOT constitute a full module build or a
transitive assumptions audit; no unit `.vo` was produced.

Per Charles's Astra policy, there was no repair or second compiler run after
this failure. The failed lemma and all twelve failed/unvisited proof bodies
(including it) are now Abort; every statement is unchanged. Their exact
initial proof bodies remain in `initial-attempt.v.txt`. The seven preceding
completed helper scripts remain as originally checked, without changing
statements or adding assumptions. The handoff source itself was not rebuilt.

The new Sol xhigh/default fixer must retain these author statements unless
genuinely wrong and explain every change. It must complete the pure prefix
and first-result facts, witnesses, actual loop execution, all byte branches,
original-memory stack separation, and the actual guarded POP return frame.
In particular the unvisited `search_correct` and return proof scripts are
initial attempts, not certified semantic composition. No functional theorem,
whole-function memory/callee frame, or caller-result theorem is completed.

No successful new full-target command exists. `tools/print-assumptions.sh`
was not run: it would rebuild the failed target, contrary to the immediate
handoff rule, and the theorem constants are unavailable. No raw assumptions
output or closed-transitive-trust claim exists for this unit. The inherited
FE assumption is documented as baseline context only. A lexical pass is
insufficient to certify absence of imported admissions. The final producer
is therefore unassigned, not gpt-6-astra.

The first mechanical Abort-packaging pass was caught by the statement checker
(`09-final-statement-preservation.log`, exit 1): its multiline-only Qed matcher
skipped over a one-line helper proof and removed the following declaration.
Packaging was regenerated from the immutable snapshot with a line-independent
terminator matcher. `13-packaged-statement-preservation.log` passes all 19
verbatim statements. This was a packaging correction, not a proof repair or
compiler rerun. `14-packaged-source-audit.log` is the final source audit.
