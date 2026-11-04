# r05-list-insert — PARTIAL Astra handoff

Initial author: **gpt-6-astra, xhigh/default**. No final proof producer.
No second Astra proof repair or compiler cycle was performed. The coordinator
must create a NEW **gpt-6.1-sol, xhigh/default** fixer if continuing this unit.
No subdelegation, installation, push, PR, or remote write occurred.

Branch: `llm-proofs/r05-list-insert`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-c73a57d6`.
Assigned prerequisite: `4ff26413448da4d8f064b0273ac5472cc9de7e5a`.
Pinned origin: `49956416928e5b6bb3928b54ae33e3b81091f006`.

## Actual validation result

The ONE full-target command in `06-dune-initial.log` exited **1**:

```sh
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r05-list-insert --memory-kib 2500000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2500000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInsert_proof.vo'
```

The helper waited for available RAM, admitted the process, and released it
with exit 1. No cap increase or bypass. Relevant dependencies compiled to
full `.vo`, including Picinae_armv6m, armv6m_list_model and the unchanged
generated vListInsert map. **The requested proof target did not succeed.**
No successful standalone target command is claimed.

Failure in `si_apply_frame`, initial source line 206, characters 76–77:

```text
Error: Cannot infer this placeholder of type "N" in
```

The offending line is the `change (... = _)` statement. Full environment,
compiler stdout/stderr, command, gate messages and true exit code are in the
log. The initial source is byte-for-byte in `initial-attempt.v.txt` with
SHA256 `67ef3070eef5e485b7119be86fa209e2bc0e8dc2bc50c7a8febd283fd85636bf`.
This is a first elaboration failure, not evidence that later proofs succeed.

Only these three prefix facts reached Qed and Print Assumptions:

- `sorted_insert_nwc`: finite map independent of store.
- `sorted_insert_welltyped`: generated map typing.
- `sorted_insert_register_frame`: preservation of variables untouched by
  the body; R4/R5/SP are excluded here because PUSH/POP mutate them.

Their verbatim output is `Closed under the global context` for each, saved
in `assumptions-raw.txt` and the full compiler log. The target has no `.vo`.
The source retains those three checked prefix proofs; the failed and all
later attempts are `Abort`. Their statements and all definitions are retained
exactly, checked by `check-statements.py`. No new admission or axiom is added.
The post-Abort source has NOT been rebuilt, as required by the one-shot rule.

`tools/print-assumptions.sh` was read but cannot certify missing main constants;
its implicit rebuild would start a prohibited second Astra cycle. See
`assumptions-status.txt`. A successful fixer must run the helper, inspect all
transitive assumptions, and disclose inherited FE if it appears. Three closed
prefix queries do not certify the proposed functional theorem.

## Intended contract, not proved coverage

The new proof file contains a full finite circular list specification over
32-bit little-endian fields: list/sentinel layout, sorted value/owner node
records, exact next/previous/container links, count modulo 2^32 and index
membership. The new item, old nodes and list objects are nonnull, aligned,
nonwrapping and mutually byte-disjoint; the sentinel is embedded at L+8.
SP is 8-byte aligned, at least 12 and below 2^32. Its 12-byte spill area is
separate from those objects. Permissions require read AND write access for
all five fields of each item/list plus spill words (a deliberately explicit,
satisfiable uniform permission requirement, broader than actual accesses).
No special CPU tunable, external callee, IRQ or hardware premise is assumed.

Entry is 0x72, the loop cut is 0x7e, store join 0x88, and POP exit 0x9a.
The max-value branch 0x9c/0x9e chooses sentinel.prev. Otherwise traversal
inserts after all equal values. Output is the exact prefix/new/suffix list,
with sortedness, membership/cardinality helpers, preserved owners/index,
container assignment and original-byte frame. Stack writes and the six body
stores are recorded in actual order. NZCV have the final ADDS semantics.
The actual return is POP {r4,r5,pc}, with the inherited guarded BX operation,
not a literal BX LR instruction. The contract restores R4/R5/SP and lands at
LR & 0xfffffffe under odd LR < 0xfffffff0. No EXC_RETURN claim.

Main pending statements:

- `si_memory_refinement`: original-memory writes imply the new ring and frame.
- `sorted_insert_correct`: `satisfies_all` using explicit loop/join/exit invariants.
- `sorted_insert_at_pop`: actual finite trace reaches the specified POP state.
- `sorted_insert_return_step` and `sorted_insert_trace_returns`: actual guarded
  POP return, register restoration, flags and final memory.
- `sorted_insert_nonvacuity`: typed entry states for empty, singleton and
  two-node lists; includes equal-value insertion and embedded sentinel alias.

All these are **unproved**, as are the helpers after the first three Qeds.
The initial scripts require substantive Sol completion beyond the first
placeholder. Do not weaken the contract or retain an assumption of the result.
Statements must remain unchanged unless genuinely wrong; explain any change.
No termination, complete trace existence, whole-kernel, scheduler, hardware
or independent binary/lifter refinement is established. Inherited e03/e05
provenance remains the trust boundary.

## History and source evidence

Prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent was pinned origin. A successful read-only `ls-remote`
returned no matching fork branch. Only the prepared local branch was renamed.
The initial sandbox DNS check failed; the authorized network retry succeeded.
Git metadata was read-only in the sandbox, so the authorized exact ff-only
merge and branch rename used escalation. No auto-review rejection occurred.

The exact assigned prerequisite forest has 11 commits above origin, including
accepted r00 Astra/Sol history. It was fast-forwarded, not cherry-picked from
a fork branch. r03/r04 proof templates were read from the supplied worktrees;
neither branch was imported. `audit-ancestry.py` checks the complete forest,
scoped unit commits, pinned merge base and unchanged generated map.

Generated map SHA256 remains
`379c3edfa2edc460bf9d9e466804ad492c291778bb49086ffb2e3a21003b3ecc`.
Root dune adds only `Examples.FreeRTOS.armv6m_vListInsert_proof` to the existing
explicit list. Source audits against pinned origin exit 0, both full-tree
and scoped: no new `Admitted`, `admit`, `Axiom` or `Parameter`. Full-tree
baseline findings are unrelated existing modules, not a transitive certificate.
All exact commands/logs are recorded with `tools/record-command.sh`.
