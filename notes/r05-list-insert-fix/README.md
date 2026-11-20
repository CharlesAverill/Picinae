# r05-list-insert-fix — PARTIAL / WIP, stopped by Charles

Initial author: gpt-6-astra, xhigh/default. Iterative fixer: gpt-6.1-sol,
xhigh/default. No final proof producer for the full contract.
Branch: llm-proofs/r05-list-insert-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-1b541d85.
Authorized checkpoint: dae969a921f24e3541b7b406c5f6be7618e520f6.
Pinned origin: 49956416928e5b6bb3928b54ae33e3b81091f006.

Charles ordered immediate wrap-up. No further proof/compiler retry was run.
The gated interactive shell was exited, releasing its lease. A diagnostic
build queued at the time of that order was rejected by automatic approval
review because it would violate the stop order; it did not run. No permission
or retry is sought. No installations, remote writes, or subdelegation.

## Actual results

No successful full target .vo. No main correctness/assumptions certificate.
The initial capped build in 05-dune.log compiled all relevant dependencies,
then failed in si_result_membership. Repairing its partition rewrite allowed
all 13 original prefix theorems through si_result_sorted to reach Qed and
Print Assumptions (all print `Closed under the global context` in 06-dune.log).
These include the original nwc/typing/register frame, exact original-byte
write frame, typed writes, split/cut partition, result length/membership,
max cut, split bounds, and pure sorted insertion. This is pure list/memory
helper coverage, not a certified machine function theorem or target .vo.

Additional endpoint, spill separation, original-stack word preservation,
and typed load helper scripts passed the compiler before later failures.
The guarded POP construction reached the jump elaboration in 12/13/14 logs;
14 failed `Not convertible`. With explicit jump width in 15-dune.log the
compiler instead exhausted the unchanged 2,500,000 KiB cap. Its exact location
past the last printed prefix assumption is not established. Diagnostic prints
added afterward are uncompiled. No successful claim is made for the POP,
return, or nonvacuity proofs. Their current Qed scripts are WIP, not certificates.

si_memory_refinement, sorted_insert_correct, sorted_insert_at_pop and
sorted_insert_trace_returns remain Abort. All their original statements and
all original definitions are preserved. The original failed scripts remain
verbatim in notes/r05-list-insert/initial-attempt.v.txt. Current return and
witness repair attempts are retained in the proof file; they have not passed
a full .vo build. No Admitted/admit, Axiom or Parameter was added.

## Evidence and limits

Every launched compiler used the required shared gate at 2500000 KiB,
stack 65536, Dune -j1 and --cache=disabled. 11-gated-session.log records the
single gated shell enclosing sequential recorded builds 12 through 15;
its exit and lease release are saved. No concurrent unit proof compilers.
04-dune.log is an early gate failure before compilation: the sandbox could
not create the shared admission lease. Authorized escalation was used for
the gate thereafter. The first retry waited for resource admission; no cap
or shared configuration was changed. 08-resource-snapshot.log records the
read-only resource evidence during the wait.

07-source-audit.log passes the scoped source audit at that intermediate
source. 09-preservation.log passes preservation of all 66 original source
declarations and original evidence/map. 10-ancestry.log verifies the exact
13-commit authorized prerequisite forest, merge base, scoped changes, diff
stat and status. The generated IL SHA256 remains
379c3edfa2edc460bf9d9e466804ad492c291778bb49086ffb2e3a21003b3ecc;
initial source archive remains
67ef3070eef5e485b7119be86fa209e2bc0e8dc2bc50c7a8febd283fd85636bf.
Root dune and all inherited files other than the assigned proof are unchanged.

tools/print-assumptions.sh has not been run for the repaired module because
no full target succeeded. The only raw assumptions evidence is prefix output
in failed build logs. The inherited FE boundary must still be audited for
any eventual main theorem. No binary/lifter refinement, full function partial
correctness, termination, scheduler, hardware, or IRQ claim is established.

Next step after coordinator authorization: localize the OOM without increasing
the cap, finish and check the original-memory splice and all loop/max branches,
complete witnesses and actual POP return, then obtain a successful full target
and raw transitive assumptions for every main theorem. Preserve this WIP and
all original Astra evidence. This unit is explicitly PARTIAL, never DONE.
