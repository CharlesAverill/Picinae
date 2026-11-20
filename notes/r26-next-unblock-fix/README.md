# r26-next-unblock-fix — validation in progress

Initial statement/proof author: OpenAI gpt-6-astra, xhigh/default.
Assigned fixer: OpenAI gpt-6.1-sol, xhigh/default. Final proof producer is
uncertified until successful full target and transitive assumptions queries.

Prepared worktree: `/home/charles/.t3/worktrees/Picinae/t3-539c20e7`.
Local branch: `llm-proofs/r26-next-unblock-fix`. Local only; no publication.

Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, with sole
parent pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`. After an empty
successful read-only `ls-remote`, only the prepared branch was fast-forwarded
to assigned checkpoint `9cdc8b9ede899efa594dc84a55f33e85616c9091` and renamed.
Allowed pre-unit history is exactly origin..checkpoint. Original Astra branch,
archive, logs, map, generated IL, and prerequisites are preserved unchanged.
The initial sandbox DNS failure was retried with approved read-only access.

The exact archived initial attempt was restored before the first Sol build.
`check-statements.py` checks all 16 original statements and every original
definition, plus byte equality of the archived source against the checkpoint.
`06-provenance.log` independently checks the existing lift SHA256, source
hashes, actual List_t offsets and immutable global literal addresses.

Every compiler/query uses the required shared resource gate with this unit's
2500000 KiB address-space limit and 65536 KiB stack. Dune runs full `.vo`
mode, `--cache=disabled -j1`. No dependencies installed; shared toolchain is
read-only. No concurrent proof compilers. Gate waits are admission waits,
not compiler failures. Commands and true exit codes are recorded in logs.

Contract scope remains the archived author's: sequential ARMv6-M IL partial
correctness, both delayed-list count branches, original memory head reads,
exact single output word and bytes, frame and ordinary odd-LR guarded return.
Only typed initial store is required for the main theorem; executable traces
supply permissions. Modular aliasing is allowed because reads precede the
store. Byte frame uses explicit nonoverlap. No list-cardinality, scheduler,
IRQ, hardware, totality, C-memory safety or binary/lifter-refinement claim.

## Final status: PARTIAL — Charles ordered immediate wrap-up

No main theorem is exported or certified. The exact restored author attempt
ran out of memory at the new 2500000 KiB cap (05-restored-build.log, exit 1),
after reaching the two branch postcondition goals. The subsequent diagnostic
query was admitted shortly before wrap-up: it printed both symbolic branch
postconditions, then loaded the syntactic-rewrite candidate and also reported
Fatal error: out of memory. See 08-diagnostic.log for the true exit status.
No successful repair build or assumptions query completed. No retry was
started after Charles's wrap-up order. The stop command found no live resource
runner in its sandbox process view; a final privileged cleanup checks only
this exact unit and checkout.

The syntactic-rewrite repair is preserved in unverified-repair.v.txt. It
changes only proof tactics: modular load rewrites require a syntactic match
and memory equality reflexivity requires syntactic identity. The diagnostic run of this candidate also exhausted memory; it does not
resolve the OOM, and no completed main theorem was checked. Active source
retains the ten original helper proofs and all six execution/return statements
as Abort. It is the same logical source as the checkpoint, apart from WIP
comments. All public statements/definitions and original evidence are intact.
No Admitted, admit, new Axiom or Parameter was added. There is no successful
full proof target and no raw transitive assumptions output for the main
theorems. Existing inherited FE is neither ruled out nor newly certified. Source and
assumptions audits were not rerun after the immediate wrap-up order.

Next step: a future authorized continuation should inspect both symbolic
branch obligations, test the archived syntactic-rewrite candidate under the
required gate, complete all six execution/return facts, build the full .vo,
and query all sixteen retained facts. The original ten helpers have no
separate full-module assumptions certificate from this unit.
