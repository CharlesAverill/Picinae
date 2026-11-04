# r13 reset-event Sol continuation

Initial author: OpenAI gpt-6-astra, xhigh/default (`r13-reset-event`).
Fixer: OpenAI gpt-6.1-sol, xhigh/default (`r13-reset-event-fix`).
State: **PARTIAL**, stopped on Charles's explicit wrap-up order.
Final proof producer: none; full unit validation is incomplete.
Branch: `llm-proofs/r13-reset-event-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-5a06644e`.

## Preservation and scope

The prepared e00 HEAD was verified, then this branch fast-forwarded to the
exact authorized author source checkpoint
`003d8a6d10510ce11b7c45beea2e62174b2ded2b`. Its eleven prerequisite commits
above pinned origin are the entire allowed pre-unit history. The original
Astra branch, archive, generated map, definitions and fifteen statements are
preserved. `preparation.txt`, initial/checkpoint ancestry logs and
`audit-ancestry.py` record this. No host installation, remote write,
publication, subdelegation or other-branch change occurred.

The contract is the original sequential IL partial-correctness contract:
entry 0x1524, pre-BX cut 0x1536, current-TCB global 0x20000108, event field
TCB+24, priority field TCB+44, 32-bit little-endian accesses, return the
original event word in R0 and store `(5-priority) mod 2^32`. The four event
bytes may change, all other memory bytes are framed modulo 2^32; R4-R12,
SP, LR, permission maps and temporary variables are preserved. Aliases and
wraparound are permitted without alignment, non-overlap or priority-range
restrictions. The normal-priority corollary separately assumes priority<5.
The invariant theorem assumes a modeled entry and an entry trace; executable
trace corollaries also assume exec_prog and no prior exit. Permissions are
supplied by executable memory-access derivations. Arbitrary bounded memories
and odd LR<0xfffffff0 have a typed/readable/writable witness. The explicit
return theorem uses actual ordinary BX IL, odd LR and LR<0xfffffff0, clearing
the low bit and preserving the complete post-store state.

No termination, hardware/exception/IRQ behavior, scheduler property,
whole-kernel correctness, or binary/lifter refinement is established. Literal
folding and inherited unvalidated lifting provenance remain trusted. There
is no callee contract. Provenance check output is in `provenance.log`.

## Iterations

Every compiler/query uses the mandated shared resource-run.py gate with unit
r13-reset-event-fix, memory=2500000 KiB and stack=65536 KiB. All Dune commands
use --cache=disabled -j1 and build the full .vo target.

1. `build-01.log`, source `attempt-01.v.txt`: restore the archived proofs and
   add diagnostic BEGIN markers. The build was admitted after RAM/paging
   waits, compiled its dependencies, then failed with OOM/exit 1 inside
   reset_event_entry_satisfiable. Thus the larger cap alone does not fix it.
2. `attempt-02.v.txt`: replace the witness's `repeat split` with exactly three
   conjunction splits. Repeated split can try equality reflexivity and
   evaluate the N.ones(2^32) permission bitmap. Explicit splits keep the
   subsequent ones_spec_low/modulo bound proof symbolic. No declaration,
   definition or hypothesis changes.

The original initial evidence remains under `notes/r13-reset-event/` without
modification. Source audits do not replace transitive assumptions queries.

## Wrap-up on explicit user order

Charles ordered no further work/retries, immediate stop of proving/compiling/
waiting, and a local WIP commit. Only this worktree's active rocqworker
(PID 778663, cwd verified) received SIGTERM. No other process was signaled.
The gate releases the reservation when Dune exits; no further compiler or
query was started. `build-02.log` retains the actual termination exit status.

The second run passed the first five Qed commands, including the symbolic
permission witness, then reached both invariant cuts in reset_event_correct.
Buffered compiler output ended with `Goal at < 5430 >`; the precise remaining
tactic/kernel conversion has not been isolated. Observed own compiler RSS
was 864340 KiB, VmSize 1092368 KiB. This was a stop order, not a second OOM.
No full unit .vo exists, no Print Assumptions was run, and no new theorem is
claimed certified as a full module result. Inherited FE is known from the
baseline but this unit's transitive assumptions remain unverified.

The live source retains the five prefix helper proofs and preserves all
remaining ten declarations as Abort, including the main theorem. All attempted
proof bodies are retained in attempt-02.v.txt. No admissions, new axioms or
parameters were introduced. The WIP packaging itself was not rebuilt or
re-audited after the stop order. Initial whole-tree source and ancestry audits
passed; they are not final kernel certificates.

Next step, only if reauthorized: isolate the final proof/checking cost in
reset_event_correct with syntactic bounds/explicit proof arguments, complete
all ten aborted proofs, then obtain a successful full target, all fifteen
transitive Print Assumptions results, final source/declaration/ancestry audits.
All original definitions/statements, generated IL and author evidence remain
unchanged. No completed main theorem or binary-correctness claim is made.
