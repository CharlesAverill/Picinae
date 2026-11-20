# x07 AVX REP overlap repair

State: PARTIAL WIP — stopped on Charles's explicit wrap-up order.

Author model: gpt-6-astra. Repair model: gpt-6.1-sol.
Final proof model: unset pending full checks. Assigned xhigh/default.
Branch: llm-proofs/x07-avx-rep-overlap-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-16637109.
Local only. No installs, subagents, publication, remote writes or shared
source/environment edits. Original author branch and archive are unchanged.

The original nine statements and seven definitions are preserved verbatim;
see audit-declarations.py and 02-declarations.log. In particular the x03
contract and generated instruction map are unchanged. 05-lift-and-parent.log
checks the generated lift, accepted x03, baseline REP and root dune files.

## Intended scope

`memmove_avx_correct_rep_overlap` establishes satisfies_all over the actual
AVX memmove IL. `memmove_avx_rep_overlap_at_ret` derives original-source copy,
destination-complement byte frame, RAX=d, unchanged RSP, and System V AMD64
RBX/RBP/R12-R15 frame at actual pre-RET cuts493,692,794.

Typed entry RDI=d,RSI=s,RDX=n,RSP=rsp,DF=0;256<n<2^63;
d<s<d+n;s+n<=2^64;entry-memory qword[0x31a3f8]<n.
Destination nonwrap follows. There is no NOV, minimum gap, lower pointer
bound, policy-bit bound, stop-threshold bound or NT-threshold premise.
Both REP alignment paths, low32-distance policy fallback and stop-threshold
fallback are included. Every real selected global read is retained, before
stores, including the second threshold read on the stop branch. No global
address disjointness or preservation premise is imposed. NT threshold
0x3215a8 is not read on the selected paths.

Inherited binary/lifter provenance is not newly validated. Sequential IL
partial correctness only: no termination, executed RET, continuation,
hardware/CPU availability, page permissions, faults, concurrent writes,
timing or binary refinement claim. Total memory is the inherited model.

`orp_entry_satisfiable` constructs a typed entry for every gap1..8191 at
n8192,d4096,all policy<2^32 and stop<2^64. `orp_critical_distances` selects
gaps1,31,32,63,127,4096,policies0/1,stop0/16384. These witness satisfiable
inputs for both alignments/fallbacks, not a terminating trace. No helper,
kernel or callee contract is assumed.

## Repair and evidence

01-dispatch-prune.log is the first Sol full-vo attempt, starting with a
fresh local _build. The repair prunes impossible dispatch branches after
the actual threshold read, before expanding their successors. Arithmetic
threshold values are folded to local names before branch reasoning, so
lia does not inspect symbolic memory. Diagnostic BEGIN markers identify
the segment if another failure occurs. All theorem statements and
invariant/spec definitions remain exact.

Source audit04 passes relative to the pinned origin: NEW totals {}.
Baseline's unrelated admitted modules are not in this target's dependency
closure; lexical checks alone are not a transitive certificate.

Build/assumptions scripts use the required shared resource gate,6000000KiB,
stack65536,Dune -j1,--cache=disabled,full vo and no concurrent compilers.
Raw logs retain exact commands, stdout/stderr and actual exit codes.
Fresh transitive Print Assumptions is still required before DONE. Expected
inherited FunctionalExtensionality.functional_extensionality_dep is to be
reported from actual output, never silently accepted from an inherited log.

First repair result: 01 exited1 with an ordinary dispatch tactic error
("Not an inductive goal with 1 constructor"), not OOM. Source inspection
then showed why the original pruning variant stopped at the dispatch entry:
ISA_symbolic_interp clears unused numeric locals, including an unused stop
threshold alias, so the post-step `fold T` could fail and backtrack the step.
This first repair is archived as first-repair.v.txt. No main theorem was
certified by it; reaching that error does not alone establish that the original
OOM was fixed. The queued 06 attempt instead introduces/clears aliases inside
each `try solve` branch-pruning check, so no alias must survive an ISA step.
It adds a diagnostic dump of all dispatch goals before the fallback proof.
The source was updated while 06 was still waiting for admission, before Dune
started. The wait is gate scheduling, not another compiler failure.


## Forced wrap-up

Charles ordered stop proving/compiling/waiting and commit immediately. The
queued 06 resource-run process was terminated, without starting a new compiler
or retry. Its prior wait reasons are preserved verbatim. No other process was
signaled. No new x07 theorem is certified: the first Sol build checked the
prerequisite closure and reached an ordinary error in the main dispatch proof;
the revised dispatch tactic never ran because admission remained pending.
The complete current source is archived in wrap-up-attempt.v.txt. All nine
original statements are retained as Abort in the proof module, so no unproved
result or admission is exported. No fresh x07 Print Assumptions output exists.
Final proof model remains unset. The source/ancestry audits already recorded
passed before this wrap-up; no new proof validation was run.

Open: check the revised per-step dispatch pruning; finish all dispatch,
destination-aligned REP and stop-fallback obligations, Qed/kernel check and
RET/witness checks, then all nine fresh assumptions queries and final audits.
Original Astra failure: OOM/ABRT at6000000KiB. First Sol attempt: exit1,
ordinary tactic error, no OOM. Second attempt: gate wait only, stopped.
No new Admitted/admit/Axiom/Parameter. No publication or installation.
