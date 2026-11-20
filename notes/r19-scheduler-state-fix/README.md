# r19-scheduler-state-fix

Status: PARTIAL / WIP, stopped on Charles's explicit wrap-up order.
No successful full unit target or assumptions query; no completion claim.
Initial author: OpenAI gpt-6-astra, xhigh/default, r19-scheduler-state.
Assigned repair producer: OpenAI gpt-6.1-sol, xhigh/default.
Branch: llm-proofs/r19-scheduler-state-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-c04b62c5.

The prepared worktree was clean at e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9,
whose sole parent is origin 49956416928e5b6bb3928b54ae33e3b81091f006.
The initial prepared branch was t3/c04b62c5; by the recorded preparation
step its harness name was t3/scheduler-state-fix, with identical HEAD.
The successful empty fork check preceded the only local branch rename.
The exact authorized checkpoint 47a4a26a7e155fdfa1d045fddb288f68bf343a6b
was imported with merge --ff-only. Its eleven pre-unit commits above origin
are allowed verbatim; no unrelated history was imported. The original
llm-proofs/r19-scheduler-state ref remains at that checkpoint.
Initial network and read-only Git metadata failures are retained, as is the
successful read-only collision check and authorized escalated import/rename.
No push, PR, remote write, install, shared-environment change or delegation.

The entire archived Astra attempt was restored, correcting sizeof(void*)
to sizeof(pointer) in the header so it cannot close a Rocq comment. The
original archive and all original evidence remain byte-for-byte unchanged.
The original audit verifies all 13 theorem statements and seven definitions
are retained verbatim. The generated map is unchanged (SHA256
079c2ba35ac01da4db0ec699cdda334fc68bf870f396a448e2410b38cd4c04c8).
The inherited explicit root Dune list already includes the required target;
no extra module selection is necessary.

Every compiler/query runs through resources/resource-run.py with unit
r19-scheduler-state-fix, 1750000 KiB memory, stack 65536 KiB, using only the
read-only isolated arm-validation/picinae-env. Dune uses -j1, --cache=disabled,
full .vo mode. There are no concurrent proof compilers within this unit.
check.sh saves the exact attempt and uses tools/record-command.sh to retain
the actual command, stdout/stderr and true exit code. Original logs and
failed attempts are evidence, never certificates of completion.

## Specification and limitations

The unchanged finite xTaskGetSchedulerState_armv6m_prog is used directly.
There are no register arguments. From initial modeled ARMv6-M store s at
0x12fc, the functional postcondition at the first designated BX LR 0x1310
reads the original four-byte little-endian word at 0x20000024
(xSchedulerRunning). If it is zero R0=1; otherwise the original word at
0x20000008 (uxSchedulerSuspended) determines R0=2 when zero and R0=0 otherwise.
All 32-bit word values are covered; no Boolean-only or reachable-kernel-state
premise. The frame preserves every variable other than R0/R3/N/Z/C/V,
including every memory byte, permissions, R1/R2/R4-R12, SP, LR and temporaries.

The invariant theorem is partial correctness. Post-at-BX results also assume
an actual exec_prog trace and no earlier designated exit. Such actual loads
supply read permissions. The witness exhibits a typed store for every bounded
memory m<2^(8*2^32) and every odd LR below 0xfffffff0, with read permission on
both four-byte globals. The ordinary BX step requires the odd LR and upper
bound, excludes exception-return encodings, clears bit zero and preserves the
whole store. No calls or callee contracts are assumed. No input pointer,
size, overlap, CPU feature, tunable or additional path restriction is imposed.

Provenance is inherited: FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
The folded literal pools are trusted immutable code. There is no proved
binary-to-IL refinement, scheduler atomicity, IRQ interference, hardware
exception-return behavior, whole-kernel invariant or termination claim.

## Wrap-up evidence and remaining work

Charles ordered immediate wrap-up, no further proof/compiler/query retries.
The first seven original facts were kernel checked in the capped timed
diagnostic through scheduler_state_entry_satisfiable (13-timed-readable-fix.log).
These are nwc, welltyped, preserves_memory, adc_result, zero_bound,
witness_models and entry_satisfiable. This is not a successful full Dune
unit target and no raw Print Assumptions certificate exists for this unit.

Repairs: restore the archived attempt and sanitize the header; replace the
unrestricted cbv LR-bound proof (out of memory at 1750000 KiB) with explicit
change and N.lt_trans; replace the unavailable lia readable-address proof
with direct transitivity. All statements and seven definitions are retained.
The original memory/typing/arithmetic/witness helpers remain Qed.
The main theorem and all dependent corollaries/return proof are explicitly
Abort in the active file. No new admission, axiom or parameter is introduced.
The unchecked complete repair attempt is preserved as
wrap-up-unfinished-attempt.v.txt and the individual timed snapshots.

The next obstruction was the first broad reflexivity on the loaded-memory
expression after symbolic execution and frame proof in scheduler_state_correct.
That diagnostic was explicitly terminated (own PID 785296 only), exit 143.
A revised attempt abstracts the loaded word before arithmetic simplification;
its last run was started before the wrap-up order. Its outcome is not inferred.
No further compilation or assumptions query was run after that order.
Automatic approval review rejected the process/log inspection intended to
identify and stop that last run, interpreting it as a forbidden new query.
Cancellation is left to the coordinator as requested.

Next: resume from the saved abstract-result attempt, finish functional
correctness, original-memory/callee frame, and guarded ordinary BX/caller
result. Then run the full Dune .vo target successfully and all thirteen
transitive Print Assumptions queries through the mandatory gate; inspect
them for imported admissions, recording inherited FE honestly if present.
The initial full source audit passed with unchanged baseline totals
(seven Admitted, one admit, 89 interface Parameter tokens); those are not
a transitive certificate. The pre-unit ancestry audit passed with exactly
eleven allowed prerequisite commits and unchanged generated map/author notes.
No final validation or clean-status audit is claimed after the stop order.
