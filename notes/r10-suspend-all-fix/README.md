# r10-suspend-all-fix

Initial theorem/proof author: OpenAI gpt-6-astra, xhigh/default.
Repair author: OpenAI gpt-6.1-sol, xhigh/default. Validation status is recorded
below after full target checking and transitive assumptions queries.

Assigned branch: `llm-proofs/r10-suspend-all-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-d99c9594`.
Pinned origin/merge base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Exact permitted source checkpoint: `523f68f8d4401758f20cf9b3c3a2358917eef443`.

## History and preserved evidence

Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is the pinned origin. The explicit override permits exactly
origin..523f68f (reviewed e00/e03/e04/e05/r06 and original r10 history), plus
this unit's scoped repair commits. The checkpoint was imported by ff-only.
The successful read-only fork collision check returned no branch. Only the
prepared branch was renamed. Initial sandbox errors and authorized retries
are retained in logs 03/03b and 04/04b; no other branch was changed.
The initial tree was clean before creating these notes (the first recorded
status lists only this unit's untracked evidence directory).

`notes/r10-suspend-all/` is preserved byte-for-byte, including the initial
attempt SHA256 `50f84eb3cf4b90cf8ac40dac817e929faed92c5a6981a0470a606b1b524ee87b`,
failed author build, statements audit and provenance records. The original
author branch is unchanged. `vTaskSuspendAll_armv6m.v` is unchanged. No shared
plan/status/config, other unit, toolchain, host dependency or remote was
modified. No installs, pushes, PRs, comments or subdelegation occurred.

## Retained specification

All 16 original declarations and eight definitions must match the archived
attempt exactly; `audit-statements.py` enforces this. The theorem concerns
the finite generated ARMv6-M Cortex-M0 program at entry 0x574 and the first
exit cut 0x57c, immediately before BX LR. It writes exactly
`(1 + initial_word) mod 2^32` to the four-byte little-endian counter at
0x20000008, including wraparound. The four stored byte values and every
original-memory byte outside [0x20000008,0x2000000c) are specified.

The register frame preserves all variables except V_MEM32, R2, R3 and NZCV;
it includes R0/R1/R4-R12/SP/LR, permission maps and temporaries. The explicit
callee-saved corollary names R4-R11/SP/LR. This void function has no ABI
result-register obligation. The caller result includes the actual BX step
to initial LR with bit zero cleared and retains the complete post-store
state.

The main invariant theorem assumes a typed initial ARMv6-M store and entry
trace. Endpoint corollaries require actual execution to the first exit cut;
its semantics enforces read/write permissions. Witnesses supply readable
and writable arbitrary memory `m < 2^(8*2^32)` and arbitrary odd ordinary LR
`lr < 0xfffffff0`. No counter, nonzero, size, overlap, CPU-feature or tunable
hypothesis is added. Artifact/config scope is pinned FreeRTOS V11.1.0,
configNUMBER_OF_CORES=1 and the unchanged inherited Cortex-M0 lift. There
are no unproved callee/kernel contracts.

This is sequential lifted-IL partial correctness and ordinary return. No
termination, scheduler exclusion, IRQ/hardware/atomicity, whole-kernel or
binary/lifter refinement is claimed. The folded literal pool remains part
of inherited immutable-code provenance. Source/ELF/layout checks are in
08-provenance.log, not a proof of lifting soundness.

## Repair record

Restored the exact archived proof bodies. The first repair accidentally
attempted to change the word-store bound to strict less-than, while the
library requires less-than-or-equal; log 06 records the real failed build
and `Not convertible` error. Corrected the side conditions of
`getmem_setmem` and `setmem_byte` to explicitly prove `4 <= 4294967296`
with arithmetic after clearing unrelated context. Statements and definitions
remain unchanged. Further repair/check results follow below.

## Validation protocol

Every build and query uses the mandatory shared gate:

```sh
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py --unit r10-suspend-all-fix --memory-kib 1750000 -- /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c '<command>'
```

The gate enforces 1,750,000 KiB address space and 65,536 KiB stack. Dune uses
`--cache=disabled -j1`, full `mode vo`. No concurrent compilers inside this
unit, cap increases, shared gate modifications or signals to other jobs.
All exact commands, stdout/stderr and true exits are retained using
`tools/record-command.sh` in this directory.

The next build (07) passed the main invariant proof and stalled at
`apply suspend_all_memory_word` in the original-memory corollary. Its own
compiler PID 751056 was verified by cwd and command, then interrupted with
SIGINT; log 07 records `User interrupt`, exit 1. No other job was signaled.
The three applications in that corollary now use `exact` with the original
memory argument explicitly supplied, avoiding expensive memory unification.
No other proof-body changes were necessary. Log 10 is named `build-timed`
because instrumentation was prepared while admission was queued; it was
removed before the compiler started once log 07 had identified the site.
The actual successful source has no timing instrumentation. The command
uses `--no-buffer` to stream compiler output. No Dune file change was needed:
the checkpoint already lists exactly this proof plus its inherited modules.

Log 10 records the successful full target command (exit 0):

```sh
dune build --cache=disabled -j1 --display short --no-buffer Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.vo
```

The proof header now credits Astra for the original statements/proofs and Sol
for the kernel-checked repairs; original notes are still unchanged. The
assumptions helper rebuilds this final header-only update before querying.

## Final result: DONE for the retained sequential IL specification

Log 14 records the final-source full target rebuild plus all 16 verbatim
`Check`/`Print Assumptions` queries, exit 0, through the mandatory gate. Its
inner command is `bash notes/r10-suspend-all/print-all-assumptions.sh`, which
calls `tools/print-assumptions.sh` with all original theorem names, explicitly
sets PROOF_MEMORY_KB=1750000 / PROOF_STACK_KB=65536, and builds the exact .vo
with `--cache=disabled -j1` before compiling its temporary assumptions file.
There is no skipped proof checking. The final .vo is 135278 bytes; the
compiled and working proof source SHA256 is
`d7cb7b1a4b1e69902f59d98df8d4001982bce5ef9165ab8ff7d3def130fe4a11`.

All 16 retained statements now exist as kernel-checked constants. Ten have
verbatim output `Closed under the global context`:

- suspend_all_nwc
- suspend_all_welltyped
- suspend_all_zero_bound
- suspend_all_witness_models
- suspend_all_entry_satisfiable
- suspend_all_entry_nonempty
- suspend_all_memory_word
- suspend_all_memory_byte
- suspend_all_outside_distance
- suspend_all_memory_frame

The six remaining constants are:

- suspend_all_correct
- suspend_all_post_at_bx
- suspend_all_original_memory_effects
- suspend_all_preserves_callee_saved
- suspend_all_return_step
- suspend_all_caller_result

For EACH of these six, the entire raw transitive assumptions block is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib assumption documented by e00, not an imported
admission or a newly declared axiom. Log 14 contains every full query/type
and raw block; audit-results.py inspects all 16 blocks, not merely lexical
source. Log 16 initially failed an overly strict artifact assertion because
Rocq emits zero-byte .vos/.vok markers even when compiling full .vo. The
corrected artifact audit in 16b passes: mode vo, actual nonempty .vo, identical
source/built source, and only empty markers. This did not require any proof
or build configuration change, skipped-proof target or extra compilation.

Logs 11 and 12 record whole-repository and unit source audits against
49956416928e5b6bb3928b54ae33e3b81091f006, both exit 0. Baseline totals remain
seven Admitted, one admit and 89 module-interface Parameters in unrelated
baseline sources; NEW totals are empty. The unit has no admissions,
Abort, Axiom or Parameter, and all 16 proofs end in Qed. No imported admitted
proof appears in the transitive queries. Log 15 verifies exact retained
statements/definitions and unchanged original notes/generated lift, exit 0.

Final proof producer: Sol; initial statement/proof author: Astra. The retained
specification above is complete; no functional/witness/frame/return proof
obligation remains. Termination, scheduler/IRQ/hardware/whole-kernel and
binary/lifter refinement remain outside the statements, not proved results.

The local commit and final clean ancestry/status seal are recorded externally
under `/home/charles/code/friends/.refs/picinae-llm-proofs/units/r10-suspend-all-fix/`
so recording the final commit hash and clean status does not dirty this tree.
Only origin..the exact assigned checkpoint and this scoped linear local
repair commit are permitted. The assigned branch is unpublished.
