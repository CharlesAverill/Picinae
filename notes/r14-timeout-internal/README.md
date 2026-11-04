# r14-timeout-internal

Initial author: **gpt-6-astra**, xhigh, one-shot. Final proof producer: **none; PARTIAL**.
Branch: `llm-proofs/r14-timeout-internal`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-8df74c71`.

Prepared HEAD was clean at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The required read-only fork collision check succeeded with no result after
sandbox DNS initially failed. Only the prepared branch was renamed.
Fast-forwarded to exact assigned prerequisite
`5fec2fc24d0c739bafc08add426f02a3085e15cd`; no other histories imported.
The initial unprivileged merge/rename attempts were denied by the filesystem
sandbox, before changes; the authorized retry succeeded. Git metadata lives
outside the writable worktree. The accepted prerequisite includes the r06
Astra/Sol getter proof history, disclosed in the ancestry logs.

Base/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
The generated lift is unchanged. Only the proof, its explicit Dune module/
alias, and unit evidence are new. The proof imports the core ARMv6-M model
and this function's generated lift, not the r06 proof or any callee contract.
The root list's other inherited modules are not requested by the new target.

`provenance.log` verifies the pinned source/config/layout/lift SHA256 values,
quotes exact C statements/layout, and records global addresses and instructions.
No toolchain installation, shared environment changes, remote writes, or
publication occurred.

## Statements

- `timeout_correct` and `timeout_post_at_bx`: sequential partial correctness
  of the finite generated map, entry 0x908 to first BX cut 0x914. Exact
  ordered memory effect, arbitrary aliases and modeled 32-bit initial store;
  all variables except memory and R3 preserved.
- `timeout_original_memory`: first store must not overlap the four-byte tick
  global. Under that precise separation both stores use original values.
  Aliasing the overflow global or the second store with globals is allowed.
- `timeout_original_fields`, `timeout_original_bytes`: add nonwrapping
  pointer+8 <= 2^32; original little-endian field words and each byte.
- `timeout_memory_frame`: all bytes disjoint from the modular eight-byte
  target agree with original memory.
- `timeout_preserves_callee_saved`: R4-R11, SP and LR frame.
- `timeout_return_step`: actual guarded BX execution for odd LR below
  0xfffffff0; clears bit zero, preserves store, excludes EXC_RETURN range.
- `timeout_caller_result`: combines execution, exact memory/register frame,
  fields, bytes, outside frame and caller return step.
- `timeout_entry_satisfiable`: arbitrary bounded memory and pointer have a
  typed, fully readable/writable witness with LR=1; plus a concrete separated
  pointer at 0x20000100 in `timeout_separation_nonvacuous`.
- `timeout_nwc` and `timeout_welltyped`: immutable-code and typing facts.

No nonzero/alignment restriction in the IL theorem (C alignment 4 recorded);
no count/value/CPU/tunable restriction. Trace execution provides actual memory
permission premises. No IRQ, concurrent snapshot, hardware/lifter refinement,
whole-kernel, termination or scheduler-cardinality result.

## Validation

`initial-attempt.v.txt` preserves the exact one-shot source;
`initial-source-sha256.log` pins it. `initial-build.log` records the full
`.vo` target, stdout/stderr, admission, cap 2000000 KiB, stack 65536,
-j1, cache disabled and true exit code. No second Astra repair cycle permitted.
`source-audit.log` is the full base-relative source audit (exit 0, no new
admissions or axioms/parameters). This lexical check is not a transitive trust
certificate. The baseline core has inherited
`Stdlib.FunctionalExtensionality.functional_extensionality_dep`; only actual
Print Assumptions output can determine whether these new theorems use it.
`run-assumptions.sh` specifies all 16 theorem/helper queries for the required
post-success gated assumptions audit.

## PARTIAL handoff — first attempt did not finish

The single full target command returned **exit 1** after I deliberately sent
SIGINT to this unit's verified compiler PID 719383 (cwd checked), at 9m54s
wall time / 10m12s CPU for the proof file. This was an author-imposed stop
of a slow attempt, **not** a compiler-detected proof error, memory-cap failure,
or automatic timeout. No other process was signalled and no cap was raised.
The shared admission helper released the reservation normally. No compiler
was started again, including for Print Assumptions.

Exact diagnostic:

```
Goal at < 2312 >
Goal at < 2324 >
File "./Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.v", line 194, characters 59-71:
Error: User interrupt.
```

The location is the final `reflexivity` in `timeout_correct`'s memory-equality
branch, after `repeat armv6m_step` and the modular-memory rewrites. The
conversion did not finish. No diagnosis beyond that is established. Sol
should inspect that equality with bounded diagnostics and retain the
statements unless a genuine specification error is demonstrated.

`initial-compiler-aux.txt` records 11 completed helper Qed checks, through
`timeout_memory_frame`; it is **not a full .vo or assumptions certificate**.
Those 11 helper proofs are retained unchanged. The five declarations from
`timeout_correct` onward preserve their statements, but their initial proof
scripts are now comments followed by Abort. This is failed-attempt packaging,
not a second proof attempt. The exact original source is unchanged in
`initial-attempt.v.txt`. Neither the initial target nor the packaged partial
file has a successful full target build. No main theorem is certified, and
no Print Assumptions output is available. Baseline functional extensionality
remains disclosed; transitive assumptions for the retained helpers still
need querying. A new **gpt-6.1-sol xhigh/default** fixer is required; the Astra
author has not started one.

Proposed spec coverage listed above is the preserved target specification,
not achieved execution/return correctness. Source/provenance audits passed;
functional correctness, caller theorem, full target and all 16 assumptions
queries remain outstanding.
