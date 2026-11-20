# r14-timeout-internal-fix

Initial author: OpenAI gpt-6-astra, xhigh, one-shot.
Repair/final proof producer: OpenAI gpt-6.1-sol, xhigh. The full target passed
(`build-02.log`, exit 0); transitive assumptions queries are recorded separately.

Assigned branch: `llm-proofs/r14-timeout-internal-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-508b2fbc`.
Prepared HEAD: e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent
`49956416928e5b6bb3928b54ae33e3b81091f006` (pinned origin).
The first tool inspection showed clean status. The recorded initial ancestry
check follows creation of this evidence directory and therefore shows only
this new untracked directory. The sandbox's DNS failure on the first remote
read was retried with network permission; the recorded collision check
succeeded with no remote head. Only the prepared branch was renamed.
Fast-forwarded only to assigned unproved checkpoint
`97fd8ecfb6adac59f137ca465a0bfb4beb3862ac`; all history through that checkpoint
is explicitly authorized, including its reviewed e03/e04/e05/r06 prerequisites.
No fork branch was used as a base. No remote writes or other branch changes.

Original author evidence remains unchanged under `notes/r14-timeout-internal/`.
The 9m54s author build was manually interrupted at memory-equality conversion;
it was not an OOM, automatic timeout, or compiler-reported proof error.
The eleven original helper proofs and every original statement/definition are
retained. The five archived execution/return proofs were restored before repair.
The generated finite map and root Dune selection are unchanged.

Every compiler/query uses the shared `resource-run.py` gate with this unit ID,
2000000 KiB address-space limit, stack 65536 KiB, the read-only isolated
`picinae-env` wrapper, and Dune `--cache=disabled -j1` full `.vo` mode.
No dependencies installed. No compiler runs concurrently inside this unit.
Build logs preserve stdout/stderr and true exits with `tools/record-command.sh`.
Attempt snapshots are diagnostic sources, not theorem certificates.

Scope is sequential partial correctness of the unchanged ARMv6-M IL from
0x908 to the first BX cut at 0x914, plus a separate actual ordinary BX step.
The ordered stores permit modular aliases. Original tick results retain the
explicit first-store/tick-global separation; field/byte corollaries retain
the eight-byte nonwrapping extent. Register frames, memory frame, arbitrary
bounded-memory typed writable witnesses, and odd LR < 0xfffffff0 are retained.
No IRQ, concurrency, hardware/lifter refinement, whole-kernel or termination claim.

## Repair and validation

`build-01.log` is an intentional diagnostic failure (exit 1), not a failed
specification or a resource failure. It builds dependencies and prints the
post-execution memory equality before conversion. Both sides have exactly the
same two stores, memory and loaded values; only the outer address differs:
`4 + s R_R0` versus `s R_R0 + 4`. The original blanket rewrites followed by
`reflexivity` attempted conversion of these unequal address expressions,
which can unfold the integer representation of the whole memory.

The repair applies `f_equal` to the explicitly matched outer `setmem` function
and `N.add_comm 4 (s R_R0)`. This constructs the memory equality without
computing memory contents. No new helper contract, assumption, precondition,
statement or definition was introduced. The other four original archived
proofs succeeded unchanged after restoration. The header now attributes final
checked proof production to Sol and points to this continuation's evidence;
the original Astra provenance remains intact.

`build-02.log` records a real full `.vo` target success (exit 0):

```
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py --unit r14-timeout-internal-fix --memory-kib 2000000 -- /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.vo'
```

`assumptions.log` runs the original sixteen queries, through the same gate:

```
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py --unit r14-timeout-internal-fix --memory-kib 2000000 -- /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'bash notes/r14-timeout-internal/run-assumptions.sh'
```

That script exports `PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536` before
`tools/print-assumptions.sh`, builds the full target again if needed, and
compiles actual `Check` / `Print Assumptions` queries against `_build/default`.
The final attribution header was changed only after the first successful
check; the assumptions command also checks the exact final source.

All gate waiting messages are retained. They are scheduling delays from the
shared admission policy, not proof compiler failures. No compiler was
interrupted. Original author branch remains at the exact checkpoint.

## Theorem coverage

- `timeout_correct`, `timeout_post_at_bx`: from typed entry at 0x908 to the
  first 0x914 cut, exact ordered overflow/tick stores and all-variable frame
  except MEM32/R3. Pointer is the AAPCS32 R0 value. Modular aliases allowed.
- `timeout_original_memory`: first store disjoint from the four-byte tick
  global (`~ overlap 32 0x2000002c 4 p 4`) recovers both original loaded values.
- `timeout_original_fields`, `timeout_original_bytes`: additionally `p+8 <=
  2^32`, recover the original two 32-bit fields and each of their four bytes.
- `timeout_memory_frame`: bytes disjoint from the modular eight-byte target
  retain their original values, without the tick-separation precondition.
- `timeout_preserves_callee_saved`: R4-R11, SP and LR unchanged along execution.
- `timeout_return_step`: actual BX at 0x914 with odd LR < 0xfffffff0, clears
  bit zero, preserves the store; high EXC_RETURN tokens are outside the claim.
- `timeout_caller_result`: combines the execution/frame, original fields,
  bytes and memory frame, and ordinary return step under the retained extent,
  separation and LR hypotheses.
- `timeout_witness_models`, `timeout_entry_satisfiable`: any memory below
  `2^(8*2^32)` and pointer below `2^32` has a typed fully readable/writable
  witness with ordinary LR=1. `timeout_separation_nonvacuous` provides a
  concrete separated pointer 0x20000100 (also satisfying the eight-byte extent).
- `timeout_nwc`, `timeout_welltyped`, `timeout_zero_bound`,
  `timeout_ranges_separate`: immutable map, typing and arithmetic helpers.

There is no new callee contract. Executable traces supply actual permissions;
no nonzero pointer, alignment, count, CPU-feature or tunable restriction is
added to the IL theorem. The original immutable-code literal folding and
unvalidated binary-to-IL/hardware provenance boundary remains inherited.

## Final result: DONE

Full target and all sixteen transitive assumption queries succeeded with exit
0, including a rebuild of the final attributed source. `certificate-audit.log`
checks the saved raw output, all sixteen names in order, exact assumption
sets, sixteen Qed terminators and no active Abort/admission/axiom/parameter.
`final-artifacts.log` records matching working/build source hashes and the
successful `.vo` hash. `final-compiler-aux.txt` preserves the final per-proof
build/check metadata; the full target and raw queries are the certificates.

Eleven facts are closed under the global context: `timeout_nwc`,
`timeout_welltyped`, `timeout_zero_bound`, `timeout_witness_models`,
`timeout_entry_satisfiable`, `timeout_ranges_separate`,
`timeout_separation_nonvacuous`, `timeout_original_memory`,
`timeout_original_fields`, `timeout_original_bytes`, `timeout_memory_frame`.

The five execution/return facts (`timeout_correct`, `timeout_post_at_bx`,
`timeout_preserves_callee_saved`, `timeout_return_step`, `timeout_caller_result`)
each print exactly this transitive assumption set:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is inherited Stdlib functional extensionality, documented at e00 in
`notes/e00-build/logs/15-extensionality-provenance.log`, used by the existing
Picinae proof machinery and the original reset-store extensionality proof.
It is not hidden or a new unit axiom. No admitted theorem or additional axiom
appears in any queried fact's transitive assumptions.

`final-source-audit.log` is the requested full base-relative lexical audit:
exit 0, NEW totals `{}`; baseline unrelated admissions remain inventoried.
`unit-source-audit.log` is the scoped audit with zero admission/axiom/parameter
tokens. `final-scope.log` verifies the exact checkpoint, unchanged original
statements/definitions/helper scripts, map, Dune and initial author evidence.
`precommit-scope.log` records the final staged state. After committing, the
final full-SHA/ancestry/diff-stat/clean-status record is saved outside this
checkout (so recording it cannot dirty the audited tree) at:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/r14-timeout-internal-fix/final-ancestry.log`.

All retained obligations are complete within the stated sequential IL scope.
Remaining boundaries are the inherited unproved lifting/hardware provenance,
IRQ/concurrent memory, whole-kernel semantics and termination, which are not
claimed. No installation, shared-environment mutation, subdelegation, push,
PR, remote comment or other remote write occurred.

The first staged whitespace check (`staged-diff-check.log`, exit 2) identified
only blank C source lines in raw provenance stdout. A notes-local
`.gitattributes` exempts raw `.log` output from whitespace checking so evidence
remains verbatim; proof-source whitespace checking passed. The final staged
check is recorded separately with its true status.
