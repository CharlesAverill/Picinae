# r42-port-mask-fix — DONE for the stated sequential IL scope

Initial author: OpenAI gpt-6-astra, xhigh/priority (`r42-port-mask`).
Final proof producer: OpenAI gpt-6.1-sol, xhigh/priority (`r42-port-mask-fix`).
Branch: `llm-proofs/r42-port-mask-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-5f10d9a4`.

Restored the entire 430-line archived initial attempt before iterative repair.
All 50 original definitions/predicates/statements are retained verbatim modulo
comments and whitespace; all 31 original theorem/lemma declarations now end in
Qed. No added helper declarations, changed preconditions, Abort, Admitted,
admit, Axiom, or Parameter in the proof. See `declaration-preservation.log` and
`check-declarations.py`. The original archive and original author's notes are
unchanged (SHA256 `09737e2e7a0bab906ffe702b70fbc551538de98605d062d2973bb3d00edc0bd0`).

## Established specification

`ulSetInterruptMask_correct` establishes universal correctness of three actual
finite-map instruction steps: MRS at 0x4090, CPSID at 0x4094, BX LR at 0x4096.
R0 returns the old one-bit PRIMASK, PRIMASK becomes 1, and the final store equals
`mask_set_result s`. `vClearInterruptMask_correct` establishes universal
correctness of two actual steps: MSR at 0x4098 and BX LR at 0x409c. PRIMASK becomes
input R0 mod 2, R0 is preserved, and the final store equals `mask_clear_result s`.
Both return to `Addr (N.land (s R_LR) 0xfffffffe)`.

`mask_set_execution` and `mask_clear_execution` construct all three/two actual
`can_step` transitions, including the dynamically guarded BX, and prove the
postconditions. `ulSetInterruptMask_satisfies_all` and
`vClearInterruptMask_satisfies_all` provide the Floyd–Hoare interfaces to the
BX-instruction cut; these interfaces alone stop before BX, while the execution
witnesses and universal completed-step theorems include it.

Exact hypotheses: full `models armv6mtypctx s`, CONTROL.nPRIV=0, odd LR,
LR < 0xfffffff0. ABI registers/pointers are 32-bit ARMv6-M. Typed PRIMASK and
Handler values are 0/1; either Thread or Handler mode is supported. Arbitrary
typed memory, argument R0, SP, access maps, and other variables are allowed.
There are no memory permissions, buffer-size, overlap, CPU feature, or tunable
hypotheses. No memory is accessed. `mask_input_store_typed` constructs typed
stores for all m < 2^(8*2^32), R0 < 2^32 and SP < 2^32; `mask_entry_witness` and
`mask_both_bits_inhabited` establish entry inhabitance for both mask bits and
either mode while preserving memory/R0/SP.

Set frames every variable except R0 and PRIMASK. Clear frames every variable
except PRIMASK. Thus memory, SP/LR, R1–R12, NZCV, access maps, temporaries,
Handler state and CONTROL.nPRIV are preserved by the proved executions.
`mask_set_code_stable` / `mask_clear_code_stable` require equality of
CONTROL.nPRIV and LR between stores. There is no unconditional nwc claim:
state-dependent profile and normal-return guards remain active.

Inherited provenance: FreeRTOS V11.1.0 source
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`, e04 ELF SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`,
e19 strict primask-v1-base finite maps. Generated maps, frontend, ISA and root
Dune selection are unchanged. This proves properties of those sequential IL
maps, with inherited unvalidated binary/lifter refinement. No asynchronous IRQ
exclusion/delivery, barriers, scheduler, exception return, caller-continuation
termination, hardware, or complete binary/lifter refinement theorem is claimed.
Normal odd LR may target code in the map; no extra exclusion was added. No e20
projection or unproved kernel/callee contract is imported.

## Repair and validation evidence

Every build/assumptions compiler runs in the existing read-only environment:
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`, with
`ulimit -v 2000000`, `ulimit -s 65536`, `--cache=disabled -j1`. No simultaneous
proof compilers within this unit, cap increases, dependencies installed, host
changes, or changes to shared environments.

`build-01.log` through `build-17-time.log` retain failed repair iterations,
compiler stdout/stderr, exact commands and true exit codes. Builds 01/02 hit
the cap in the typed-store witness because lia saw an unrelated enormous
memory bound; clearing irrelevant context fixed it. Build 16 hit the cap when
`destruct_inv` unfolded the state-dependent decoder at many address prefixes.
The repaired proof first extracts the actual program's precondition and then
uses a constant lookup solely to enumerate invariant addresses; all subsequent
NIStep lookups and semantics still use the actual generated program. Remaining
errors were tactic bullet allocation, update/reset aliases and frames, overly
broad bit rewrites, and missing explicit constructor arguments. No statement
was false or changed. A temporary Dune `-time` flag was removed after diagnosis;
there is no final Dune diff.

`build-18-time.log` is the first successful full target build, exit 0.
`build-clean.log` is the successful final clean full `.vo` build, exit 0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short Examples/FreeRTOSMask/armv6m_port_mask_proof.vo'
```

The root theory retains `(mode vo)` and explicit module selection. No `.vos`
proof-skipping invocation was used (Rocq may create empty companion markers).

`assumptions.log` contains verbatim Check/Print Assumptions output from
`tools/print-assumptions.sh`, for every one of the 31 main/helper/frame/witness
facts, exit 0. `check-assumptions.sh` records the exact queried names and caps.
`assumptions-inspection.log` verifies each output: 21 facts closed, 10 depend
only on the inherited Stdlib functional extensionality axiom. Those ten are
`mask_reset_same`, `mask_reset_update`, `mask_move_step`, `mask_return_step`,
`mask_set_execution`, `mask_clear_execution`, `ulSetInterruptMask_correct`,
`vClearInterruptMask_correct`, `ulSetInterruptMask_satisfies_all`, and
`vClearInterruptMask_satisfies_all`. Their raw output is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

No other transitive assumption or imported admission occurs. The inherited
axiom and baseline usage are documented in `notes/e00-build/README.md`.

`source-audit.log`: `python3 tools/audit-proof-source.py --base
49956416928e5b6bb3928b54ae33e3b81091f006`, exit 0, NEW totals {}.
Baseline unrelated admissions remain inventoried, but are absent from this
unit's transitive assumptions. `protected-sources.log` establishes no tracked
change outside this proof relative to the exact author checkpoint before notes
were staged, including unchanged root Dune, generated maps and original notes.

## Local ancestry and publication

Prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose
sole parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
Initial status was clean before evidence creation. `fork-name-check.log` records
a successful empty read-only fork-name query before renaming only the newly
prepared branch. An initial sandbox DNS query and sandbox branch rename/merge
attempts failed; required read-only network and local Git metadata operations
then succeeded through sandbox escalation. No automatic approval rejection.

Only exact checkpoint `528ce6ea33010569580804878da662aec03a47e6` was imported via
`git merge --ff-only`. Its exact reviewed e00/e03/e04/e05/e19 and original r42
ancestry is preserved. The merge base remains pinned origin. Only scoped linear
Sol fixer commits follow that checkpoint. `audit-ancestry.sh` checks this,
records full log/diff-stat/status, and rejects out-of-scope fixer paths.
`ancestry-prepared.log`, `ancestry-imported.log`, and subsequent ancestry logs
retain before/after evidence. A final clean status is also checked after the
evidence commit.

No fork branch was used as a base, no new worktree or other branch was changed,
no original author's branch/worktree/notes or shared campaign was edited, and
no pushes, PRs, comments or remote writes occurred. Publication remains with
Charles. No remaining proof gap within these unchanged statements; limitations
are the IL/provenance and sequential-scope boundaries above.
