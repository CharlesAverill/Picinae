# r42-port-mask — PARTIAL Astra handoff

Initial author model: **gpt-6-astra, xhigh/priority**.
Final proof producer: **none**. This is not a completed proof unit.
Assigned branch: `llm-proofs/r42-port-mask`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-14b2d9df`.

The single permitted full relevant Dune build failed, exit **1**, at the initial
`mask_set_result_post` proof, line 77. The error applies `update_updated` to a
remaining R0 `< 2` goal. See `initial-dune-build.log` for the exact command and
complete compiler stdout/stderr. No repair or second proof compilation occurred.
No unit `.vo` was produced. The core dependency closure and both generated
finite-map modules compiled successfully as dependencies of that failed command;
this is not a successful unit target build.

The complete original statements and one-shot proof are frozen verbatim in
`initial-attempt.v.txt`, SHA256
`09737e2e7a0bab906ffe702b70fbc551538de98605d062d2973bb3d00edc0bd0`.
After failure, only proof bodies starting at the failing lemma were replaced
with `Abort`. Definitions and statements remain unchanged. The four earlier
Qed declarations (`port_set_welltyped`, `port_clear_welltyped`,
`mask_set_result_frame`, `mask_clear_result_frame`) were passed by the compiler
before its first error; they have no separately built/certified unit `.vo`.
`check-statements.py` verifies statement preservation. Later proofs were never
checked and may have further errors. No statement change is authorized merely
to make those proofs easier.

## Requested fixer work and specifications

Return to coordinator for a **new gpt-6.1-sol, xhigh/priority** fixer; this author
has not delegated, launched a fixer, or begun another proof cycle. Restore proof
bodies from the snapshot and fix them while retaining the statements unless a
statement is genuinely wrong, with each necessary change explained.

Unproved main declarations retained as Abort:

* `ulSetInterruptMask_correct`: any three actual finite-map instruction steps
  from the typed entry return to the modeled aligned LR target, yield the exact
  store with R0 equal to the old PRIMASK and PRIMASK=1, and satisfy the post/frame.
* `vClearInterruptMask_correct`: any two actual finite-map instruction steps
  yield PRIMASK = input R0 mod 2, preserve R0 and every other variable, and return
  to the modeled aligned LR target.
* `mask_set_execution`, `mask_clear_execution`: construct all three/two actual
  `can_step` transitions, including guarded BX, and the functional postcondition.
* `ulSetInterruptMask_satisfies_all`, `vClearInterruptMask_satisfies_all`:
  Floyd–Hoare interfaces up to the BX-instruction cut, complemented by the
  explicit BX execution and completed-step specifications.

Additional unchecked declarations include conditional code stability, typed
entry witnesses for both initial mask bits/either mode, arbitrary typed memory,
argument and SP, and instruction semantics/determinism helpers. Result frame
helpers assert all variables other than Set's R0/PRIMASK or Clear's PRIMASK are
unchanged. This includes memory, SP/LR, R1-R12, NZCV, access maps, temporaries,
Handler state and CONTROL.nPRIV. They describe proposed exact result stores;
without the main proofs they are not an execution frame theorem.

Entry hypotheses: full `models armv6mtypctx`, CONTROL.nPRIV=0, odd LR,
LR<0xfffffff0; 32-bit ARMv6-M ABI, typed 0/1 PRIMASK/Handler. No buffer sizes,
overlap restrictions or memory permission requirements. The inherited Cortex-M0
base profile supports either Thread or Handler mode. The code-stability
statements require equal CONTROL.nPRIV and LR; there is no false unconditional
store-independent nwc assertion. The statements do not exclude LR targets in
the function map: they claim the finite callee steps, not subsequent caller code.

Provenance is inherited, unvalidated binary/lifter refinement: FreeRTOS V11.1.0
source dbf70559b27d39c1fdb68dfb9a32140b6a6777a0, e04 ELF SHA256
5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca;
e19 base-profile maps at 0x4090/0x4094/0x4096 and 0x4098/0x409c. No generated map,
ISA, frontend, shared campaign file or accepted prerequisite was edited. No
asynchronous IRQ delivery/exclusion, barrier, scheduler, termination,
EXC_RETURN-as-normal-return, hardware or binary-refinement result is claimed.
The missing e05 24 call closures remain missing.

## Validation and assumptions

Exact sole proof command, via `tools/record-command.sh`:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOSMask/armv6m_port_mask_proof.vo'
```

Result: **exit 1**. Every compiler inherited the 2,000,000 KiB memory cap and
65,536 KiB stack. There was only one Dune build and no concurrent compiler.
No dependencies were installed; the isolated environment was reused read-only.

`tools/audit-proof-source.py --base 49956416928e5b6bb3928b54ae33e3b81091f006`
is recorded in `source-audit.log`; the initial scoped check is also retained.
No new Admitted/admit/Axiom/Parameter appears in the unit artifacts. Abort
is an unfinished declaration, not a certified theorem.

**Unit Print Assumptions output: unavailable.** No main theorem was compiled.
`tools/print-assumptions.sh` itself rebuilds the target; invoking it after this
failure would violate the one-build/no-Astra-repair instruction. It was not
invoked, and no assumptions output is fabricated. The fixer must build the full
unit, then use that helper for all main, frame, witness and stability facts and
inspect transitive assumptions. Baseline e00 reports inherited
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`; this
attempt imports functional extensionality for store equality helpers, but its
transitive assumptions have **not** been certified. An imported admission would
disqualify completion.

## Ancestry and local-only actions

Prepared HEAD was exactly e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9, whose
sole parent was pinned origin 49956416928e5b6bb3928b54ae33e3b81091f006.
The initial read-only `git ls-remote --heads fork
refs/heads/llm-proofs/r42-port-mask` succeeded with empty output before rename
(exit 0 in tool transcript). A redundant recorded query failed sandbox DNS
(exit 128, `fork-collision.log`); the successful recorded later query is
`fork-collision-recheck.log` (empty, exit 0). The original successful query was
the authorization condition for renaming only `t3/prove-armv6m-port-mask`.
The first rename attempt was blocked by read-only Git metadata; the explicitly
authorized rename and exact e19 fast-forward succeeded through sandbox escalation.

Only exact accepted e19 0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6, including its
reviewed e00/e03/e04/e05 and two e19 commits, was imported. The origin merge base
remains 49956416928e5b6bb3928b54ae33e3b81091f006. Before/after ancestry logs record
full commit IDs, diff stats and status. The initial workspace was clean before
creating this unit's evidence directory (the recorded pre-import status shows
that newly created directory). No other local branch was changed, no fork branch
was used as a base, and there were no pushes, PRs, remote comments or writes.
Only local unit commits follow accepted e19.
