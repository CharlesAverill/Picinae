# r07-current-task — PARTIAL, Astra one-shot handoff

Initial author: OpenAI gpt-6-astra, xhigh. Requested service tier: default.
Final proof producer: NONE; no unit theorem was kernel checked.
Branch: `llm-proofs/r07-current-task`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-459be5b6`.
Prerequisite: `5fec2fc24d0c739bafc08add426f02a3085e15cd`.
Origin/base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

The one permitted full Dune build exited **1**, before any new theorem was
processed. At line 18 of the proposed proof header, `sizeof(void*)` contains
Rocq's comment terminator `*)`. The remaining prose was parsed as vernacular:

```text
File "./Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v", line 18, characters 32-33:
Error: Syntax error: illegal begin of vernac.
```

Per Charles's one-shot policy, there was no repair or second compilation.
The coordinator must assign a NEW `gpt-6.1-sol`, xhigh/default fixer, retaining
the statements unless a genuine error requires an explained change. The
immediate syntax repair is to reword the sizeof expression in the comment;
the proofs have not yet been elaborated, so further errors remain possible.
No successful full unit target and no assumptions certificate are claimed.

## Preserved handoff

- `initial-attempt.v.txt` is the exact complete proposed proof, SHA256
  `8bc7f4bd966dee9fad5e9bb44c7264fbb50d23084bcb65dee45664acdac650d5`.
- `statements.v.txt` extracts all 13 theorem/lemma/corollary statements verbatim.
- `initial-dune.patch` preserves the explicit module addition and target alias.
- `06-initial-build.log` contains the exact command, all compiler stdout/stderr,
  shared-admission output and true exit code 1.
- `04-provenance.log` records read-only hashes of the pinned source, config,
  ELF and unchanged generated lift, plus source/global/layout evidence.

The failed proof was removed from active `.v` inputs and the root Dune edit
was reverted to its prerequisite contents. Only WIP notes/archived attempts
are committed: no unverified proof is presented as completed, and no new
admissions, axioms or parameters are introduced. To resume, restore
`initial-attempt.v.txt` as
`Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v` and apply
`initial-dune.patch`, then correct the comment before compiling.

## Intended statements, not established results

The unchanged finite generated `xTaskGetCurrentTaskHandle_armv6m_prog` has
entry 0x12dc, word load at 0x12de, and designated exit before BX LR at 0x12e0.
Its folded literal at 0x12e4 is 0x20000108. The official V11.1.0 single-core
source returns `pxCurrentTCB`; the pinned manifest and nm evidence locate that
four-byte global at 0x20000108, offset zero. No TCB object field is accessed.
The pointer ABI is 32-bit; the file uses ARMv6-M memory operations, not x86 or
AArch64 widths.

The intended `current_task_correct` / `current_task_post_at_bx` prove R0 equals
the four-byte little-endian word in ORIGINAL memory, with every variable
except R0/R3 unchanged. `current_task_preserves_memory`,
`current_task_preserves_callee_saved` and `current_task_original_bytes` cover
full memory, R4-R11/SP/LR and every original byte. `current_task_return_step`
and `current_task_caller_result` provide an actual modeled BX step under odd
LR and LR < 0xfffffff0, preserving the entire state and clearing LR bit zero.
`current_task_nwc` and `current_task_welltyped` cover code independence/typing.
`current_task_zero_bound`, `current_task_witness_models`,
`current_task_entry_satisfiable` and `current_task_entry_nonempty` provide
arbitrary-memory typed/permitted entry witnesses and an inhabited instance.

Functional statements require a modeled initial store and entry; exit
corollaries require an actual execution and no earlier designated exit. Load
permissions follow from the actual execution; witnesses explicitly supply
readability. No result/nonzero/object-validity condition is assumed. No size,
overlap, CPU-feature, tunable, scheduler-cardinality or whole-kernel hypothesis
is added. No callee is called or assumed. The scope is sequential IL partial
correctness and an ordinary return step, not termination, IRQ/hardware or
binary/lifter refinement. Folded literal immutability remains trusted.

## Validation and assumptions

The exact one-shot command, invoked via `tools/record-command.sh`, was:

```bash
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
 --unit r07-current-task --memory-kib 1750000 -- \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 1750000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.vo'
```

The gate admitted the run at 1750000 KiB. Dune compiled the dependency closure,
including the generated getter, before the proposed proof failed. The source
uses full `mode vo`. No `.vos` or skipped proof checking, concurrent compilers,
new installation, shared-environment change, or cap increase was used.

Whole-tree source audit against the exact origin base (`07-source-audit.log`)
exited 0, with `NEW totals: {}`. The active proposed unit and lift audit also
exited 0 (`08-unit-source-audit.log`) before the attempt was archived. The
baseline has unrelated admissions and interface parameters; these are not a
certificate of the new proof. Final source audit is recorded separately.

`tools/print-assumptions.sh` was NOT invoked: the new module has no successful
`.vo`, and that script would retry the failed full build. There is therefore
no raw Print Assumptions output for any new theorem. The accepted r06 template
reports inherited Stdlib `FunctionalExtensionality.functional_extensionality_dep`
for its five main execution/return facts; e00 documents that trust boundary.
The proposed r07 attempt also uses extensionality, but its transitive
assumptions are UNVERIFIED. A fixer must query every new theorem and reject
any inherited admitted proof dependency before claiming completion.

## History and local-only scope

Initial observation was a clean prepared branch `t3/prove-current-task-handle`
at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent pinned origin.
The first sandbox remote check failed DNS (exit 128); the recorded network
retry succeeded with no result before the branch rename. Only this prepared
branch was renamed, and it was fast-forwarded to the exact assigned head.
The prerequisite includes the accepted e00/e03/e04/e05/r06 history, including
the original r06 author checkpoint and Sol completion. No unrelated history
or other branch was modified. No worktree was created.

`01-before.log` includes the new evidence directory itself as untracked; the
initial observation before creating it was clean. `03-prepare.log` records
the full import, log, diff stat, merge-base and working status. An ancestry
script checks the exact allowed prerequisite union and permits only scoped
notes commits above it. Final clean-tree evidence is saved under the assigned
external `units/r07-current-task/` evidence directory to avoid self-modifying
committed logs. There were no pushes, PRs, comments or remote writes.

State: **PARTIAL**. Remaining work: restore and fix the archived attempt using
a new Sol delegate; complete the full target, all Print Assumptions queries,
source and ancestry audits. No actual unit theorem is claimed proved.
