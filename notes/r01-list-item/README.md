# r01-list-item — PARTIAL author handoff

Initial author: OpenAI **gpt-6-astra**, xhigh, priority. Final proof producer:
**none**. A new gpt-6.1-sol xhigh/priority fixer is required; no fixer was
spawned and no second proof compiler/build was run.

Branch: `llm-proofs/r01-list-item`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-4346038a`.

The initial full target failed with exit **1** at initial source line 102,
in `item_preserves_registers`. The constructor tactic did not reduce the
lifted MOVS form to an assignment constructor:

```text
Unable to unify "allassigns ?M1791 (If ?M1792 ?M1793 ?M1794)" with
 "allassigns (fun v0 : ARMv6MArch.var => v0 <> v)
    (arm2il 86 (thumb16_decode (vListInitialiseItem_armv6m 86)))".
```

`02-dune-initial.log` preserves the exact command, full stdout/stderr and exit.
The immutable `initial-attempt.v.txt` contains all original statements and
one-shot proofs (SHA256 in `01-initial-source.log`). The active proof file
retains all definitions and statements byte-for-byte. Only the ten unchecked
proof bodies were replaced by `Abort`; `04-preserve-statements.log` verifies
that transformation. No repair attempt followed the failed build.

## Scope of statements, not a completion claim

- `item_welltyped`, `item_nwc`, `item_memory_fields`, `item_memory_outside`
  reached Qed before the failure. These four unchanged helper proofs remain
  in the active source, but no full unit `.vo` was produced and no separate
  certification of them is claimed.
- `item_preserves_registers`: every variable except memory, R3, N and Z is
  preserved along actual finite-map executions; includes SP/LR, all other
  GPRs, C/V and permission maps.
- `item_exact`: real `satisfies_all` over the unchanged generated finite map,
  from 0x56 to designated BX exit 0x5a. Exact original-memory store at R0+16,
  R3=0, N=0, Z=1, and register frame. Requires typed initial state; the
  exact modular-address partial-correctness statement does not require a
  nonwrapping object or permissions to characterize successful executions.
- `item_correct`: at an actual reached designated exit, container is zero,
  initial value/next/previous/owner are unchanged, and every original byte
  outside the four-byte write is unchanged. Entry additionally requires
  nonnull/aligned/nonwrapping 20-byte object, writable container bytes and
  ordinary odd LR below 0xfffffff0. No extra object separation hypothesis.
- `item_entry_store_witness`, `item_arbitrary_fields_witness`: inhabited,
  typed and writable entries over arbitrary memory / arbitrary five 32-bit
  field values. The symbolic all-writable mask is never evaluated as a
  giant memory integer. SP=8192 and LR=257 in these constructed witnesses.
- `item_mov_step`, `item_store_step`, `item_execution_witness`: actual modeled
  two-instruction execution reaches the BX with the postcondition.
- `item_return_step`, `item_execution_returns`: actual modeled BX transfer
  to LR with Thumb bit cleared under the explicit ordinary odd LR boundary.

All ten latter declarations are **Aborted, not available theorems**. The fixer
must retain the statements unless genuinely wrong, and explain any statement
change. Claims are sequential IL only: no termination, IRQ stability, TCB or
scheduler invariant, EXC_RETURN, callee contract, hardware or binary/lifter
refinement. The void ABI preserves R0. This function does not initialize all
five fields. The exact CPU/config/provenance is in the proof header.

## Validation and assumptions

The only full Dune command was:

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInitialiseItem_proof.vo'
```

Result: **exit 1**, logical proof failure, no cap increase. Core dependencies,
ARMv6-M ISA, accepted list model and generated target lift built successfully
within this invocation. **Successful unit target commands: none.**

`tools/print-assumptions.sh` was not run: it would rebuild the failed unit,
violating the one-shot handoff rule. There is no raw unit assumptions output.
See `assumptions-status.txt`. The inherited baseline axiom
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` is known
and honestly recorded; the accepted r00 facts have inherited closed-assumptions
evidence. No new theorem's transitive assumptions are certified here.

Full source audit against pinned base and the unit-only audit both exited 0:
`NEW totals: {}`; unit `CURRENT totals: {}`. Baseline unrelated admissions
remain outside the selected dependency closure. No new admission, axiom or
parameter is present. Statement preservation also exited 0.

## Preparation and ancestry

Initial clean prepared branch `t3/list-item-container-clear` was exactly e00
71470bffba65392adf1873a3df9f0cf0ca4f1ac9, whose sole parent is pinned base
49956416928e5b6bb3928b54ae33e3b81091f006. The read-only fork-name check first
failed DNS in the sandbox (128); its authorized network retry succeeded (0)
with no result. Only the prepared branch was renamed. Sandbox git metadata
was read-only (rename exit 128); the authorized retry performed:

```bash
git branch -m llm-proofs/r01-list-item && git merge --ff-only 4ff26413448da4d8f064b0273ac5472cc9de7e5a
```

Result: exit 0, fast-forward only. `audit-ancestry.sh` enumerates all eleven
exact allowed prerequisite commits (e00/e03/e04/e05, original r00 author and
two accepted r00 Sol commits) and requires explicit own unit commits. Merge
base is the pinned origin base. Before/after logs record history, diff stats,
status and protected-file identity. The only root Dune change is adding this
proof module. Generated lift, shared memory kit and ISA remain unchanged.

No dependency installation, shared-environment modification, remote write,
push, PR, branch deletion, unrelated history or campaign-file edit occurred.
