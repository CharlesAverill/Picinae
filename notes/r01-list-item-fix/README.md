# r01-list-item-fix — DONE

Initial statements/attempt: OpenAI gpt-6-astra, xhigh, priority.
Final proof producer: OpenAI gpt-6.1-sol, xhigh, priority.
Branch: `llm-proofs/r01-list-item-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-856859c4`.
Checkpoint: `36b196e6bcf526b568e1b1b6990f2aa11640e546`.
The implementation commit is identified by `30-implementation-commit.log` and
`31-after-implementation.log`; the later evidence commit changes notes only.

All **14 original theorem statements and all definitions/predicates are retained
byte-for-byte** from `notes/r01-list-item/initial-attempt.v.txt`. All 14 now end
in `Qed`. There are no missing/aborted declarations, admissions, axioms or
parameters in the proof file. The only change outside proof bodies is the
final-producer attribution/validation-note pointer in the header. The four
original prefix proofs are unchanged. Original author notes and archived attempt
remain unchanged; this DONE result supersedes their historical PARTIAL status.

## Actual specification and coverage

The unchanged accepted finite instruction map is the official FreeRTOS V11.1.0
Cortex-M0 fixture, ELF SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`:
entry **0x56 MOVS R3,#0**, **0x58 STR R3,[R0,#16]**, designated exit
**0x5a BX LR**. This is AAPCS32, with 32-bit registers/addresses and four-byte
little-endian field writes; no x86/AArch64 ABI is imported.

- `item_welltyped`, `item_nwc`: actual generated finite map is welltyped and
  independent of data-memory contents.
- `item_memory_fields`, `item_memory_outside`: clear the container word at
  offset 16 in a 20-byte item, preserve original value/next/previous/owner,
  and compare **every byte outside the four-byte write to original memory**.
- `item_preserves_registers`: along actual map executions every variable
  except V_MEM32/R3/N/Z is unchanged. Includes R0, R1/R2, R4–R12, SP/LR,
  C/V, read/write/execute permission maps and every temporary.
- `item_exact`: actual `satisfies_all` invariant proof from 0x56 to 0x5a,
  assuming only a typed initial state and the original trace-start equation.
  Exact modular-address store, R3=0, N=0, Z=1 and register frame. Successful
  executions can be characterized without assuming writable permissions or
  a nonwrapping object; this theorem alone is partial correctness.
- `item_correct`: for an actual execution reaching the designated exit for
  the first time, establish `item_post`, all preserved original field values,
  zero container, and the outside-byte frame. `item_entry` requires typed
  initial state; nonnull pointer p=R0 with p mod 4=0, p<2^32 and p+20<=2^32;
  write permission on each of `(p+16+i) mod 2^32` for i<4; ordinary LR with
  LR<4294967280 and LR mod 2=1. No second-object separation, memory-value,
  stack-access, CPU-tunable or callee-contract hypothesis is added.
- `item_entry_store_witness`: executable, typed and writable entry over any
  original memory m<memsize 32 and any valid object pointer. Original m is
  unchanged in the witness; R0=p, SP=8192, LR=257. The all-writable mask
  `N.ones (2^32)` stays symbolic, using `ones_bound` and bit-index bounds.
- `item_arbitrary_fields_witness`: inhabited entry for any valid pointer and
  any five independently chosen unsigned 32-bit field values. It uses the
  accepted r00 image constructor over typed zero memory, plus real writable
  permissions; it does not rely on r00's zero-permission state being executable.
- `item_mov_step`, `item_store_step`: actual modeled MOVS and STR steps;
  MOVS works over any store, STR requires `item_writable` only.
- `item_execution_witness`: from every `item_entry`, construct the actual
  two-step trace reaching 0x5a and establish the exact postcondition.
- `item_return_step`, `item_execution_returns`: actual modeled ordinary BX
  transfer to `N.land LR (N.ones 32-1)`, preserving the post-store state.
  Retain the ordinary odd LR/below-EXC_RETURN boundary from the original
  statements, even where a particular proof uses only oddness.

The exact path is straight-line, with one four-byte store. Field separation
comes from the object's nonwrap bound. No extra overlap exclusion is needed;
other aliased memory objects are protected only where their bytes lie outside
this store. No load or stack memory access occurs.

These are checked sequential IL results under inherited accepted lift/model
provenance, not a hardware/lifter refinement, IRQ/concurrency/scheduler/TCB,
EXC_RETURN or whole-kernel termination result. The explicit finite ordinary
return witness is recorded without upgrading it to a broader binary-soundness
or termination claim. No helper/callee contract is silently assumed.

## Repair and validation

Restore the **entire** archived attempt first. Repair the original failing
frame proof by reducing the finite-map/decode to a concrete statement before
constructing the `allassigns` proof. Further failures exposed tactic elaboration
issues: normalize 16+p to p+16 in the exact-state proof; supply explicit
instruction addresses, values and widths to execution constructors; express
store reads through the post-MOV state; rewrite only the returned store in
BX's reset identity; rewrite oddness in a separate evaluated-expression fact
rather than rewriting width literals. No statement correction was needed.

Every attempted full target build and diagnostic failure is retained in
`02`–`17` logs with exact command, stdout/stderr and real exit code. The first
successful full `.vo` target is `17-dune-repair.log` (exit 0). After final
provenance text, `23-final-clean-build.log` records a **clean rebuild of the
entire relevant dependency closure**, exit 0:

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInitialiseItem_proof.vo'
```

Root Dune already explicitly selected this target and its dependencies in the
assigned checkpoint, so no Dune edit was needed. Its `mode vo` is unchanged.
No `.vos`, cache import, skipped proof checking or concurrent compiler was used.
Every Dune/Rocq/assumptions process ran under 2,000,000 KiB virtual memory and
65536 KiB stack, with `-j1`. No cap increase, installation, shared environment
change or other unit process interruption occurred.

`24-final-assumptions.log` contains **verbatim Check/Print Assumptions for all
14 declarations**, via the required helper, exit 0:

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  env PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536 \
  bash tools/print-assumptions.sh \
  Picinae.Examples.FreeRTOS.armv6m_vListInitialiseItem_proof \
  item_welltyped item_nwc item_memory_fields item_memory_outside \
  item_preserves_registers item_exact item_correct item_entry_store_witness \
  item_arbitrary_fields_witness item_mov_step item_store_step \
  item_execution_witness item_return_step item_execution_returns
```

Nine are `Closed under the global context`. The remaining five are
`item_exact`, `item_correct`, `item_execution_witness`, `item_return_step` and
`item_execution_returns`. Each has **only** the inherited
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This includes the core framework's extensionality, already documented in e00,
and the explicit reset identity in the ordinary-return proof. It is recorded,
not hidden as a closed result. The exact dependency inventory is checked in
`28-assumptions-review.log`. No imported admitted proof appears transitively.

`20-source-audit.log`: required full source audit against pinned base, exit 0,
`NEW totals: {}`. Baseline unrelated admissions/interface parameters remain
outside this theorem dependency closure. `21-unit-source-audit.log`: unit
baseline/current/new totals all `{}`, exit 0. `27-final-preservation.log`:
all original declarations/definitions retained, all 14 Qed, exit 0. No new
supporting declaration or assumed result was introduced.

## Local history and boundaries

`preparation.txt` honestly summarizes initial preparation, including the
successful read-only fork-name check before rename and the filesystem sandbox
failure/retry for Git metadata. The later redundant remote-name recheck in
`25` failed DNS (exit 128); it does not invalidate the successful pre-rename
check and no remote write was attempted. `26` independently records the e00
sole parent and branch-rename/fast-forward reflog.

The merge base is exactly `49956416928e5b6bb3928b54ae33e3b81091f006`.
`audit-ancestry.sh` enumerates the exact 13 accepted checkpoint/prerequisite
commits, then permits only explicitly supplied fixer commits. It checks scoped
changes against exact checkpoint `36b196e...`, preserving the generated lift,
ISA, r00 kit, root Dune, original author notes and r00 notes byte-for-byte.
`01`/`22`/`29`/`31` record history, diff stats and status. No fork branch was
used as a base and no unrelated history was imported. Only this prepared branch
was renamed. No original author branch/worktree or shared plan/status/campaign
file was changed. No subagent, host install, remote write, push, PR or publication.

No remaining proof gap in the assigned 14-statement sequential IL scope.
