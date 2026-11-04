# r11-missed-yield-fix

Initial author: OpenAI gpt-6-astra, xhigh/default, unit r11-missed-yield.
Final proof producer: OpenAI gpt-6.1-sol, xhigh/default. State: **DONE**
for the assigned sequential IL scope. All 18 original facts end in kernel-checked
`Qed`; no aborted theorem, admission or new axiom/parameter remains in the unit.

The prepared worktree was clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole parent is pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006`. The first read-only fork collision
check failed because sandbox DNS could not resolve github.com; the escalated
retry succeeded with no output. Only the prepared branch was renamed, to
`llm-proofs/r11-missed-yield-fix`, and fast-forwarded to exact authorized source
checkpoint `be3394d9240594694c90e28e5acf37887f9cf14e`. The first rename attempt
failed on read-only external git metadata and changed no branch; its authorized
retry succeeded. No other branch was modified.

The archived author source and initial failure evidence are retained byte for
byte under `notes/r11-missed-yield/`. The original attempt SHA256 is
`f4c7cb34fa53a4ecbd6e853d2852ee0e23bd188468531b82ac2a1dcac13cac9d`.
All 18 statements and 13 definitions are retained verbatim, checked by
`audit-statements.py`. The generated finite map is unchanged. No root Dune
module addition is necessary: the checkpoint already explicitly selects the
target and its dependencies.

Every compiler run uses the shared admission gate, the read-only toolchain
wrapper, 2,000,000 KiB address-space cap, 65,536 KiB stack, `-j1` and disabled
Dune cache. Builds, queries and failures are recorded with exact commands and
true exit codes by `tools/record-command.sh`. No host installs, shared
environment changes, remote writes, subdelegation or other-unit process
changes are performed.

Repair notes:

- Restored all original proof scripts from the archive. Temporary `Time`
  wrappers locate failing declarations without modifying their statements.
- Build 01 reproduced ABRT/OOM at the byte lemma, after the word lemma checked.
  `repeat split` attempts equality construction on a memory read and unfolds
  the enormous integer memory representation. The repair splits only the
  three conjunctions explicitly and applies the existing fully instantiated
  byte-extraction lemma, preserving the exact four-byte assertion.
- Build 02 passed the former OOM point and reported the first byte helper's
  numeric `<=` side condition: reflexivity cannot discharge that comparison.
  Replaced the four side-condition `reflexivity` proofs by `discriminate`.
- Made the return evaluation's low-bit cast explicit as
  `cast CAST_LOW 32 1 (s R_LR)` before applying `ECast`. This avoids the
  unification problem already evidenced in r06's original build. The public
  ordinary-LR guard is unchanged.
- Build 03 succeeded for all 18 facts. Removed temporary timing wrappers,
  updated only attribution/comments, then performed the clean final build and
  all assumptions queries successfully. There were no other statement,
  definition, generated-map, precondition or contract changes.

Scope remains sequential generated ARMv6-M IL: exact original-memory write of
1 to the four-byte word at 0x2000001c; disjoint modular byte frame; all-variable
frame except MEM/R2/R3/N/Z; typed writable entry witnesses; actual instruction
trace and ordinary odd LR below 0xfffffff0. No scheduler, IRQ, hardware,
whole-kernel, termination, or proved binary/lifter-refinement claim.


The checked coverage is:

- `missed_yield_correct`: `satisfies_all` for the actual finite generated map,
  typed entry at 0x9c0, exact postcondition at first BX LR cut 0x9c6.
- `missed_yield_post_at_bx`: for an actual execution from entry reaching the
  cut with an unterminated preceding trace, the whole final memory equals
  original memory updated by the four-byte little-endian store of 1; R2=1,
  R3=0x2000001c, N=Z=0 and the full variable frame holds.
- `missed_yield_functional`: the global word is 1, its exact bytes are
  [1;0;0;0], and every byte modularly disjoint from those four bytes agrees
  with ENTRY memory. The frame query's only overlap condition is
  `~ overlap 32 a 1 0x2000001c 4`; there is no old-value or address restriction
  on entry memory.
- `missed_yield_preserves_registers` and
  `missed_yield_preserves_callee_saved`: exact preservation outside
  MEM/R2/R3/N/Z, including SP/LR, R4-R11, other registers, permissions and
  temporaries. No stack access occurs; no disjoint-stack hypothesis is needed.
- `missed_yield_entry_satisfiable`: for arbitrary `m < 2^(8*2^32)` and any
  odd `lr < 0xfffffff0`, exhibits a typed store with original memory m, LR lr,
  and all four target bytes writable. The witness uses the symbolic
  `N.ones (2^32)` write-permission bitmap. Its numeric antecedents are
  inhabited, for example by m=0, lr=1; zero's bound follows from the checked
  polymorphic `missed_yield_zero_bound`, without evaluating the huge power.
- `missed_yield_ldr_step`, `missed_yield_mov_step`,
  `missed_yield_store_step`, `missed_yield_execution_witness`: actual
  LDR/MOVS/STR steps and their finite trace, with the exact postcondition.
  The store step requires only the four-byte write permission.
- `missed_yield_return_step`, `missed_yield_execution_returns`: guarded
  ordinary BX LR and the complete five-state execution trace, returning to
  `LR land (N.ones 32 - 1)` with the completed store. The explicit ordinary
  return guard is odd LR strictly below 0xfffffff0. No callee contract is used.
- `missed_yield_welltyped`, `missed_yield_nwc`, `missed_yield_memory_word`,
  `missed_yield_memory_bytes`, `missed_yield_memory_outside`, and
  `missed_yield_zero_bound` supply the typing, immutable-code and memory facts.

The ABI is AAPCS32, void, no register arguments. Address width is 32 bits;
0x2000001c is fixed, aligned, and the four-byte write does not wrap. There are
no CPU-feature, tunable, length, old-value or path-class hypotheses. Partial
correctness uses typed entry plus actual finite-map execution to the cut;
entry/execution witnesses additionally supply the write permissions and
ordinary LR. The generated decoder, folded immutable literal, pinned binary
and extraction provenance remain inherited trusted inputs. This is not a
hardware exception-return theorem, a concurrency/IRQ/critical-section proof,
a scheduler/whole-kernel theorem, a termination theorem, or proved binary
refinement. The C critical-section requirement is outside this sequential IL
specification. No gap remains within the assigned public statements.

Validation and exact commands:

```bash
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit r11-missed-yield-fix --memory-kib 2000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'bash notes/r11-missed-yield-fix/validate.sh'
```

`validate.sh` runs `dune clean`, then the actual full target
`dune build --cache=disabled -j1 --display short
Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.vo`, then
`tools/print-assumptions.sh` with **all 18** explicit theorem names.
The final gated validation, clean build and assumptions query all exit 0.
`build-clean.log` contains all compiler stdout/stderr; `assumptions.log`
contains the verbatim transitive reports. The surrounding gate transcript and
exact resource limits are in `validate.log` and `validate.sh`. No `.vos` or
skipped checking is used. Builds 01/02 exit 1, build 03 exits 0; each has its
source snapshot and unmodified raw log. Admission waits are retained too.

`source-audit.log` records the required base-wide auditor against
49956416928e5b6bb3928b54ae33e3b81091f006 (exit 0, NEW totals {}). Existing
unrelated baseline admissions remain inventoried by that audit; they are
outside this target's dependency closure. `unit-source-audit.log` has zero
baseline/current/new tokens. `statement-audit.log` proves original statement
and definition retention and immutable author evidence. All proof/source/retention audits exit 0.
The source-only whitespace check exits 0. The full staged whitespace check
exits 2 solely because Rocq prints a trailing space in a theorem type in the
raw assumptions output (also repeated in the outer validation log). Those
bytes are deliberately preserved; `raw-log-whitespace.log` records this check
and its true exit status.

The 11 closed facts are welltyped, nwc, memory_word, memory_bytes,
memory_outside, preserves_registers, zero_bound, entry_satisfiable, ldr_step,
mov_step and store_step (all prefixed `missed_yield_`). The other seven are
correct, post_at_bx, functional, preserves_callee_saved, execution_witness,
return_step and execution_returns. Each of those has exactly the same
previously documented baseline Stdlib functional-extensionality axiom:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

`assumptions-audit.log` inspects all 18 raw reports and rejects any additional
axiom or imported admitted proof. The known e00/r06 baseline documents this
axiom; the return proof also uses it to equate reset stores. Closed facts print
`Closed under the global context` verbatim. These are transitive checks, not
merely a lexical source audit.

Ancestry and publication boundary:

- `ancestry-checkpoint.log` records the exact imported history (11 allowed
  prerequisite commits above origin), merge base, diff stat and status.
- `check-ancestry.py` checks the exact allowed checkpoint, linear own history,
  unit-only changed paths, original archive and generated-map preservation,
  assigned branch and origin pin. `ancestry-precommit.log` is captured before
  the local commit. The final commit SHA and clean postcommit status are
  recorded externally only in the authorized unique unit evidence directory
  `/home/charles/code/friends/.refs/picinae-llm-proofs/units/r11-missed-yield-fix/`.
- Worktree: `/home/charles/.t3/worktrees/Picinae/t3-7fbb9e39`.
  Local branch: `llm-proofs/r11-missed-yield-fix`.
- Original author branch and exact initial evidence are preserved. No push,
  PR, comment, remote write, other-branch modification, dependency install,
  shared environment/config edit or subagent was used.
