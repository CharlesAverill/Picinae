# a-inet-makeaddr-fix

**DONE: full kernel-checked sequential IL partial correctness.**
`author_model=gpt-6-astra`; `final_proof_model=gpt-6.1-sol`.
The original author ran xhigh/priority, as its evidence records; this fixer
ran xhigh/default. Original author branch and `notes/a-inet-makeaddr/`
are preserved unchanged. There is no remaining proof gap in the assigned
scope; inherited provenance and the semantic limits below remain explicit.

Assigned branch: `llm-proofs/a-inet-makeaddr-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-0bd22e4f`.
Pinned origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Authorized source checkpoint: `e3ddea3cffe75231193e5b51e04a30ee7012e17a`.

## Scope retained from Astra

All 18 theorem/lemma statements and nine definitions are retained verbatim
from `notes/a-inet-makeaddr/initial-attempt.v.txt`. No precondition,
postcondition, frame, witness or invariant statement changes are needed.
`check-retention.py` checks their exact text, the generated map hash, original
author evidence, the assigned branch, and allowed ancestry.

`inet_makeaddr_correct` states `satisfies_all` partial correctness from
`0x1f9d40` to any of the three RET sites `0x1f9d50`, `0x1f9d68`, `0x1f9d88`.
Every low32 X0/X1 input pair is covered with arbitrary upper halves under
ordinary 64-bit Picinae typing. The four network classes use boundaries
128, 65536, 16777216; the final branch ORs the arguments. The result in X0
is the zero-extended byte reversal of the 32-bit assembled address.
The main postcondition includes memory, SP and X30 equality. Separate
`forall_endstates` frames preserve modeled X19–X29 and Z8–Z15 as well as
memory, SP and X30. Typed input and postcondition witnesses are retained,
including arbitrary 32-bit upper halves in the input witness.

There is no memory-accessibility/content, buffer size, overlap, callee,
global, CPU-feature, tunable, or result-oracle premise. This is a theorem
about the exact inherited sequential IL, not termination, verified lifting,
hardware faults, cache/timing, concurrency, or whole-binary refinement.
The unchanged 19-instruction, 76-byte map comes from the e29 Ghidra 11.4.2
explicit scalar replacement for Ubuntu ARM64 glibc 2.35-0ubuntu3.15,
libc SHA256 `79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
Map SHA256: `41c9789da4f26019b8c8b9269f421d8f1ac74b0a34925d1b2b5d4c74a8d75ae8`.
Its inherited binary/lifter provenance remains unproved.

## Repair and resource evidence

The complete original attempt was restored. The initial mask/testbit
failure requires normalizing `N.ones 32`, evaluating closed mask bits and
closed comparisons explicitly. The main script also contained the invalid
empty `clear -` command. Proof repair is local to this module's tactics;
the generated map, shared proof libraries and root Dune list are unchanged.

The first main bit-analysis attempts exceeded the assigned virtual-memory
cap. `logs/10-build.log`, `13-timed-main.log` (exit 134), and `15-build.log`
record the actual failures. The timed run isolates the expensive final
bit-analysis tactic after successful stepping and branch reasoning.
`14-goals.log` is an intentional failing diagnostic showing seven remaining
pure bitvector equalities. Its exact source and the timed/pruned attempts
are archived as `.v.txt` files in this directory.
Only these fixer's snapshots have trailing blank lines at EOF normalized;
all proof lines and diagnostic line numbers are preserved. The Astra
archive is unchanged. The initial staged whitespace check (external log
28) caught those blank lines; the normalized snapshots pass the final check.

`17-bit-timing.log` refines the diagnosis: it completed the first main
equality, then exhausted memory on bit 25 of the second. The next repair
simplifies both left and right boolean identities before leaf splitting,
clears unused execution context, resolves high-bit comparisons using bounds,
and uses `abstract` to check each final equality as an opaque subproof.
These are proof-term/automation changes only; no contract or IL change.

Every proof/Dune/assumptions process uses `ulimit -v 2000000` and
`ulimit -s 65536`. Dune uses full `.vo` mode, `--cache=disabled -j1`, one
compiler at a time. The shared isolated toolchain wrapper is reused without
modification; no dependency was installed. No worktree was created and no
other branch was modified. No push, PR, comment or remote write occurred.

## Preparation and ancestry

The initial worktree was clean at e00, whose sole parent was the pinned
origin base. Creating the evidence directory accounts for the untracked
notes visible in `00-prepared.log`. The sandboxed read-only fork lookup
failed DNS; the network-enabled retry returned exit 0 with no branch.
The sandbox denied the first rename and merge because Git metadata is
outside the writable worktree; the authorized retry renamed only the new
prepared branch and fast-forwarded the exact checkpoint.

`01-allowed-checkpoint.log` records the exact seven allowed commits above
origin, including only the authorized reviewed upstream prerequisites:

- `71470bffba65392adf1873a3df9f0cf0ca4f1ac9` (e00)
- `081d0233cd6667803b3907343b2fea6dc9eba714` (e02)
- `052521a753adbda077843ec7b259801282a7b1e9` (reviewed e02 merge)
- `378fe1b57514b9af3f017a72b4ca665910156cc7` (e11)
- `9ae8e6800fa044797efd98372857e6ac89b18e1b` (e08)
- `9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b` (e29)
- `e3ddea3cffe75231193e5b51e04a30ee7012e17a` (Astra source checkpoint)

Only this unit's scoped linear commits may follow that set. The original
`llm-proofs/a-inet-makeaddr` branch remains at the checkpoint.

## Retained facts

| Declaration | Coverage |
| --- | --- |
| `inet_makeaddr_nwc` | Map independent of the input store |
| `inet_makeaddr_welltyped` | Full generated IL map typing |
| `inet_makeaddr_preserves_memory` | Memory frame for all end states |
| `inet_makeaddr_preserves_callee_saved` | All 21 listed modeled saved registers |
| `inet_makeaddr_preserves_sp` | SP frame |
| `inet_makeaddr_preserves_x30` | Link register frame |
| `inet_makeaddr_ret_map` | Actual X30 RET semantics at all three sites |
| `inet_makeaddr_result_bound` | Result is below 2^32 |
| `inet_rev32_correct` | Byte-reversal expansion equals `ntohl32` |
| `inet_bfm24_correct` | BFM implements network<<24 plus low24 host |
| `inet_bfm16_correct` | BFM implements network<<16 plus low16 host |
| `inet_bfm8_correct` | BFM implements network<<8 plus low8 host |
| `inet_msub32_eqb` | 32-bit subtraction zero test is operand equality |
| `inet_makeaddr_zero_typed` | Inhabited zero typed store |
| `inet_makeaddr_input_typed` | Typed inputs with arbitrary 32-bit upper halves |
| `inet_makeaddr_inputs_inhabited` | Entry invariant witness for every input pair and upper halves |
| `inet_makeaddr_spec_inhabited` | Typed postcondition witness for every input pair |
| `inet_makeaddr_correct` | All four branches, endianness, memory/SP/X30 postcondition |

The nine retained definitions are `makeaddr`, `inet_makeaddr_result`,
`inet_makeaddr_postcondition`, `inet_makeaddr_exit`, `inet_makeaddr_invs`,
`inet_makeaddr_saved`, `inet_rev32`, `inet_bfm32`, and `inet_makeaddr_input`.

## Validation record

`18-build.log` is the first successful complete `.vo` target, exit 0.
It prints all 18 retained facts' assumptions, including the main theorem.
The subsequent comment-only author/provenance update is checked by the
clean final build rather than relying on that earlier object.

`19-retention.log` reports an evidence-ordering error: the concurrently
started clean rebuild removed the `.vo` before the retention script checked
its existence. Its statement/definition checks passed, but its true exit is
1. `23-retention.log` is the successful final check after the clean build.
`20-source-audit.log` passes for all 342 source files relative to the pinned
base, with `NEW totals: {}`. The seven baseline admissions, one baseline
`admit` and 89 module-interface parameters remain inventoried; they are not
evidence of dependencies of this proof. Transitive assumptions are checked
separately by `print-assumptions.sh`.

`21-clean-build.log` records `dune clean` followed by the successful full
target build of the final source, exit 0, elapsed 4:39.25, maximum resident
set size 1,524,220 KiB, zero swaps. The exact isolated capped command was:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536; dune clean; /usr/bin/time -v dune build --cache=disabled -j1 --display short Examples/claude/arm8_inet_makeaddr_proof.vo'
```

`22-assumptions.log` contains the complete raw `Check` and `Print Assumptions`
output for every retained fact and definition, plus the imported map's typing
theorem. It uses `tools/print-assumptions.sh`, which also successfully rebuilds
the exact target with cache disabled and `-j1`. Its actual exit is 0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; bash notes/a-inet-makeaddr-fix/print-assumptions.sh'
```

`24-assumptions-review.log` checks all 28 blocks: 25 are closed; exactly
`inet_makeaddr_welltyped`, `inet_makeaddr_correct`, and the imported map's
`welltyped` use inherited functional extensionality only. There is no imported
admitted theorem or other assumption. Verbatim output for each of those three:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the existing Stdlib assumption documented in e00's
`notes/e00-build/logs/15-extensionality-provenance.log`; these three facts
are **not closed**. Among the unit's 18 theorem/lemma facts, 16 are closed
and two are FE-only. All nine definitions are closed.

The source audit, retention/ancestry audit, and whitespace check all pass.
No live `Abort`, admission, new axiom or parameter remains. Only the proof
module and this unit's notes differ from the authorized checkpoint.
Final commit and clean post-commit ancestry evidence are recorded separately
under `/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-inet-makeaddr-fix/`.
