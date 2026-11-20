# a-insque: AArch64 LP64 exact insertion

State: **PARTIAL — first full build failed, Sol fixer required.** This is not
a completion certificate. Initial author: **gpt-6-astra**, reasoning xhigh, service tier
default as assigned. No final proof producer is claimed before successful
kernel checking. No Sol fixer was spawned by this child.

Branch: `llm-proofs/a-insque`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-378c8105`.

## Statements and coverage

The unchanged generated program is
`Examples/claude/lifter/scalar_ports/e08_insque_arm8.v`, SHA256
`0d6d574a200f0674353fc00c68f9affb99de3eb33944637d454c7bcbe3056879`.
Its eight instructions occupy 32 bytes at model addresses 0x1e45e0–0x1e45fc
(ELF 0xe45e0, image base 0x100000). Runtime ELF SHA256 is
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
The accepted e08/e11 scalar replacement and its historical provenance are
inherited; no new lifting or binary-soundness claim is made here.

`initial-attempt.v.txt` preserves the complete initial statements and tactic
attempt, byte for byte as submitted to the first build. The initial target is
`Examples/claude/arm8_insque_proof.vo`. Only that proof module was added to
Dune's explicit module list; its generated dependency was already listed.
No AMD64 proof or `amd64_common` is imported by the new module.

Intended main statements (their status is determined by the build, not by a
`Qed` token in an unchecked attempt):

- `insque_exact`: `satisfies_all` from 0x1e45e0 to the pre-RET exit 0x1e45fc;
  typed state, X0/X1 input pointers, original memory, SP and X30 input values.
  Exact ordered writes handle null predecessor, null successor, non-null
  successor, all aliases, and modular wrap. There is no input size argument.
- `insque_preserves_callee_saved`: X19–X29, SP, X30, modeled Z8–Z15 and access
  bitmap preservation on all endstates.
- `insque_ret_map`, `insque_return`, `insque_return_frame`: actual generated
  RET map and an explicit execution to X30, changing PC alone. These are
  separate from the pre-RET invariant theorem; no whole-run termination claim.
- `insque_empty_links`, `insque_links`: recover the pointer fields when the
  inserted 16-byte node does not wrap and is separated from neighbor writes.
  Neighbor write fields may coincide (same value written) or be disjoint.
  In particular a singleton circular list with prev=next is permitted.
- `insque_byte_frame`: every byte outside the path-dependent writes equals
  the byte in original memory; no global pairwise-disjointness assumption.
- `insque_empty_witness`, `insque_tail_witness`, `insque_circular_witness`:
  concrete typed states and sufficient access/nonwrap contracts. Element at
  512; nonempty predecessor at 256; circular successor also at 256. The
  permission bitmap grants the first 1024 bytes. These witnesses do not prove
  whole-program execution or a sequence/cardinality abstraction.

`insque_access` requires writable elem[0..15], readable/writable prev[0..7]
when non-null, and writable next[8..15] when non-null, with nonwrapping upper
bounds. The conditional trace theorem is stronger and does not require this
additional predicate: existence of modeled execution already requires access.
No CPU-feature/tunable/callee hypothesis is used. Alignment, hardware faults,
concurrency, lifetime, lifting refinement, full ABI beyond modeled registers,
and termination are outside the claim.

## Validation and handoff rules

The exact resource-gated build command, full stdout/stderr and real exit code
are in `initial-build.log`; memory 1,750,000 KiB, stack 65,536 KiB,
`--cache=disabled -j1`, full `.vo` mode. Admission waits are not compiler
attempts. No second Astra repair/build cycle is authorized.

`source-audit.log` records the required repository-wide source audit against
`49956416928e5b6bb3928b54ae33e3b81091f006`. Baseline admissions are inventoried,
not certified. This module's imports are ARM8 core and the generated e08 map.
Source audit alone cannot establish absence of transitive assumptions.

`check-assumptions.sh` is the exact resource-gated command to invoke
`tools/print-assumptions.sh` for all 19 proposed facts after a successful
full-target build. Baseline ARM8 typing and functional theorems have inherited
`FunctionalExtensionality.functional_extensionality_dep`; any actual output
must be recorded verbatim, and any admitted dependency disqualifies DONE.

## Ancestry and local-only operations

Initial status was clean, prepared branch `t3/aarch64-insque-proof`, HEAD e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, sole parent pinned origin
`49956416928e5b6bb3928b54ae33e3b81091f006`. The first sandboxed fork collision
query failed with DNS resolution error (exit 128); the network-enabled retry
succeeded with empty output (exit 0, `branch-collision.log`). Initial branch
rename failed with read-only metadata (exit 128); authorized escalation then
renamed only the prepared branch and fast-forwarded it to the assigned head
`9ae8e6800fa044797efd98372857e6ac89b18e1b` (`prepare-branch.log`).

The exact accepted prerequisite union above origin is e00, partial e02 artifact
gate `081d0233cd6667803b3907343b2fea6dc9eba714`, reviewed import merge
`052521a753adbda077843ec7b259801282a7b1e9`, e11
`378fe1b57514b9af3f017a72b4ca665910156cc7`, and e08 `9ae8e68`.
`ancestry-before.log` and `ancestry-precommit.log` preserve full SHAs, merge-base,
logs, diff statistics and status; the only untracked files before edits were
this unit's newly created evidence. `audit-ancestry.sh` checks that the final
history contains exactly that union plus single-parent commits scoped to this
unit. No other local branch or remote ref is modified.

No dependencies installed, shared environment changed, worktree created,
subagent spawned, remote write/push/PR/comment made, or campaign file edited.
The admission helper alone manages its authorized shared scheduling state.

## Actual first-build result and mandatory fixer handoff

The sole gated build exited **1** at initial source line 158 in
`insque_empty_links`. The diagnostic is `Unable to unify "0" with` the
unreduced conditional memory load beginning `if 0 =? 0 then ...`.
No resource-cap failure occurred. No second Astra build or repair was run.
The raw attempt is unchanged in `initial-attempt.v.txt`.

Rocq processed the following ten declarations before failing:
`insque_nwc`, `insque_welltyped`, `insque_preserves_callee_saved`,
`insque_exact`, `insque_ret_map`, `insque_return`, `insque_return_frame`,
`insque_halves`, `insque_lo`, and `insque_hi`. Their original proofs remain
in the `.v` file. **No successful full-target command or proof `.vo` exists**,
so this is not a certification of the assembled unit. The nine declarations
starting at `insque_empty_links` retain their exact statements but are
`Abort`ed in the handoff source; no later initial proof was tested. The
sanitized handoff has deliberately not been recompiled under the one-shot rule.

A new **gpt-6.1-sol, xhigh/default** fixer should restore the nine attempted
proofs from the snapshot, repair the first branch normalization error, and
check all later attempts. Preserve statements unless genuinely wrong and
explain every change. Finish byte-frame/link and typed witness checks, then
run a complete resource-gated target build and `check-assumptions.sh`.

Main-theorem Print Assumptions output is **unavailable** because compilation
failed before producing the module. `tools/print-assumptions.sh` was not run:
it would rebuild the failed target and violate the immediate handoff rule.
The generated map's own `Print Assumptions welltyped` did run during the full
build; its verbatim output is saved separately in
`generated-map-assumptions.txt` and reports only inherited
`FunctionalExtensionality.functional_extensionality_dep`. This is not a
transitive assumptions audit of `insque_exact` or any other new theorem.
Final proof producer: **not yet established**. All intended coverage beyond
the processed prefix remains unverified. No full-list sequence refinement,
termination, hardware or binary-lifting soundness is established.
