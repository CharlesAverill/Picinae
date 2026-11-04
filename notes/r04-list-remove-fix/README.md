# r04-list-remove-fix

Worktree: `/home/charles/.t3/worktrees/Picinae/t3-41a02797`.
Assigned local branch: `llm-proofs/r04-list-remove-fix`.
`author_model=gpt-6-astra` (original xhigh/priority author evidence preserved).
`final_proof_model=gpt-6.1-sol` (this fixer: xhigh/default).

## Scope and retained contract

The target is `Examples/FreeRTOS/armv6m_uxListRemove_proof.vo`, full kernel
checking, against the unchanged 18-instruction `uxListRemove_armv6m_prog`:
entry 0xa0, join 0xb2, BX 0xbc, index-equal fixup 0xbe/0xc0/0xc2.
The original ELF SHA256 and compiler/layout provenance are in the proof header
and unchanged accepted generated map. No source-level replacement was introduced.

All 16 original theorem/lemma statements, definitions and Ltac declarations
are retained. The seven originally completed proof bodies are verbatim.
`check-retention.py` mechanically removes comments/proof scripts and compares
the entire remaining source to the original `initial-attempt.v.txt`. The sole
added non-proof command is `Implicit Types (equal : bool).`: the original
singleton statement failed elaboration because an untyped binder used only
as an `if` condition does not determine an inductive type. This supplies the
intended Boolean type without changing that statement's text or hypotheses.
No statement was weakened, and no witness or hard branch was removed.

`list_remove_correct` proves `satisfies_all` on finite IL traces from entry.
`list_remove_at_bx` extracts the full original-memory postcondition, field and
byte effects and preserved-register frame at BX. `list_remove_return_step`
proves the ordinary modeled BX transition; `list_remove_returns` combines
that step with the functional effects and frame of the entry-to-BX trace.

Inputs are AAPCS32 R0=P and typed original memory containing P.next=N,
P.prev=B, P.container=L, L.count=C>0, L.index=I. C ranges over the entire
positive 32-bit field range (no natural-number cutoff). P/L are nonnull,
4-byte aligned, nonwrapping 20-byte objects, and N/B have nonnull, aligned,
nonwrapping 12-byte link prefixes. The original field separation matrix and
removed-item versus list/neighbor separations are unchanged. Neighbor aliases
and the singleton B=N=L+8 are allowed; there is no pairwise object-disjointness
requirement. Both I=P and I<>P paths are covered. Readable/writable hypotheses
are exactly the original access-word requirements, including conditional
index-word writing. SP is neither accessed nor required to be aligned.

The effects are N.prev=B, B.next=N, L.index=(if I=P then B else I),
P.container=0 and L.count=R0=C-1; R1=N, R2=0, R3=L. The exact final memory is
written in actual store order over original memory. P.value/owner/next/prev,
every byte outside the conditional four/five-word footprint, and every
separate untouched word are preserved. R4-R12, SP, LR, permissions and
temporaries are preserved; NZCV are caller-clobbered. The return requires odd
LR<0xfffffff0 and lands at LR & 0xfffffffe, preserving the modeled store.

`list_remove_entry_witness` constructs a typed store with readable/writable
permission maps, from arbitrary typed memory satisfying the original fields.
`list_remove_singleton_layout` and `list_remove_singleton_witness` establish
B=N=L+8, both index cases, arbitrary typed base memory and opaque bounded value
and owner. `list_remove_multi_layout` and `list_remove_multi_witness` establish
a distinct-neighbor entry with either index case. These are real Qed
nonvacuity/permission witnesses, not assumed callee contracts.

The other seven declarations are `list_remove_nwc`, `list_remove_welltyped`,
`list_remove_register_frame`, `rm_read_write`, `rm_read_frame`,
`list_remove_mem_frame` and `list_remove_mem_effects`.

## Repair details and validation

The exact Astra source was restored before repair. The entry proof now
normalizes addresses and uses the original finite slot separation to prove
the next/previous/index loads survive the preceding link writes. This proves
both branch cases at the join without substituting away all input parameters.
The suffix uses a separate unchanged-count load fact before applying the
32-bit modular decrement identity. Witness repairs fix malformed disjunction
patterns, use appropriate proofs for concrete <= bounds, replace uninferrable
Prop placeholders with exact field goals, and instantiate the generic witness
explicitly before its positive-count proof. No new helper contracts were added.

All commands/stdout/stderr/true exit codes are recorded with
`tools/record-command.sh`. Logs 02-12 retain the failed repair diagnostics;
13 is the first successful full-target build (exit 0). Log 18 checks the final
source including the final-producer comment. No skipped `.vos` checking.
Every Dune/Rocq/assumptions invocation uses `ulimit -v 2000000`,
`ulimit -s 65536`, `--cache=disabled -j1`, one compiler, through the read-only
shared `arm-validation/picinae-env` wrapper. No host installation or dependency
installation, new environment, or shared-toolchain mutation occurred.

Successful build command (13 and 18):

```
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short --no-buffer Examples/FreeRTOS/armv6m_uxListRemove_proof.vo'
```

## Ancestry and local-only boundary

Initial clean HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
sole parent pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
A successful empty read-only fork collision check preceded renaming only this
prepared branch. Sandboxed DNS and Git metadata failures, then successful
escalated read-only check and authorized rename/fast-forward, are recorded in
`setup-session.txt`; log 17 repeats the remote check successfully. The sole
import was `git merge --ff-only e74e54bdcc1b2f2cb15160c7b17417316bcac627`.
`allowed-checkpoint-commits.txt` records the exact 13-commit origin..checkpoint
set; `audit-ancestry.sh` rejects any other imported parents or non-unit paths.
No r01/r02/r03, fork, arm-validation, duneify, fix or ixb history was imported.
The original author evidence, shared plan/status/campaign, generated map,
ISA, r00 model and root Dune are unchanged from the authorized checkpoint.
The root module list already includes the exact target and its dependencies.
No branch other than this prepared branch was changed, and nothing was pushed,
published, commented on, or written remotely. No subagents were used.

## Limits

This completes the assigned local IL **partial-correctness** contract and
witnesses. It proves no termination or finite circular-list cardinality
refinement (r47), scheduler/IRQ/TCB property, hardware exception behavior, or
new lifter/binary soundness theorem. There are no additional CPU/tunable
hypotheses beyond the inherited sequential ARMv6-M IL model. Binary/lifting
provenance remains the inherited trusted boundary; no claim beyond it is made.

## Completed assumptions/source checks — DONE

The final-source full-target build (18) and all 16 transitive assumption
queries (21) exited **0**. Twelve declarations print exactly
`Closed under the global context`. The other four are `list_remove_correct`,
`list_remove_at_bx`, `list_remove_return_step`, and `list_remove_returns`.
Each prints the following **verbatim**, and no other assumption:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib functional-extensionality trust documented by
e00, not a claim that those four theorems are closed. The entire unmodified
`Check`/`Print Assumptions` stdout/stderr for every declaration is in
`21-assumptions.log`. No imported admitted proof appears transitively.
The assumptions command is recorded verbatim in that log; it calls
`tools/print-assumptions.sh` with `PROOF_MEMORY_KB=2000000` and
`PROOF_STACK_KB=65536` inside the same hard-capped shared environment.

The origin-based whole-source audit (16) and unit-only source audit (20)
exit **0**; whole-source NEW totals are `{}`, and unit totals are `{}`.
No remaining Abort, Admitted, admit, or new Axiom/Parameter exists in the
completed unit. Inherited unrelated baseline admissions are inventoried by
the whole-source auditor, and are absent from the selected transitive trust.
Final retention (19) and ancestry checks pass; generated IL/ISA/r00, root
Dune and archived author evidence are unchanged. Remaining limits are exactly
the scope exclusions above, with no unfinished assigned proof obligation.
