# a-ldiv: complete IL partial-correctness proof

Branch: `llm-proofs/a-ldiv`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-82be9105`.
Status: **done for the assigned existing-lift IL proof**, not binary validation
or termination. No remote writes, dependency installations, shared-environment
changes, subagents, or edits to the separate div unit.

## Scope

`Examples/claude/arm8_ldiv_proof.v` imports only the ARM theory and unchanged
`ldiv_arm8.v`. Root Dune adds exactly these two modules to e00's explicit list.
The arithmetic specification and two pure range helpers are ported locally
from the AMD64 proof/common file, without importing AMD64 program logic.

The inherited target is `/lib/aarch64-linux-gnu/libc.so.6`, Ubuntu AArch64 glibc
2.35-0ubuntu3.15, SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`, symbol
`ldiv` at `0x13d860`, entry rebased to zero, Ghidra 11.4.2 + pcode2coq.
Independent binary/lift revalidation belongs to e02. This unit does not certify
that inherited provenance or any alias such as lldiv/imaxdiv.

`ldiv_correct` proves `satisfies_all` from entry 0 to RET offset 12.
For a modeled AArch64 store, X0/X1 encode signed 64-bit n/d; require d != 0 and
exclude n = -2^63 with d = -1. There are no additional restrictions on n/d,
buffers, sizes, overlap, CPU features, tunables, stack pointers, or return
addresses beyond the modeled register widths. X0/X1 decode to `Z.quot n d` and
`Z.rem n d`. SP and X30 retain their entry values. The SDIV zero branch is
excluded using the genuine d != 0 precondition, not an assumed result.

`ldiv_return` and `ldiv_return_step` analyze the actual lifted RET: jump to X30,
with the architectural store exactly updated at PC. `ldiv_returns_correct`
combines the functional result and RET with memory and callee-saved frames.
It assumes a valid trace from entry reaching the first RET and one actual RET
step; these are execution premises of partial correctness, not termination or
an assumed arithmetic answer. It proves the target, signed quotient/remainder,
quotient*d+remainder=n, unchanged memory and saved registers after the RET.
`ldiv_identity` also exports the division identity separately.

`ldiv_preserves_memory` preserves the entire V_MEM64 store along any execution.
`ldiv_preserves_callee_saved` preserves X19-X29, SP, X30, and all modeled bits of
SIMD Z8-Z15 (stronger than only their ABI-preserved low portions). These frame
lemmas cover all traces, including RET. `ldiv_nwc` proves code independent of
the store; `ldiv_welltyped` proves lift typing. `ldiv_inputs_satisfiable`
constructs a modeled input store for every signed 64-bit pair; the concrete
7/3 witness `ldiv_defined_example` satisfies the exclusions. No callee or other
unproved helper contract is introduced.

## Validation

All compiler/build/query commands ran through the read-only isolated wrapper
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`.
Every such command used `ulimit -v 3000000`, stack 65536 KB, Dune `-j1`, disabled
Dune cache, and full `.vo` mode. No proof compilers ran concurrently in this unit.

Successful final target command (exit 0), recorded verbatim with stdout/stderr
in `build-06.log`:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 3000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_ldiv_proof.vo'
```

`build-01.log` records the initial full dependency build and an intentionally
aborted exploratory theorem; it is NOT evidence of completed correctness.
`build-02.log` through `build-05.log` preserve actual intermediate errors and
exit 1 statuses (scope annotation, reset_temps statement, lemma name, trace
start simplification). `build-06.log` checks the completed file, all Qed.

`assumptions.log` records the exact `tools/print-assumptions.sh` invocation,
with `PROOF_MEMORY_KB=3000000 PROOF_STACK_KB=65536`, and raw Check/Print Assumptions
output for all main, return, frame, typing, input, and range theorems. Exit 0.
The complete assumption output for `ldiv_correct`, `ldiv_returns_correct`,
`ldiv_return`, `ldiv_return_step`, and `ldiv_welltyped` is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the existing Stdlib assumption documented by e00, not a new axiom.
All other queried theorems, including both frame theorems and the arithmetic
identity, print verbatim `Closed under the global context`. There are no
transitive admitted proof dependencies in these theorem assumptions.

`source-audit.log` records the required repository-wide audit against
`49956416928e5b6bb3928b54ae33e3b81091f006`: exit 0, `NEW totals: {}`; unrelated
baseline admissions remain inventoried and unchanged. `unit-source-audit.log`
restricts the same audit to the lift and proof: exit 0, baseline/current/new
forbidden-token totals all empty.

## Ancestry and local publication boundary

Initial status was clean, HEAD was the reviewed prerequisite
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, its sole parent and the merge-base with
origin/llm_generated_proofs was
`49956416928e5b6bb3928b54ae33e3b81091f006`. No import/merge was necessary.
`ancestry-before.log` records the prerequisite history and baseline diff; its
untracked notes entry is the recorder's own newly created evidence directory.

The first sandboxed network check failed DNS resolution; the read-only retry
succeeded with no branch match (`branch-collision.log`, exit 0). Renaming the
prepared local branch needed access to Git metadata outside the sandbox and
succeeded on the authorized retry. No other branch was modified.

Only e00 and this unit's own commits are permitted above the pinned origin.
`ancestry-after.log` records the implementation commit, its diff stat, and a
clean status before adding that audit record. A final audit after the evidence
commit is also returned to the coordinator. No push, PR, or remote comment.
