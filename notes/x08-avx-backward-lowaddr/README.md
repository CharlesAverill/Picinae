# x08 AVX backward low-address proof

State: **PARTIAL — first Astra full build failed; new Sol fixer required.**

Initial author: OpenAI gpt-6-astra, xhigh; assigned service tier default.
Final proof producer: not certified.
Branch: `llm-proofs/x08-avx-backward-lowaddr`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-b39074c1`.

## Scope and statements

The intended main theorem is `memmove_avx_correct_backward_lowaddr`, on
exactly `low_domain d s n`: `256<n`, `s<d<s+n`, `0<d<128`,
`d+n<=2^64`, `s+n<=2^64`, plus typed entry and the actual AMD64 argument
registers/memory/trace-start hypotheses. There is no additional alignment,
minimum gap, upper size limit, CPU, DF, threshold, or policy restriction.
All possible gaps at these addresses are `1<=d-s<=d<128`.

`memmove_avx_backward_lowaddr_at_ret` is intended to extract original-source
byte copying, the outside-destination memory frame, RAX=d, unchanged RSP
and RBX/RBP/R12-R15 from an actual exec_prog prefix ending at RET 623.
`memmove_avx_backward_lowaddr_after_ret` additionally describes a trace
executing RET: RSP increments by eight modulo 2^64 and the jump target is
the **final** memory's stack quadword. There is deliberately no assumption
that destination is disjoint from the return-address slot, so preservation
of the original caller return address is not promised.

The cursor invariant has two cases. `low_live` retains x04's copied suffix,
original saved head/tail vectors and the unread-source consequence.
`low_wrapped` retains RCX=c, RDI=d, c<2^64 and d<c mod 128. The decrement
preserves this residue, which excludes the unsigned exit test. It imposes
no memory claim on this nonreturning case. Example d=1,s=0,n=289 starts
at c=160, proceeds to c=32, then wraps to 2^64-96. Conversely
n=257,d=1 starts at c=128 and reaches c=0 after its first body.
No totality, fault freedom, or safe framing of arbitrary nonreturning
prefixes is claimed. This distinction is necessary for the unchanged IL.

The witness statements use finite **nonzero** read and write permission
masks covering addresses below 4194304, including source, destination,
threshold and return-stack bytes, and an actual entry NOP transition.
They are not witnesses of a whole terminating execution. There are no
new callee contracts. The provenance and physical-CPU boundaries remain
inherited from x04, rather than independently validated binary semantics.

## One-shot policy and evidence

`initial-attempt.v.txt` preserves the complete initial declarations and
proof scripts. `initial-full-build.log` records the one full `.vo` command,
compiler stdout/stderr and real exit status. Admission waits are separate
from compiler attempts. There is no second Astra repair cycle.

The command uses the mandatory resource helper, the shared environment
read-only, `ulimit -v 4000000`, stack 65536, `--cache=disabled -j1`, and
only `Examples/claude/amd64_memmove_avx_backward_lowaddr_proof.vo`.
The explicit root module list adds only this target to x04's closure.
No dependencies were installed; no shared environment or other process
was changed. No publication or other remote writes were performed.

## Ancestry

Prepared HEAD was clean at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
The fork collision check initially failed because sandbox DNS was blocked;
its authorized network retry succeeded with no result. The exact assigned
prerequisite `48d4aa84b986150a8f4b4b12d50d92c67f2545ee` was then imported
with `git merge --ff-only`; only the prepared local branch was renamed.
The initial sandbox merge failure was a read-only git metadata error,
resolved by the authorized retry. All failure and success logs are retained.

The five accepted pre-unit commits above origin are e00 and x04's initial
partial/evidence/fix/evidence chain. The ancestry checker permits only that
exact union and scoped unit commits. It records merge-base, the complete
origin..HEAD log, diff stat and status. No other branches were changed.
The generated map and accepted x04 proof have an empty protected-source diff.

## Trust boundary

The accepted prerequisite's original raw certificate remains at
`notes/x04-avx-overlap-backward-fix/14-assumptions.log` (23 queries,
18 closed and five with inherited Stdlib functional extensionality).
Its main theorem certificate says, verbatim:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is inherited evidence, **not** a new x08 assumptions certificate.
The new main theorem needs its own full target and Print Assumptions before
any completion claim. Lexical source audit alone cannot certify that result.

## Final result and exact handoff

The sole full target build returned **exit 1**, after successful admission
at 4000000 KiB. All prerequisites, including the unchanged accepted x04,
built successfully. There was no cap failure. The new target failed in
`memmove_avx_correct_backward_lowaddr`, initial-attempt line 203, while
establishing the saved-head-vector component of the loop invariant:

```
Unable to unify "m Ⓨ[ s ⊕ 32 ]" with
 "(s1[...][R_YMM5 := m Ⓨ[ 32 + s ]][...]) R_YMM5".
```

The full diagnostic, context, commands and true exit are retained in
`initial-full-build.log`; the excerpt above elides only the update chain.
No second Astra proof attempt, build or assumptions compiler was run.
The failed proof and every later unchecked proof are now **Abort**, while
the complete original scripts remain byte-for-byte in `initial-attempt.v.txt`.
All 26 original declarations (19 result statements and seven definitions)
are retained; the declaration audit checks their bodies/statements, not
just their names. No statement was weakened or otherwise changed.

Eleven proof scripts completed before the failure:

- `memmove_avx_backward_lowaddr_nwc`
- `memmove_avx_backward_lowaddr_welltyped`
- `memmove_avx_backward_lowaddr_preserves_callee_saved`
- `low_domain_all_gaps`
- `low_initial_memory`
- `low_rcx_c0`
- `low_cursor_nowrap`
- `low_cursor_wrap`
- `low_cursor_residue`
- `low_wrapped_no_exit`
- `low_live_unread`

These are retained completed helpers, **not a successful full module
certificate**. No new x08 full `.vo` target succeeded. The main invariant
proof, at-RET/after-RET functional and frame results, RET-step helper and
permission/state witnesses remain unproved. In particular, the witness
attempts have not yet passed a compiler and no accessible whole execution
is certified. The final Abort-only handoff layout was not rebuilt, as that
would be another Astra build after the first failure.

`tools/print-assumptions.sh` was not run on x08: the main constants do not
exist after Abort, and that helper would rebuild the failed target. There
is **no new raw x08 assumptions output**. Inherited x04 evidence, including
its functional-extensionality assumption, is identified above; it cannot
stand in for the missing x08 certificate. The fixer must restore the
initial scripts, complete all eight unfinished results and witnesses,
run the full target under the same resource gate/cap, and query all main
theorems and helpers with `tools/print-assumptions.sh` using
`PROOF_MEMORY_KB=4000000 PROOF_STACK_KB=65536`. Any genuine statement
correction requires an explicit explanation; otherwise retain all statements.

No final proof model is claimed. A new coordinator-launched
`gpt-6.1-sol`, xhigh/default, is required; this child did not delegate it.
