# a-div: completed IL proof

Branch: `llm-proofs/a-div`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-bca255ed`.
Status: **done for the assigned partial-correctness IL proof**. No binary
validation or termination result is claimed. Publication is not authorized;
no push, PR, remote comment or other remote write was performed.

## Scope

`Examples/claude/arm8_div_proof.v` proves `div_correct`: for a typed AArch64
entry store at address 0, W0/W1 interpreted as signed 32-bit integers n/d,
with d nonzero and excluding only INT_MIN / -1, every execution considered
by `satisfies_all` has the specified invariant at RET offset 24. X0's low
32 bits are `Z.quot n d`, its high 32 bits are `Z.rem n d`, and the decoded
fields satisfy quotient*d + remainder = n. Upper halves of the input X
registers are unrestricted within the 64-bit model. No memory pointers,
size limits, overlap conditions, CPU-feature or tunable assumptions occur.
This is an invariant/partial-correctness theorem at RET, not termination.

`div_preserves_memory` preserves V_MEM64 on all execution endpoints.
`div_preserves_callee_saved` preserves X19-X29, X30, SP and the full modeled
SIMD Z8-Z15 registers on all execution endpoints (stronger than the ABI's
low-64-bit preservation requirement for SIMD callee-saved registers).
`div_nwc` proves state-independent code, and `div_welltyped` proves typing.
`div_packed_hi` checks the actual BFXIL/BFM packing. `div_inputs_satisfiable`
constructs a typed store for every pair of signed 32-bit inputs, so entry
conditions do not assume an answer or an unproved callee contract. There
are no callees or newly assumed helper contracts.

The small `div_arith.v` contains the architecture-neutral `quot_range` and
`rem_range` lemmas from `amd64_common.v`, with attribution. It imports only
Stdlib ZArith/Lia. No existing proof or shared helper was edited; the ARM
proof imports no AMD64 logic. Root Dune selects only these three new target
modules in addition to e00's existing explicit list.

The target provenance is inherited: AArch64 Ubuntu glibc 2.35-0ubuntu3.15,
`/lib/aarch64-linux-gnu/libc.so.6`, SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`, symbol
at Ghidra address 0x13d840, image base 0x100000, rebased entry zero,
Ghidra 11.4.2 + pcode2coq. The independent e02 binary check is not imported
or represented as completed here. `lift-unchanged.log` verifies the generated
`div_arm8.v` is byte-for-byte unchanged from the pinned origin base.

## Validation

All compiler/build/query processes used the existing read-only environment
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`,
`ulimit -v 3000000`, `ulimit -s 65536`, `--cache=disabled -j1`.
No dependency installation or shared-environment modification was needed.
No concurrent proof compilers were run in this unit.

The final full `.vo` build is `build-10.log`, exit 0:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 3000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_div_proof.vo'
```

The initial build compiled the full required core closure locally with the
cache disabled. Earlier logs preserve real diagnostic failures and their
exit codes. In particular build-02's successful compilation contained an
Aborted exploratory main theorem; it is NOT completion evidence. Build-06
first checked the completed main theorem, and build-09 also checks the
expanded SIMD frame and general typed-input witness. Build-10 rechecks after
removing a trailing blank line in the pure helper. The final sources
contain no Abort, Admitted, admit, Axiom, or Parameter declarations.

`assumptions.log` records the exact `tools/print-assumptions.sh` invocation
and verbatim output for all seven exported ARM proof facts. The sole
transitive assumption, for `div_correct` and `div_welltyped`, is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib functional-extensionality assumption documented
by e00, not an admitted proof introduced or imported by this unit. The
memory and register frame theorems, `div_nwc`, `div_packed_hi`, and
`div_inputs_satisfiable` each report verbatim:

```text
Closed under the global context
```

`arithmetic-assumptions.log` reports the same closed status for both pure
arithmetic helpers. All assumptions queries exit 0 and explicitly set
`PROOF_MEMORY_KB=3000000`, `PROOF_STACK_KB=65536`.

`source-audit.log` runs the required repository-wide audit against
`49956416928e5b6bb3928b54ae33e3b81091f006`, exit 0, `NEW totals: {}`.
Unrelated baseline admissions remain inventoried; none occurs in this
proof's transitive assumptions. `unit-source-audit.log` additionally checks
the lift, proof and arithmetic helper: baseline/current/new totals all `{}`.
The lexical result is supplemented by the transitive assumptions above.

## Ancestry and local operations

Initial direct inspection before creating the notes directory returned an
empty `git status --short`, HEAD
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, and sole parent
`49956416928e5b6bb3928b54ae33e3b81091f006`. No merge/import was necessary.
`ancestry-before.log` repeats the audit after creating its log, hence it
shows only the newly untracked unit notes. The application renamed the new
prepared branch from `t3/bca255ed` to `t3/arm8-div-proof` during startup;
HEAD/history stayed at the exact prerequisite. No other branch was changed.

The first sandboxed `ls-remote` failed DNS (exit 128); the escalated read-only
retry succeeded with no match. The sandboxed rename failed due to the
read-only shared Git metadata (exit 128). `branch.log` records a successful
repeat of the collision check immediately followed by the authorized rename
of the prepared branch to `llm-proofs/a-div`. No fork branch was a base.

`ancestry-after-implementation.log` records merge-base, allowed log and diff
stats before committing. Final clean status, full local commit and ancestry
are recorded after commit in the permitted external unit directory
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-div/` (so recording
the commit hash does not itself dirty the committed tree). Only e00 plus
this unit's local commit may appear above the pinned origin base.

Remaining limitations: inherited unvalidated lifting/binary provenance;
partial correctness at RET rather than termination; the documented inherited
functional-extensionality assumption. No unfinished proof obligation remains
in the assigned IL scope.

The first commit attempt stopped at `git diff --cached --check` (exit 2):
a redundant final blank line in the helper was removed. Rocq prints trailing
spaces on some wrapped type lines; assumptions logs retain them verbatim.
The final whitespace check therefore covers source/build files, not raw logs.
