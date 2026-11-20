# a-ffs — PARTIAL: Astra one-shot handoff

Initial author: **gpt-6-astra**, xhigh; requested service tier default.
Final proof model: **none**. A NEW gpt-6.1-sol xhigh/default fixer is required.
No second Astra proof/build cycle was performed. Nothing was installed or published.

Branch: `llm-proofs/a-ffs`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-3b4b4f41`.
Allowed pre-unit forest: exactly origin base `49956416928e5b6bb3928b54ae33e3b81091f006`
through accepted e08 `9ae8e6800fa044797efd98372857e6ac89b18e1b`.
The prepared branch started clean at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`
with the expected sole parent. The remote collision query succeeded with no result.
Only the prepared branch was renamed and fast-forwarded. No unrelated unit history
was imported. Git metadata/network needed sandbox escalation; the initial failed
Git metadata command is logged and did not change the branch.

## Result and exact failure

The single full build waited for the shared resource gate, was admitted with
1,750,000 KiB hard virtual-memory cap, stack 65536 KiB, one compiler, `-j1` and
cache disabled, then returned **exit 1**:

```
File "./Examples/claude/arm8_ffs_proof.v", line 75, characters 21-23:
Error: Syntax error: '|' or ']' expected (in [or_and_intropattern]).
```

This is the intro pattern in `ffs_return_cut`, not a resource failure. The exact
unmodified author attempt is `initial-attempt.v.txt` (SHA256
`96ea8fe0ae907de546e74b0cb6bc50a57132b61dc2376b45107a293770660dea`).
`06-first-build.log` records the full command, gate messages, compiler stdout/stderr
and true exit. The only requested target was:

```
dune build --cache=disabled -j1 --display short Examples/claude/arm8_ffs_proof.vo
```

No successful full unit target exists. The build successfully compiled its core,
ARM8/common and canonical generated-lift dependencies. The compiler passed the
four prefix Qeds `ffs_nwc`, `ffs_welltyped`, `ffs_preserves_memory`, and
`ffs_preserves_callee_saved`, but no completed unit `.vo`/assumptions certificate
is claimed. All twelve subsequent proof bodies are now **Abort** in the active
file. Their exact initial proofs remain in the archive. All 16 theorem/lemma
statements are unchanged (`statements.json`, `statement-retention.txt`).
This packaging change was not rebuilt: no second attempt is allowed.

## Intended coverage and remaining obligations

The proposed `ffs_correct` contract uses the low32 of any typed X0 and matches the
32-bit least-set-bit specification in `amd64_ffs_proof.v`. Zero returns zero;
nonzero returns 1 plus the least set-bit index, between 1 and 32, zero extended
in X0. It has no positive-input, fixed-vector, upper32, path, overlap, CPU extension
or tunable restriction. SP, X30 and memory occur in the postcondition; separate
frames cover X19-X30, SP, model LR and Z8-Z15.

Unlike the ffsl template, actual ffs reads a 256-byte lookup table. Its explicit
hypothesis `ffs_table m` supplies `N.size i` at model address `0x24e738+i` for
all `i<256`. This is a pinned-data hypothesis, not an assumed output. The accepted
e08 reference bytes (ELF address `0x14e738`) have SHA256
`14a5d850c255623f9472e3c650abce0c78d32f0276b315b3a276a0462d97a1ac`.
`07-table-provenance.log` independently checks all 256 bytes against bit length;
this Python provenance check is not a Rocq proof.

The attempted mathematical isolation argument applies to every 32-bit bit pattern.
Execution then splits on all 33 possible result positions (zero plus 1..32), not
on a collection of input test vectors. Cut12 separates isolation from the actual
lookup/branch execution; cuts52/96 are the actual RET instructions. Proposed
`ffs_table_satisfiable`, `ffs_entry_satisfiable`, `ffs_spec_satisfiable` and
`ffs_return_guard_satisfiable` provide nonvacuity obligations. Proposed
`ffs_guarded_return` executes the actual RET under an external-address guard.
All of those proposals remain unchecked/aborted; no functional result is claimed.

Fixer must restore the archive, fix the syntax and finish the full proof, retaining
statements unless genuinely wrong with every statement change explained. Check
isolation, table witness/typing, cut12, finite-position symbolic execution and the
RET adapter. Obtain a full `.vo`, then run `print-assumptions.sh` here through the
same gate/cap. The script enumerates all 16 facts and invokes the required shared
`tools/print-assumptions.sh`. Main queries cannot run now: its prerequisite build
would constitute the prohibited second Astra attempt and the mains are aborted.

## Trust and audits

The generated lift printed the following transitive assumptions verbatim during
its successful dependency build (also `dependency-assumptions.txt`):

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the documented inherited e00 functional extensionality assumption.
It is NOT assumptions output for `ffs_correct` or the other unit facts. Their
transitive assumption audit remains pending, so no completion claim is made.
The source auditor against pinned origin passed with no new admissions, axioms or
parameters. Baseline admissions elsewhere are inventoried, not certified or used
as proof completion. The unit imports only Picinae_armv8, e11_ffs_arm8,
arm8_common and Stdlib arithmetic/list libraries.

Canonical `e11_ffs_arm8.v` and historical `ffs_arm8.v` are unchanged. Root Dune adds
only `Examples.claude.arm8_ffs_proof`; the generated target was already explicit.
The accepted ffsl proof was read only as a mathematical/style template, not imported.
Even eventual proof completion establishes sequential IL partial correctness,
not termination, accessibility/fault freedom, full binary/lifter soundness or
hardware refinement. The witness proposes all-read permissions but the public
partial-correctness contract relies on the read checks in executing IL traces.
