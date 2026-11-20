# a-memset-emag — PARTIAL Astra handoff

Initial author: **gpt-6-astra**, xhigh, default service tier requested by the
assignment (runtime tier is not independently observable here). Final proof
producer: **unset**. No second Astra proof/build cycle was run.

Branch: `llm-proofs/a-memset-emag`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-3c6c9c73`.
Assigned prerequisite: `9ae8e6800fa044797efd98372857e6ac89b18e1b`.
Pinned origin/merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.

The first full build exited **1**, at initial proof line 147:

```text
Error: The reference N.pow_pos_nonneg was not found in the current
environment.
```

This is a proof-script compatibility failure in the inhabited-input witness,
not a memory-cap failure. The candidate, exact commands, compiler stdout/stderr,
and real exit code are in `initial-attempt.v.txt` and `06-first-full-build.log`.
There is **no successful full target command** for the new proof module.
The source file now retains the four preceding Qed bodies and mechanically
replaces every later proof with Abort; the 22 theorem/lemma statements are
preserved exactly. The sanitized file was not rebuilt, as that would be a
second Astra cycle. The initial candidate remains the authoritative repair
input. `preserve-partial.py` records this mechanical transformation.

The compiler passed these four declarations before the failure:

- `memset_emag_nwc`: state-independent unchanged generated program map.
- `memset_emag_welltyped`: inherited e08 typing theorem.
- `memset_emag_preserves_callee_saved`: X19–X29, SP, X30, modeled full Z8–Z15.
- `memset_emag_preserves_result`: X0 is never assigned.

None has a newly completed proof-file .vo or transitive assumptions query.
They are not a completed unit certificate. All remaining proposed helpers,
the inhabited-input witness, return-step theorem and main theorem are
unverified; the build did not reach them.

## Contract and remaining proof work

`memset_emag_correct : memset_emag_contract` states `satisfies_all` for the
unchanged exact e08 scalar map, entry 0x19c300, all sizes and alignments.
The input state is typed, X0=d, X1=c, X2=n, d,n<2^64 and d+n<=2^64.
The postcondition writes low8(c) at each modular address d+i, i<n,
frames every other byte, returns X0=d and preserves the saved register list.
No source-buffer separation, alignment, ZVA/vector, CPU or tunable condition
is introduced. n=0 has no memory-access requirement. Memory in this model
is a total bitvector; staticMemory=False does not certify real allocation,
permission checking or fault behavior. The end d+n=2^64 is allowed.

Separate precondition, postcondition, exit and invariants are in the source.
Cuts cover byte replication, tiny-size decisions, medium ranges, the large
entry, loop and tail, and all six actual RET addresses. The loop tracks the
aligned cursor q, prefix max(16,q+16-d), and mathematical count d+n-q-81.
The tail records r<64 and X2=msub64 r 64. Overlapping scalar stores are tracked
with a set-of-filled-offsets predicate and an outside-byte frame.

`memset_emag_inputs_inhabited` proposes typed witnesses for **every** permitted
d,n and every in-range c,sp,lr, with zero initial memory. Its first attempt
failed; nonvacuity is not yet kernel checked. `memset_emag_ret_correct`
proposes the actual RET instruction's jump to X30. It was not reached.
All byte-replication, store-chain, branch, loop and tail proof scripts require
Sol validation and repair. Do not infer their success from the early error.
The initial symbolic-execution automation is an attempt, not a complete proof.
The theorem is partial correctness before RET, not a termination/existence or
hardware/binary-lifter refinement theorem. Such further claims remain absent.

The coordinator must create a **new gpt-6.1-sol xhigh/default fixer** using
this exact checkpoint. Keep statements unless genuinely wrong and explain
any correction. No subagent was created by this child.

## Build and assumptions evidence

The single actual build used:

```bash
bash tools/record-command.sh notes/a-memset-emag/06-first-full-build.log \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-memset-emag --memory-kib 3000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 3000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_memset_emag_proof.vo'
```

Admission succeeded, the cap was not raised, and there was one compiler at a
time. Core dependencies, `arm8_common.vo` and the unchanged e08 lift `.vo`
were built before the proof-file failure. No .vos or skipped proof checking.

`tools/print-assumptions.sh` was **not run** on the failed new module: it
would rebuild the failed target, violate the one-shot policy and cannot
print a nonexistent main theorem. Main theorem assumptions are unavailable.
The lift itself prints its existing typing theorem's assumptions during
compilation; the verbatim excerpt is `inherited-lift-assumptions.txt`:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the documented inherited e00 baseline dependency, **not** an
assumptions certificate for the unproved functional theorem. No admitted
AMD64 proof is imported. Pure memory helper scripts were adapted to ARM8
instead. Source audits (including the required whole-repository base audit)
exit 0 with no new suspicious tokens. Baseline admissions remain outside
this unit. A lexical audit cannot certify the unbuilt transitive theorem.

## Provenance, ancestry and local-only boundary

Initial HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`
with sole parent the pinned origin, and the initial worktree was clean.
The first sandboxed remote check failed DNS; the escalated read-only check
succeeded with no branch match (`00-remote-branch-check.log`). Only the prepared
branch was renamed. The first ff-only command hit read-only Git metadata;
the explicitly authorized retry fast-forwarded to the exact assigned e08.
No unexpected history was imported; `ancestry-audit.sh` checks the five
accepted prerequisite commits and only scoped unit commits above them.

The generated lift is unchanged, SHA256:
`d88c12780e15542ee4a78674e9621deab12a58e415382ee50914b116b8cec8a8`.
The only Dune change adds `Examples.claude.arm8_memset_emag_proof` to the
explicit module list; its dependencies were already selected by e08.

No dependency was installed, no shared environment modified, no other
process touched, no other branch changed, and no push, PR, comment or other
remote write was performed. Final commit/status evidence accompanies the
handoff; original author branches are unchanged.
