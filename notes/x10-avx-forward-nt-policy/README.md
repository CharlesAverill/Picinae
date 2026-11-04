# x10-avx-forward-nt-policy

**Status: PARTIAL — first full build failed; handoff to a NEW Sol fixer required.**
Initial author: gpt-6-astra, xhigh/default as assigned. Final proof producer:
none. No Astra repair cycle or second Dune/Rocq run was performed.

Assigned branch: `llm-proofs/x10-avx-forward-nt-policy`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-df03b650`.

## Statements and intended coverage

`memmove_avx_correct_forward_nt_policy` states `satisfies_all` from actual
normalized entry 0 on the unchanged `memmove_avx_amd64` program.
`memmove_avx_forward_nt_policy_at_ret` extracts the original-memory byte copy,
unchanged bytes outside destination, RAX=d, RSP=rsp before RET 493, and
preservation of RBX/RBP/R12-R15 for an execution reaching that cut.

Domain: typed System V AMD64 entry RDI=d, RSI=s, RDX=n, RSP=rsp, memory m;
256<n<2^63, d<s<d+n, s+n<=2^64, n<=m[0x31a3f8], m[0x3215a8]<n. The reads
are little-endian quadwords in starting memory. Destination nonwrap follows.
No extra gap, threshold, CPU-bit, DF, data/tunable separation or result
restriction is imposed. n=REP is included. n>REP remains x07.

Actual dispatch: 192/199 skips REP; 309/318 skips backward copying;
324/331 selects 813; 813 negates d-s into s-d, and 816/819 takes the
forward fallback to 363 because s-d<n. The NT-store entry at 825 is
unreachable in this domain. The 363 preparation and 416 loop reuse x03's
original-memory load/store helpers and saved head/tail values. x02's
nonoverlap theorem is never applied to overlapping inputs.

`ofnt_path`, `ofnt_postcondition`, `ofnt_frame`, `ofnt_exit`, and `ofnt_invs`
separate the domain, results, ABI frame, exit cut and invariants.
`ofnt_entry_satisfiable` and `ofnt_critical_distances` propose typed entry
witnesses for n=512, REP=512, NT=511 and every gap 1..511, including
1/31/32/127. These are entry witnesses, not termination witnesses.
No new callee/helper contract is assumed.

The target remains inherited Ubuntu amd64 glibc 2.35-0ubuntu3.12 libc.so.6,
SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
Ghidra address 0x2a0840, image base 0x100000, Ghidra 11.4.2/pcode2coq.
No new binary/lifter validation is claimed. Even a successful proof is
sequential IL partial correctness, not termination, execution of RET,
caller continuation, hardware availability, faults, cache/timing or
concurrency correctness.

## History and environment

Prepared HEAD was exactly e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9,
whose sole parent is pinned origin 49956416928e5b6bb3928b54ae33e3b81091f006.
The initial working tree was clean (before creating unit evidence).
The read-only remote branch-name collision check succeeded with no output
before renaming only the prepared `t3/avx-forward-nt-policy` branch.
The first sandbox network attempt failed with DNS resolution; the authorized
network retry is recorded in `branch-collision.log`.
Git metadata writes also required sandbox escalation; the first unprivileged
rename/import attempt failed without changing history.

Fast-forwarded to exactly 14ea393f2227bc8bde692b1e70badc61dce80304, then merged
only cfb65c6f988088e4d1912544a03279d7cb29a681. The only conflict was root
Dune's explicit module list, resolved by preserving the union. Integration
commit c6db0703be2cdcc9966cfa96bcf1cdd5d96f07b7 has those exact two parents.
Original author branches are unchanged. Allowed prerequisite ancestors are
e00, x03 author/fixer, x02 author/fixer, as recorded by `audit-ancestry.py`.
Both reviewed proof files and the generated map are byte-identical to their
assigned heads/base (`prerequisite-preservation.log`). The x02 forest remains
available but its costly NT theorem is not a dependency of the x10 target.

No installations, shared environment changes, other-unit process changes,
subdelegation, publication, remote writes or shared plan edits occurred.
The shared isolated environment is used read-only. Every compiler is gated
by the assigned resource helper, 4000000 KiB memory, 65536 KiB stack,
Dune --cache=disabled -j1, full vo mode and one compiler at a time.

## Evidence

- `initial-attempt.v.txt`: exact source submitted for the one-shot build.
- `write-initial.py`: adaptation script used before the first build.
- `first-full-build.log`: exact gated command, stdout/stderr and true exit.
- `build.sh`: exact relevant full .vo target with explicit resource limits.
- `source-audit-initial.log`: scoped audit, no new or current forbidden tokens.
- `source-audit-all.log`: required whole-repository audit against pinned base,
  exit 0, NEW totals {}. Baseline unrelated admissions remain outside scope.
- `ancestry-before.log`, `import-x03.log`, `import-x02.log`,
  `ancestry-integrated.log`: exact history and import evidence.
- `check-assumptions.sh`: prepared command for every main/helper/witness;
  may run only after a successful initial full target build.

The accepted x03 prerequisite reports inherited
FunctionalExtensionality.functional_extensionality_dep for its main and
welltyped theorems; other helper/frame/witness queries are closed. This
inherited evidence is preserved in notes/x03-avx-overlap-forward-fix; it
cannot substitute for fresh transitive Print Assumptions on x10.

## One-shot result and required handoff

`first-full-build.log` has the complete raw compiler stdout/stderr and exit
**1**, including admission wait/admission/release. The full dependency closure,
including `amd64_memmove_avx_overlap_forward_proof.vo`, compiled under the
assigned 4000000 KiB cap. The new target did not complete. Its diagnostic is:

```text
File "./Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.v", line 98, characters 2-58:
Error: Found no subterm matching
"(?M1547 + msub ?M1546 ?M1548 ?M1547) mod 2 ^ ?M1546" in the current goal.
```

This is a rewrite failure in `ofnt_negative_gap`, not a memory-cap failure.
No repair was attempted. `preserve-handoff.py` leaves the four preceding
compiler-accepted Qed bodies (`ofnt_welltyped`, `ofnt_nwc`,
`ofnt_preserves_callee_saved`, `ofnt_reverse_gap`) and changes that failed
helper plus the two mains and three later witness proofs to `Abort`.
Every theorem/lemma/corollary statement and all definitions remain exactly
as in the initial attempt; the check is recorded in `preserve-handoff.log`.
The complete attempted proof bodies remain in `initial-attempt.v.txt`.
The resulting partial source was deliberately NOT rebuilt after failure;
there is no successful x10 full-target command or x10 `.vo` certificate.

**Fresh x10 Print Assumptions output: unavailable.** The helper invokes Dune
before its query; running it after this failed attempt would be a second
Astra build. Therefore it was not invoked. No axiom-freedom or functional
correctness claim is made for the unfinished mains. Four prefix proof
commands were accepted before the failure, but this is not a completed
module certificate or a fresh transitive assumptions audit. The existing
x03 certificate reports inherited dependent functional extensionality:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

That quoted prerequisite output is not an x10 assumptions result.

The coordinator must launch a NEW gpt-6.1-sol xhigh/default fixer if continuing.
Restore the initial proof archive, keep statements unless genuinely wrong,
explain every statement change, repair and validate the helper, both actual
execution mains and witnesses. Then run the exact full target and the prepared
assumptions script through the same resource gate/cap. In particular, the
actual 309/813 dispatch, 363/416 loop composition, RET corollary and witness
proof scripts were not reached by the failed compiler and remain unverified.
No NOV premise, arbitrary gap/threshold restriction or assumed result may be
introduced to avoid those obligations.

Final commit and clean-history audit are recorded externally under
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x10-avx-forward-nt-policy/`
to avoid a self-referential commit hash in tracked evidence.
