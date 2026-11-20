# x03 AVX forward overlap: PARTIAL handoff

**State: PARTIAL. The only full-target build failed, exit 1.**
No second Astra build or repair cycle was performed. A new gpt-6.1-sol
xhigh/priority fixer is required; the coordinator must start it. Preserve
all initial statements unless genuinely wrong and explain any change.
Final proof producer: **none**. No complete overlap theorem is certified.

Initial author: **gpt-6-astra, xhigh/priority**. Final proof producer is not
assigned unless this initial attempt passes. No fixer was delegated here.

Branch: `llm-proofs/x03-avx-overlap-forward`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-5046f507`.
Allowed ancestry: pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`,
then e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, then this unit only.
The prepared HEAD was already e00, with exactly that sole parent. No merge
was needed. Initial status was clean before the first evidence file was
created (`00-before.log` consequently shows the new notes directory).
The initial sandboxed `ls-remote` failed to resolve github.com; a read-only
escalated query succeeded with no result. The initial sandboxed branch
rename failed because the shared Git administrative directory was read-only;
`01-branch.log` records the successful recheck and authorized rename of only
the prepared branch. No other branch was changed.

## Specification and attempt

The exact initial statements and proof text are frozen in
`initial-attempt.v.txt`. The authored module is
`Examples/claude/amd64_memmove_avx_overlap_forward_proof.v`.

Main statements:

- `memmove_avx_correct_overlap_forward`: entry 0, ordinary forward-loop
  invariant partial correctness, with RET cut at normalized address 493.
- `memmove_avx_overlap_forward_at_ret`: original-memory `copied` relation
  (all n destination bytes and every outside-destination byte), RAX=d,
  RSP unchanged before RET, and RBX/RBP/R12–R15 unchanged.
- `ofw_entry_satisfiable` and `ofw_critical_distances`: typed ABI/memory
  witnesses for every gap 1..511 at n=512, specifically including
  distances 1,31,32,127. These are entry witnesses, not termination proofs.

Scope is `256<n<2^63`, `d<s<d+n`, `s+n<=2^64`, and n no larger than both
entry-memory thresholds at 0x31a3f8 (REP) and 0x3215a8 (NT). Destination
nonwrap follows from source nonwrap and d<s. No nonoverlap premise, no
minimum gap, no d>=128 or other low-address restriction. The explicit
signed object-size ceiling supports the actual sign-change dispatch guard;
no all-size/all-tunable claim is made. The mask alone is not the dispatch.
Offsets 337–357 combine the 4 KiB mask with the high bit of
`((d-s+n) mod 2^64) xor ((d-s) mod 2^64)`. The proposed `ofw_dispatch`
lemma proves this high bit equals 1 under the stated bounds.

`ofw_load` uses the copy-set frame and source nonwrap to show that offsets
at or beyond k still read original memory. `ofw_store4` reads all four
vectors from the pre-row memory, then uses the existing original-memory
`cpy_store` for the four writes. The invariant retains the original head
YMM0 and tail YMM5–8; the final overlapping tail and saved head are included
in the entry-to-RET attempt. It never asserts that the whole source region
remains unchanged after writes.

Only five new explicit Dune modules were selected: the target, unchanged
lift, baseline small AVX proof, memcpy sets, and memcpy lemmas. No baseline
loop, REP or admitted NT proof is imported. General arithmetic/tactic
scaffolding is attributed to the baseline Claude Opus 5.5 loop proof.

## Validation policy and evidence

Exactly one full-target build is permitted for the Astra author:

```sh
bash tools/record-command.sh notes/x03-avx-overlap-forward/04-full-vo-build.log \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 6000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_overlap_forward_proof.vo'
```

The checked-in recorder log contains the exact command, compiler output
and true exit code. The read-only shared isolated toolchain was reused;
no dependencies were installed, no shared environment was changed, and no
proof compilers were run concurrently within this unit. Dune is in full
`vo` mode. Standard empty `.vos` side files emitted by full Rocq compilation
are not skipped-proof builds.

`02-source-audit-initial.log`: target audit exit 0, no new forbidden tokens.
`03-lift-unchanged.log`: generated lift diff exit 0 against pinned origin.
`05-source-audit-all.log`: repository-wide source audit exit 0; baseline and
current totals both 7 Admitted, 1 admit, 89 interface Parameters; NEW is {}.
Those inherited admissions are not selected by this dependency closure.
A lexical source audit is not a transitive assumptions certificate.

Inherited baseline assumption documented by e00:
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`.
The raw baseline declaration and its provenance are in
`../e00-build/logs/15-extensionality-provenance.log`. This must not be
reported as a fresh successful assumptions audit of this unit.

Boundary: sequential partial correctness of unchanged lifted IL. No
termination, executed RET/caller continuation, ISA availability, faults,
cache/timing/concurrency, or binary/lifter soundness result. No provenance
upgrade is inferred from the source hash or a typing proof. The inherited
binary identity is Ubuntu amd64 glibc 2.35-0ubuntu3.12, SHA256
9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9;
Ghidra symbol address 0x2a0840, image base 0x100000, normalized entry 0.

No pushes, PRs, remote comments/writes, shared campaign edits, or subagents.

## Exact failure and retained artifacts

`04-full-vo-build.log` ends verbatim:

```text
File "./Examples/claude/amd64_memmove_avx_overlap_forward_proof.v", line 264, characters 17-81:
Error: Tactic failure:  Cannot find witness.


EXIT_CODE=1
```

The error occurs inside the initial `ofw_dispatch` proof, in the `ADD`
assertion's replacement of `2^64+d-s+n` by `d+n-s+1*2^64`. This is only the
reported location, not a tested fix or diagnosis of subsequent goals.
Rocq processed preceding Qed declarations, including `ofw_load` and
`ofw_store4`, but no full unit `.vo` exists and these helpers have not been
separately assumptions-audited. Their checked proof text remains unchanged.
The existing selected lift, `amd64_common`, copy sets/lemmas, and baseline
small AVX proof each produced full `.vo` files within this one Dune command.
There is **no successful unit target command**.

The seven unchecked declarations (dispatch, heuristic, both main theorems,
threshold witness, general entry witness, named-distance witness) now end
in `Abort`. `06-preserve-handoff.log` records a text-level assertion that
**every statement is exactly unchanged**, and that only unchecked proof
bodies were removed from the active source. All initial proof bodies are
preserved verbatim in `initial-attempt.v.txt`. This conversion is handoff
packaging, not a second proof attempt. The Abort-packaged source was not
rebuilt, as required by the one-shot policy.

**Print Assumptions output: unavailable for this unit.** The failed target
exports no module from which to query the main theorems. Running
`tools/print-assumptions.sh` would start another build, which is prohibited
after the first Astra failure. Therefore no fresh raw assumptions output or
transitive assumption certificate is claimed. e00's inherited functional
extensionality evidence is recorded above, not substituted for a unit audit.
The Sol completion must use that helper (PROOF_MEMORY_KB=6000000,
PROOF_STACK_KB=65536), query both mains plus all frame/helper/witness facts,
and reject any transitive admitted dependency.

Remaining gaps: dispatch proof, all downstream symbolic entry/loop/tail
proof obligations, both RET and entry-witness proofs, a successful full
unit target, and all unit transitive assumptions queries. No termination or
expanded binary-soundness result is requested or implied.

Final local commit and clean ancestry evidence are recorded outside the
checkout (to avoid making the just-committed tree dirty) under the authorized
unit evidence directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x03-avx-overlap-forward/`,
files `astra-t3-5046f507-commit.log` and `astra-t3-5046f507-final-ancestry.log`.
The latter runs the checked-in `audit-after-commit.sh` and verifies clean
status, the exact base/prerequisite/branch, unchanged lift, and full history.
