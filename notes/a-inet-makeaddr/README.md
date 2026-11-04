# a-inet-makeaddr — PARTIAL Astra handoff

Initial author: OpenAI `gpt-6-astra`, xhigh/priority. Final proof producer:
**none**. This author did not complete the functional theorem. A NEW
`gpt-6.1-sol`, xhigh/priority fixer is required; no child was delegated.

Branch: `llm-proofs/a-inet-makeaddr`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-f64bb1b4`.
The only full proof-target build failed with exit **1**. No second proof
build, query build, or repair cycle was run. In particular,
`tools/print-assumptions.sh` was not run on the failed module, because it
would rebuild the target. No full `arm8_inet_makeaddr_proof.vo` exists.

## Exact scope and preserved statements

`Examples/claude/arm8_inet_makeaddr_proof.v` imports the unchanged complete
19-instruction e29 map. Entry is `0x1f9d40`; exits are the RET instructions
at `0x1f9d50`, `0x1f9d68`, and `0x1f9d88`. Official Ubuntu ARM64 glibc
2.35-0ubuntu3.15 SHA256 is
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
The map SHA256 remains
`41c9789da4f26019b8c8b9269f421d8f1ac74b0a34925d1b2b5d4c74a8d75ae8`.
This is the Ghidra 11.4.2 explicit scalar replacement; its binary/lifter
provenance remains inherited, not proved.

`inet_makeaddr_correct` is an **unproved, Aborted statement** of
`satisfies_all` entry-to-RET partial correctness. Inputs are the low32 bits
of X0/X1; no restrictions are placed on their upper halves beyond ordinary
64-bit typing. Output is zero-extended `ntohl32 (makeaddr net host)` in X0.
`makeaddr` uses boundaries 128, 65536 and 16777216, then OR in the final
case, with the specified host masks and 32-bit truncation. The postcondition
includes memory, SP and X30 equality. A separate generic frame theorem
covers modeled X19-X29 and Z8-Z15, SP and X30. There are no memory, size,
overlap, callee, global, CPU-feature, tunable or result-oracle premises.
The witness statements cover every 32-bit input pair; the chosen concrete
input store also permits arbitrary 32-bit upper halves. No termination,
whole-binary/lifter refinement, CPU fault, cache or concurrency claim.

All 18 lemma/theorem statements are retained verbatim from the submitted
initial build. The exact complete original source is
`initial-attempt.v.txt`. All nine unchecked proof bodies, starting with
`inet_bfm24_correct`, have been replaced by `Abort`; their original scripts
remain in that snapshot. The nine earlier Qed bodies are unchanged.
The live file is a handoff and has not been recompiled after this mechanical
Abort conversion. The root Dune edit adds only this proof module to the
existing explicit list.

## One permitted build and failure

See `initial-build.log` for the exact shell-escaped command, all compiler
stdout/stderr, and true exit status. It invokes the read-only environment:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_inet_makeaddr_proof.vo'
```

The dependency closure, including the generated map and `arm8_common`,
produced full `.vo` files in that build. The requested proof target failed
at original line 133, characters 34-50, in `inet_bfm24_correct`:

```text
Error: In environment
net, host : N
IW : 0 < 32
Unable to unify
 "(0 <? 32) && ((if 0 <? 24 then false else true) || (0 <? 24) && true)"
with
 "(0 <? 32) &&
  (true && xorb (N.testbit 4278190080 0) false
   || ((0 + 8 <? 32) && true
       || (0 <? 32) &&
          (if 0 <? 32 - 8 then false else (0 - (32 - 8) <? 32) && true)) &&
      N.testbit 4278190080 0)".
```

This is a tactic equality failure, not an observed memory-cap failure.
The remaining BFM lemmas, subtraction helper, input/spec witnesses and
functional theorem were not reached. Their attempts may contain additional
issues; no claim is made that fixing this first error will complete them.
The fixer must retain the statements unless genuinely wrong and explain
any statement change.

## Assumptions and source audit

`Print Assumptions` follows each initial declaration. The raw prefix output
is in `initial-build.log` and copied verbatim (with the exact failure) to
`raw-prefix-assumptions-and-error.txt`. Nine facts reached Qed and Print:

- `inet_makeaddr_nwc`: closed.
- `inet_makeaddr_welltyped`: inherited functional extensionality only.
- `inet_makeaddr_preserves_memory`: closed.
- `inet_makeaddr_preserves_callee_saved`: closed.
- `inet_makeaddr_preserves_sp`: closed.
- `inet_makeaddr_preserves_x30`: closed.
- `inet_makeaddr_ret_map`: closed.
- `inet_makeaddr_result_bound`: closed.
- `inet_rev32_correct`: closed.

Verbatim inherited assumption (also printed for the generated map):

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

These are checked prefixes of a failed compilation, not a successful full
module certificate. There is no assumptions output for the main theorem
or any unchecked helper. Transitive assumption review for completion is
therefore outstanding. Neither imported admitted results nor new axioms
were used as a substitute. `source-audit-initial.log` and
`source-audit-final.log` record the full baseline-relative source auditor;
new forbidden-token totals are empty. Baseline unrelated admissions and
module-interface parameters are reported honestly by that auditor.

## History and operational constraints

The prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
with sole parent `49956416928e5b6bb3928b54ae33e3b81091f006`. Initial status
was clean before evidence files were created; `ancestry-before.log` shows
only those newly created unit notes as untracked. The read-only fork-name
check returned no branch, exit 0 (`fork-name-check.log`). The initial
sandbox DNS attempt failed, then the read-only network retry succeeded.
The sandbox also denied the first branch rename because shared Git metadata
is outside the writable worktree; the authorized retry succeeded. Only the
prepared branch was renamed and the exact accepted e29 was fast-forwarded.

Allowed prerequisite history, in addition to the pinned origin base:

- e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`
- e02 `081d0233cd6667803b3907343b2fea6dc9eba714`
- e02 merge `052521a753adbda077843ec7b259801282a7b1e9`
- e11 `378fe1b57514b9af3f017a72b4ca665910156cc7`
- e08 `9ae8e6800fa044797efd98372857e6ac89b18e1b`
- e29 `9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b`

The merge base remains the pinned origin base. See `prepare-branch.log`
and `ancestry-handoff.log` for history/status/diff evidence. Only this unit's
local commits follow e29. No other branch was changed, no worktree created,
no dependencies installed, no shared environment modified, and no remote
write, push or PR performed. Every proof process used the 2,000,000 KiB
virtual-memory cap and 65536 KiB stack, with Dune `-j1` and cache disabled.
