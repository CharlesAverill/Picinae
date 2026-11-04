# a-strcmp — PARTIAL Astra handoff

Branch: `llm-proofs/a-strcmp`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-9191917d`.
Initial author: **gpt-6-astra, xhigh/default** (assigned launch settings).
Final functional-proof producer: **none**.
Next step belongs to a **new gpt-6.1-sol xhigh/default fixer** appointed by
the coordinator. No subagent was started here. Nothing was published or
installed; the shared isolated environment was read only.

The sole full build failed with exit **1** at the final `Qed` of
`strcmp_correct`: `Attempt to save an incomplete proof (there are remaining
open goals)`. This was a proof failure, not an out-of-memory failure.
Twenty-one unresolved invariant obligations are printed in the complete log.
No second proof build, repair cycle, or additional compiler invocation followed.

The exact initial source is `arm8_strcmp_proof.initial.v.txt`. The source in
`Examples/claude/arm8_strcmp_proof.v` differs only in its status comment and
replacing the failed main `Qed`/unreachable Print command with `Abort` and an
explanation. Every definition and theorem statement, including the complete
entry contract, is unchanged. This final packaging was **not rebuilt**.
There is no `arm8_strcmp_proof.vo`, and no completed `strcmp_correct` constant.

## Actual evidence

The exact full-target command, stdout/stderr and true exit status are in
`05-one-shot-full-build.log`:

```sh
bash tools/record-command.sh notes/a-strcmp/05-one-shot-full-build.log \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 4000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_strcmp_proof.vo'
```

The selected core, ARM8 helpers and unchanged e30 strcmp map compiled before
the target failed. There is **no successful full new proof target command**.
The compiler did check ten preceding `Qed`s and execute their transitive
`Print Assumptions` commands. `initial-proof-check-times.txt` preserves the
compiler's per-proof auxiliary record. This is evidence for those completed
helpers within the failed compilation, not a full-module `.vo` certificate.

`assumptions.raw.log` is the verbatim contiguous ten-query output from that
build; source order maps it to:

| Declaration | Observed assumptions |
| --- | --- |
| `strcmp_nwc` | Closed under the global context |
| `strcmp_welltyped` | Inherited functional extensionality below |
| `strcmp_preserves_memory` | Closed under the global context |
| `strcmp_preserves_callee_saved` | Closed under the global context |
| `strcmp_preserves_frame` | Closed under the global context |
| `strcmp_byte_bound` | Closed under the global context |
| `strcmp_stop_unique` | Closed under the global context |
| `strcmp_domain_ones` | Closed under the global context |
| `strcmp_samples_stop` | Closed under the global context |
| `strcmp_samples_readable` | Closed under the global context |

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited e00/e30 typing assumption, not a new axiom. No imported
admitted fact appears in the ten observed outputs. The main theorem has no
assumptions output because it failed. `tools/print-assumptions.sh` was read
but **not invoked** after failure: it would first rebuild the missing target,
violating the immediate one-shot handoff policy. A successful Sol completion
must run that harness for every main/helper/frame/witness declaration.

`06-source-audit.log` records the required whole-repository source audit
against base `49956416928e5b6bb3928b54ae33e3b81091f006`, exit **0**, NEW totals
`{}`. Existing unrelated baseline admissions are inventoried, not imported
into the proof. The final scoped audit also must show no new forbidden tokens.

## Scope and remaining proof obligations

`strcmp_full_contract` fixes the intended all-alignment/all-length input
contract and `strcmp_correct` is its aborted proof attempt. The postcondition
compares `Z.compare (toZ 32 X0) 0` with the unsigned comparison of the original
bytes at first-stop index K. It includes unchanged memory, SP, X30,
X19..X29, full modeled Z8..Z15, and access masks. Standalone frame theorems
cover every finite IL execution, without an alignment/size precondition.

The domain explicitly permits aliases and overlap and requires readable
`[down8(p),down8(p+K)+8)` and `[down8(q),down8(q+K)+16)`, both upper bounds
strictly below 2^64. It has no feature/tunable premise. This conservative
domain requires padding even where a minimal path-specific domain might not;
it does not exclude any pointer alignment or require a fixed short string.
Page-end samples are included with their padding readable. `CONTROL-FLOW.md`
records all actual loads, paths, both RET addresses, and the mismatch with
the brief's assertion that the map has three exits.

Seven concrete samples establish satisfiability of the stop/readable-domain
predicates: equal high-byte alias, two unequal high-byte cases with different
alignment/sign, either operand terminating first, overlapping empty strings,
and page-end addresses. These witnesses are input-memory/permission facts;
they are not execution witnesses or a full typed-store/caller construction.

Still open: all substantive invariant preservation, linking the read envelope
to actual loads, mask/borrow lemmas, prefix masking, word-byte decomposition,
REV/CLZ/variable-shift sign preservation, CCMP path-condition reasoning,
loop advancement, and final postcondition for both RET sites. The initial
automation symbolically executes paths and displays obligations; it does not
certify any complete functional path. Internal pair/syndrome assertions are
obligations to prove, not caller assumptions or established mask oracles.

Termination, execution of RET to a caller, fault freedom, hardware/binary-lifter
refinement, and concurrency are separate unproved claims. Retain the initial
statements in the repair; explain any necessary correction explicitly.

## Ancestry and local-only audit

The prepared branch `t3/strcmp-proof` was clean at reviewed e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, merge-base
`49956416928e5b6bb3928b54ae33e3b81091f006`. A read-only fork collision check
succeeded with no result before renaming only this branch. One recorded
sandbox network retry failed DNS (exit128); the subsequent approved read-only
check succeeded (exit0). Git metadata required sandbox escalation for the
authorized local rename/fast-forward; no approval rejection occurred.

Only reviewed e30 `bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9` was fast-forwarded.
`allowed-prerequisites.txt` fixes the exact seven authorized prerequisite
commits (including the e02 import merge). `00-preflight.log` records the
original clean status, history and diff stats before any proof edit.
`audit-ancestry.py` verifies the base, prerequisite set, own-only linear
continuation, branch, protected lift hash, changed paths, diff and status.
No fork, active-unit, or unrelated history was imported. Root Dune adds only
`Examples.claude.arm8_strcmp_proof`; its required dependencies were already
in the reviewed explicit module list.
