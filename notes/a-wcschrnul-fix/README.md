# a-wcschrnul-fix: DONE

Initial author: OpenAI `gpt-6-astra`, xhigh/default. Final checked proof
producer: OpenAI `gpt-6.1-sol`, xhigh/default. All eleven original statements
now have full kernel-checked proofs. No statements or definitions changed;
no admissions, aborted results, new axioms or parameters remain in the unit
proof. No imported admission occurs in the eleven transitive assumptions
queries. This completion is for the stated IL partial-correctness contract.

Branch: `llm-proofs/a-wcschrnul-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-dd8b174b`.
Pinned origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Exact allowed source checkpoint: `1c2abb70e24ea225674978b19053cd05b392b334`.
The final local commit and clean after-status are recorded by `audit-history.sh`
in the final handoff and external unit-only evidence directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-wcschrnul-fix/`.

## Contract and coverage

`wcschrnul_correct` establishes `satisfies_all` for the complete unchanged
nine-instruction `e30_wcschrnul_arm8` map, entry `0x19e4c0`, loop load
`0x19e4d0`, unique RET `0x19e4e0`. Input assumptions are:

- A model-typed AArch64 store and trace starting at that exact entry.
- X0 = p, X1 mod 2^32 = c, SP = sp, X30 = lr, and initial memory m.
- A stop index k with every earlier little-endian four-byte word different
  from c and zero, and the word at k equal to c or zero.
- `p + 4*(k+1) <= 2^64`; every byte of all k+1 words has the actual A_READ bit.

All 32-bit wchar patterns and low32 target values are covered, including
high-bit-set patterns and c=0. Pointer alignment is arbitrary. There is no
signed-wchar positivity, overlap, code/data separation, CPU-feature, tunable,
callee-contract or result-oracle assumption. At RET, X0 = p+4*k; memory,
low32 X1, SP and X30 retain their initial values.

`wcschrnul_return` separately proves that executing the exact RET jumps to
`Addr lr` while retaining that postcondition after resetting temporaries.
`wcschrnul_preserves_memory` and `wcschrnul_preserves_callee_saved` apply to
all execution endpoints and preserve memory, X19-X30, SP, full modeled
Z8-Z15 cells, A_READ, A_WRITE and full X1 (not merely its low32 bits).
`wcschrnul_input_satisfiable` witnesses the entire typed/readable input at
unaligned pointer 1 with an empty string, for every target bit pattern.

The retained pure helpers are `wcschrnul_stop_hit`, `wcschrnul_stop_miss`,
`wcschrnul_addr_bound`, and `wcschrnul_eq32`. Map facts are `wcschrnul_nwc`
and `wcschrnul_welltyped`. No new helper contracts were introduced.

## Exact restoration and repairs

The starting proof was restored from the exact initial Astra archive, hash
`4d3988242e3c104d76273dea3e3ea98238ee911a429a037552de4c7e7585ba29`.
`repair-vs-archive.diff` records every final source change relative to it:

1. Repair the invalid witness destruct pattern using named equations and
   `subst j`. The witness and theorem are unchanged.
2. Pass k, w, C, WB, HIT and MISS explicitly into the finishing Ltac; these
   names were unbound when that tactic was originally defined.
3. Use equality symmetry/congruence when applying HIT. The initial CCMP
   gives c=w whereas HIT uses w=c; propositional `tauto` alone failed.
4. Match the simplifier's `4+p+4*i` address ordering in the local ADD equality,
   rather than `p+4*i+4`. Its no-wrap justification and loop invariant remain
   unchanged.
5. Destructure the RET interpreter result as `[[STATE EXIT] _]`, accounting
   for its final True conjunct. Its LR substitution is already performed;
   the original additional rewrite was redundant and addressed the wrong
   conjunction component.
6. Update only the provenance comment to identify the checked Sol repair
   and its evidence, retaining the original Astra attribution.

No substantive statement, definition, ABI or generated-map change was needed.
All eight original definitions and eleven statements are retained verbatim.
The original author notes/archive and entire e30 artifact directory are
unchanged. The generated map hash remains
`ab43b39ccf445c4cb9889ae1e2df855f35c9daf85d53056c1f7d2c4127bd3d20`.
Root Dune already explicitly selected the target and required lift in the
checkpoint, so no module-list extension or unrelated build selection was needed.

## Validation and transitive assumptions

Successful commands (both actual exit 0):

```bash
bash notes/a-wcschrnul-fix/build.sh 11-build
bash notes/a-wcschrnul-fix/run-assumptions.sh
```

The first invokes the real full `.vo` target:

```bash
python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-wcschrnul-fix --memory-kib 1750000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_wcschrnul_proof.vo'
```

The second rebuilds the final source, including its final provenance comment,
with the same cap/stack/cache/jobs settings, then runs the required
`tools/print-assumptions.sh` for all eleven results inside the same gate.
`assumptions.log` contains the complete unedited compiler/query output,
including both main theorems and the nonvacuity witness. The final `.vo` is
1128190 bytes. No `.vos` or skipped kernel check was used.

Eight results print `Closed under the global context`: nwc, both frame
results, the four pure helpers, and input satisfiability. Only welltyped,
correct and return print the following verbatim transitive assumption:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited Stdlib axiom documented by e00, not a new unit axiom.
There are no other transitive assumptions or imported admitted facts.
`14-assumptions-summary.log` verifies all eleven outputs, retaining the raw
log as the authoritative evidence. Rocq prints some trailing spaces in its
pretty-printed types; those are preserved verbatim in the raw log. The
archival unified diff also retains its context-line prefixes. Only these two
raw evidence files are excluded from the staged whitespace check.

`12-final-retention.log` verifies the unchanged statements/definitions and
protected artifacts. `13-final-source-audit.log` is the required full source
audit against the pinned base, exit 0, `NEW totals: {}`. Inherited unrelated
admissions reported in its inventory are not in this theorem closure.
`03`, `04`, `07` through `10` record all failed repair builds, with true exit
1; `07` also preserves the diagnostic goals. `11-build.log` records the first
successful full target. Gate RAM/paging waits and every actual compiler/query
command/stdout/stderr/exit are retained. No cap was raised or gate bypassed;
no concurrent proof compilers were run inside the unit.

## Ancestry, publication and limits

The prepared branch started clean at e00
`71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole parent is the pinned
base. The remote branch-name collision check succeeded with empty result
before renaming only the prepared branch. The sole import was an exact
fast-forward to the assigned Astra checkpoint. Only that explicitly allowed
prerequisite history plus this unit's own repair is above origin. The original
Astra branch is preserved. Nothing was installed, pushed, published, commented
or written to a remote; no other branch or shared environment was modified.
`00-before.log`, `01-branch-check.log`, `02-import-audit.log` and the history
audits record status, merge-base, complete commit lists and diff stats.

There are no remaining proof gaps within these eleven statements. These are
partial-correctness and frame results for sequential Picinae IL, not a proof
of termination, hardware fault freedom, concurrency behavior or verified
machine-byte-to-IL refinement. The binary/package provenance and lifter are
inherited from e30. Real hardware use of unaligned loads additionally depends
on memory type/alignment configuration, which this IL does not model.
