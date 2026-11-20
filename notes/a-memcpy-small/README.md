# a-memcpy-small — PARTIAL Astra author handoff

Initial author: `gpt-6-astra`, xhigh/priority. Final proof model: **unset**.
Branch: `llm-proofs/a-memcpy-small`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-2997b5fa`.

The one permitted full Dune attempt exited **1**, before the main proof was
compiled. No second repair cycle or proof build was performed. A NEW
`gpt-6.1-sol` xhigh/priority fixer delegate is required from the coordinator.
Do not treat this checkpoint as accepted correctness, typing, or witness work.
No dependencies were installed, no shared environment was changed, and no
remote writes, pushes, PRs, other-branch mutations, or subdelegation occurred.

## Exact failure and preserved attempt

`05-full-build-once.log` contains the exact invocation, full stdout/stderr and
true exit status. The first error was:

```
File "./Examples/claude/arm8_memcpy_common.v", line 108, characters 57-67:
Error: The variable msub_add_l was not found in the current environment.
```

The adapted pure-memory `msub_off` proof relied on a helper defined at baseline
`Examples/claude/amd64_common.v:254`. The ARM-only module intentionally does not
import that architecture. Porting/proving the missing pure helper is left to
the new fixer; no post-failure repair was attempted.

The exact pre-build sources are `initial-arm8_memcpy_common.v.txt` and
`initial-arm8_memcpy_small_proof.v.txt`. All 16 original lemma/theorem statements
are retained verbatim in the active sources; `statement-preservation.txt`
records the comparison. The failed `msub_off`, dependent `cpy_store`, and all
seven unchecked main-module declarations now end in `Abort`. Initial tactics
and bodies remain in the archives. No statement was weakened or changed.

Seven common-module proofs reached Qed before the failure: `byte_of_getmem`,
`byte_setmem_cases`, `cpy_empty`, `cpy_equiv`, `cpy_copied`, `addmsub`, `cpy_load`.
Their bodies remain, but the module did NOT produce a successful full `.vo`;
these are not a certified reusable module or transitive-assumptions certificate.
The cleanup to Abort was not rebuilt, as required by the one-attempt policy.

## Proposed coverage (not proved)

`memcpy_small_correct` uses `satisfies_all` on the unchanged actual e08 union
map, starting at generic entry `0x19ab40`. It covers count 0..32, original-source
copy for every i<n, every byte outside the modular destination interval, X0=d,
and a trace-scoped frame for SP, X19..X29, X30, R_LR and full modeled Z8..Z15.
The explicit hypotheses are typed initial state, X0=d/X1=s/X2=n, initial memory
m, n<=32, d+n<=2^64 and s+n<=2^64, disjoint modular buffers, readable source
bytes and writable destination bytes. Typed pointers are 64-bit; no positivity,
non-null, alignment, global threshold, tunable, or CPU-feature premise is added.

`memcpy_small_preserves_callee_saved` exports the frame at one of the four actual
RET addresses, under an executed trace with no previous small exit. The proof
stops AT RET, not after returning into arbitrary caller code. `memcpy_small_nwc`
and `memcpy_small_welltyped` are also retained as unchecked statements.
`memcpy_small_witness_typed`, `memcpy_small_entry_inhabited`, and
`memcpy_small_zero_entry` specify symbolic typed, fully accessible witnesses,
including d=s=n=0. None was reached by this build.

The initial proof enumerates all 33 sizes, steps actual instructions with
`arm8_step`, and uses written-offset byte/frame lemmas for the store chains.
It has not been checked past the failed helper; later tactic failures or resource
needs remain unknown. No result/postcondition/callee contract is an assumption.
The header inventories every small-path instruction and actual flag widths.
Medium/large, wrappers, termination, fault freedom, CPU/cache/IRQ behavior, and
binary-to-IL/lifter refinement remain outside this specification.

## Build and assumptions evidence

The only full proof build command was:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 2000000; ulimit -s 65536; export PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_memcpy_small_proof.vo'
```

Result: **exit 1**. No successful command for either new `.vo` target exists.
Dune did compile the unchanged prerequisite generated map and ARM core closure.
Its generated `Print Assumptions welltyped` emitted this exact inherited result
(also extracted verbatim to `assumptions-prerequisite-raw.txt`):

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the baseline FE assumption documented in e00, not an admission or new
unit axiom. There is **no assumptions output for any new main/frame/witness
constant**, since they were not compiled. `tools/print-assumptions.sh` was read
but not run against absent new constants: it would rebuild after the required
failure handoff. After successful repair, the fixer must use that script with
PROOF_MEMORY_KB=2000000 and PROOF_STACK_KB=65536 on all seven main declarations
and every new/common helper, preserving raw output and inspecting transitive
assumptions. Source-only checks cannot certify their closure.

`07-final-source-audit.log` records the required whole-tree audit against pinned
base, exit 0: no new suspicious tokens. Baseline and current totals are both
7 Admitted, 1 admit, 89 module-interface Parameter declarations. None of the
inherited admitted example files is imported by this unit. The scoped initial
audit had no suspicious tokens in either new file. `08` records whitespace
check exit 0. This does not convert the partial work into a successful proof.

## Ancestry and protected inputs

Prepared HEAD was exactly e00, whose sole parent was the pinned origin base.
The first status was clean before evidence files were created. The recorded
preparation status shows only the new evidence directory. A successful empty
read-only fork collision check preceded renaming only the prepared branch.
Sandbox DNS/Git metadata restrictions required an authorized elevated retry;
no approval rejection occurred. The exact authorized ff-only e08 import
succeeded. No fork or unrelated history was imported.

The allowed prerequisite set above origin
`49956416928e5b6bb3928b54ae33e3b81091f006` is exactly:

- e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`
- e02 artifact checkpoint `081d0233cd6667803b3907343b2fea6dc9eba714`
- e11 import `052521a753adbda077843ec7b259801282a7b1e9`
- e11 final `378fe1b57514b9af3f017a72b4ca665910156cc7`
- e08 final `9ae8e6800fa044797efd98372857e6ac89b18e1b`

Only this unit's checkpoint follows e08. Logs 00/02/03 preserve initial/imported
ancestry and stats; `audit-ancestry.py` checks the exact set and optional own
commit parent. Final commit SHA, log/stat, and clean status are recorded after
commit in the authorized external `units/a-memcpy-small/` directory.

`06-protected-artifacts.log` records no changes anywhere in scalar_ports and
hashes the actual map/manifest/pcode. The 108-instruction map and provenance
are unchanged. Root Dune adds only the two new modules to the inherited list.
The exact ELF/package hash, model-address offset and trust limits remain in the
proof header and accepted e08 provenance.
