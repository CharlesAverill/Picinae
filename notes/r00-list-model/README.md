# r00-list-model — initial Astra attempt

Author: OpenAI gpt-6-astra, xhigh/priority. Final proof model: pending validation.
One-shot policy: one full relevant Dune build; failure is a PARTIAL handoff to a
new gpt-6.1-sol xhigh/priority fixer, without a second Astra repair cycle.

Branch: llm-proofs/r00-list-model.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-bcf6e4e7.
Base: 49956416928e5b6bb3928b54ae33e3b81091f006.
Prepared HEAD verified: 71470bffba65392adf1873a3df9f0cf0ca4f1ac9 (sole parent base).
Exact fork-name lookup succeeded with no result (03-fork-name-network.log).
Only prepared local branch renamed, then fast-forwarded to reviewed checkpoint
95da7ab7cee78f09a528aed86c1dfaf29520a9a8. Approved prerequisite commits are e00,
e03 original/integration/validation, e04, e05 integration/implementation/evidence.
No fork history, installation, shared environment modification, or publication.
The first sandboxed network and branch metadata operations failed; authorized
escalated retries succeeded. No automatic approval rejection occurred.

Read plan.md (current policy and assigned r00 row), BUILDING.md,
Examples/claude/SKILL.md, e05-accepted-leaf-artifacts.json, abi.json, the five list
manifests, compiler layout evidence and existing list/memory proof templates.
The 17-leaf artifact gate is accepted; full e05 remains partial for 24 closures.
No unsupported closure is imported. This kit imports only Picinae_armv6m.

The source header records the exact official release, kernel hash, ELF hash,
32-bit little-endian layout and ABI boundary. No generated lift, e03 ISA/frontend,
e04 fixture, or shared campaign file is modified. The Dune module entry sits
outside the generated selection block.

## Promised theorem statements and scope

The initial source is archived verbatim as initial-attempt.v.txt before the only
build. It contains all statements and full initial proof scripts:

- field32_bound, field32_read_write, field32_frame: bounded four-byte loads,
  read-after-write for bounded words, and exact modular byte separation frames.
- ranges32_separate, field_address32_nowrap, fields20_separate: nonwrapping
  half-open ranges, pointer arithmetic and separation of the five word fields.
- field32_object_frame, outside_frame32_refl/trans/write: original-memory byte
  frames outside an object, including sequential-write composition.
- image20_fields/frame/welltyped: five arbitrary word values in a 20-byte object,
  outside-memory preservation and memory typing. A finite witness constructor,
  not a replacement kernel program.
- empty_image_spec/frame: count zero, index equal to the embedded sentinel,
  sentinel value UINT32_MAX and both sentinel links equal to itself.
- memory_store32_welltyped, empty_list_witness: a welltyped ARMv6-M store with
  that empty list for every nonnull aligned nonwrapping 20-byte pointer, built
  from zero memory without evaluating its enormous bitwidth.
- list_regions_witness, concrete_empty_list_witness: disjoint objects at 4096
  and 8192, and an actual typed empty list at 4096.

No function correctness, termination, exit/invariant, nwc, register preservation,
permissions or CPU/interference contract is claimed. Later r01-r05 prove those
against their actual lifts. Owner values are opaque words; no TCB invariant.
The arithmetic predicates allow ranges ending exactly at 2^32. The frame and
word-operation lemmas also support modular addresses without the range premise.

## Validation

Use the read-only arm-validation/picinae-env wrapper. Every proof process:
PROOF_MEMORY_KB=2000000, ulimit -v 2000000, ulimit -s 65536, one compiler,
Dune --cache=disabled -j1, full .vo. No .vos and no skipped checking.
Status and exact diagnostics will be appended after the initial build.

## Result: PARTIAL — new Sol fixer required

The sole initial full Dune build exited **1**. Its complete stdout/stderr and
exact invocation are in 07-dune-initial.log. The dependency closure through
Picinae_armv6m compiled, then armv6m_list_model.v failed at line 180 (initial
source), inside image20_fields: the rewrite loop left the first field load
unreduced, so final reflexivity could not unify it with v0. This was a proof
script failure, not a reported memory exhaustion. No second build, tactical
repair, or other proof compilation was attempted.

The original complete source/proof attempt is preserved byte-for-byte in
initial-attempt.v.txt (SHA256
e7372f6de2a0cbc33e93bd344c4234cdcfe8a868419d0a861373f7e3739dcaad).
The live .v retains the checked prefix through outside_frame32_write and every
subsequent exact theorem statement, with failed/unreached proof scripts replaced
by Abort. All original scripts remain in the archive. This is packaging an
unfinished attempt, not a changed theorem or an Astra repair cycle. No statement
has been weakened or changed. The post-packaging file is deliberately unbuilt.
There is **no successful full unit target**, and no main theorem completion claim.

Print Assumptions output: **unavailable** for this module because no .vo exists.
The required tools/print-assumptions.sh rebuilds its target, so invoking it after
failure would violate the explicit one-build handoff policy. The Sol fixer must
run it on every exported theorem after fixing the source and achieving a full
build. No transitive-assumptions completion claim is made here. The accepted
baseline reports inherited Stdlib
FunctionalExtensionality.functional_extensionality_dep; its presence or absence
in each r00 theorem remains to be determined, not assumed closed.

Both the repository-wide and unit-scoped source audits passed (08/09); the unit
contains no admissions, admit, Axiom or Parameter. Repository-wide existing
counts are seven Admitted, one admit and 89 module-interface Parameters; NEW is
empty. These lexical counts are not a substitute for transitive assumptions.
The exact ancestry whitelist audit passed (10), with original ISA/frontend,
generated lifts/manifests and fixture unchanged.

Initial author model: gpt-6-astra. Final proof model: **none (unfinished)**.
Coordinator action: dispatch a NEW gpt-6.1-sol xhigh/priority fixer, retaining the
statements; explain any genuinely necessary statement change. Remaining work:
repair image20_fields and validate all later attempts; full target, all exported
Print Assumptions, final source/ancestry audits. No delegation performed here.
