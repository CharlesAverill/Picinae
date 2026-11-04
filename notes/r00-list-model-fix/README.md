# r00-list-model-fix — completed shared list memory kit

State: **DONE for this helper-kit scope**. Initial author: OpenAI gpt-6-astra,
xhigh/priority. Final proof producer and iterative fixer: OpenAI gpt-6.1-sol,
xhigh/priority. All 19 exported facts are proved with Qed and checked in the
full `Examples/FreeRTOS/armv6m_list_model.vo` target. This is not a function
correctness, termination, or full binary-soundness result.

Branch: `llm-proofs/r00-list-model-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-db745613`.
Implementation commit: `4369208b4edce53f84113bcfd3b859f3f58be334`.
A subsequent local evidence-only commit records the clean post-implementation
audit. Its final HEAD and final clean status are returned with the handoff.
No installation, remote write, subdelegation, or shared toolchain modification.

## Exact preservation and repairs

The initial author's branch/worktree and all `notes/r00-list-model/` artifacts
remain untouched. Its `initial-attempt.v.txt` and `07-dune-initial.log` retain
original proof scripts and the first failure. All original definitions,
predicates, imports and **all 19 exact theorem statements are unchanged**.
`check-preservation.py` compares the entire non-proof source against the archive,
ignoring comments/whitespace only; it also checks the theorem count and absence
of unfinished declarations. There are no added public helper contracts or
weakened hypotheses. The source header now attributes the final repair.

Only two original proof scripts needed repair:

1. `image20_fields`: the original `auto` membership search did not reach the
   fifth list element (16). A diagnostic exposed the unsolved disjunction
   `0 = 16 \/ 4 = 16 \/ 8 = 16 \/ 12 = 16 \/ 16 = 16 \/ False`.
   Use explicit memory/offset arguments for the nested frame/read-write
   rewrites and `tauto` for finite membership. This proves all five arbitrary
   bounded field values; separation and value bounds are unchanged.
2. `empty_list_witness`: the original `unfold memsize` is disallowed because
   the imported ISA marks it opaque. Establish positivity at abstract width
   with `change (0 < 2^(2^w*8))` and `mp2_gt_0`, then instantiate at 32.
   No concrete memory-size power or memory value is evaluated. The same
   zero-memory witness and the complete typed/frame/empty-list result remain.

The other seven formerly aborted scripts were restored unchanged from the
archive and passed. The original ten prefix proofs remain unchanged. Root Dune
already selects this handwritten module outside e05's generated block; this
fixer makes no Dune change and imports no additional module or unit.

## Exact scope and hypotheses

- `field32_bound`: every four-byte little-endian load is below 2^32.
- `field32_read_write`: same-field read-after-write for a value below 2^32.
- `field32_frame`: unchanged four-byte load given modular byte disjointness
  of the loaded and stored words. No nonwrap/alignment premise is needed.
- `ranges32_separate`: two nonwrapping half-open ranges with ordered endpoints
  are modularly disjoint. `range32 p n` means `p < 2^32` and `p+n <= 2^32`.
- `field_address32_nowrap`: a field offset below the nonwrapping range size
  leaves its address unchanged by reduction modulo 2^32.
- `fields20_separate`: distinct offsets from `[0;4;8;12;16]` have disjoint
  four-byte words when `p+20 <= 2^32`.
- `field32_object_frame`: a write at an offset with `off+4 <= n` preserves
  every byte modularly outside the enclosing object.
- `outside_frame32_refl`, `outside_frame32_trans`, `outside_frame32_write`:
  original-memory byte-frame identity, composition, and contained-write rule.
- `image20_fields`: any original memory, `p+20 <= 2^32`, and five arbitrary
  values below 2^32 give all five exact fields at offsets 0/4/8/12/16.
- `image20_frame`: the five writes preserve every byte outside the 20-byte
  region relative to the original memory, without a nonwrap/alignment premise.
- `image20_welltyped`: memory below `memsize 32` remains so after five writes;
  no field-value bounds are required for this typing result.
- `empty_image_spec`: for `object32 p 20` (nonnull, aligned modulo 4,
  nonwrapping), count = 0, index = p+8, sentinel value = 4294967295,
  sentinel next = p+8 and previous = p+8. The sentinel is embedded at offset 8.
- `empty_image_frame`: all original bytes outside the list's 20 bytes persist.
- `memory_store32_welltyped`: memory below `memsize 32`, with every other
  register/flag/permission map zero, gives a store modeled by `armv6mtypctx`.
- `empty_list_witness`: for **every** `object32 p 20`, construct that typed
  empty-list store from zero memory and prove its outside-zero-memory frame.
- `list_regions_witness`: concrete nonnull aligned 20-byte list and item
  regions at 4096 and 8192 are nonwrapping and disjoint.
- `concrete_empty_list_witness`: a typed empty list actually exists at 4096,
  with every outside byte equal to zero memory.

This uses 32-bit little-endian ARMv6-M memory, not x86-64/AArch64 pointers.
ListItem is 20 bytes (value/next/previous/opaque owner/container at 0/4/8/12/16),
MiniItem is 12 (value/next/previous at 0/4/8), List is 20
(count/index/sentinel at 0/4/8, sentinel links 12/16). Owners are opaque values;
no TCB or scheduler invariant is assumed. The witnesses do not claim readable
or writable permissions: their permission maps are zero. There is no execution
path, return/exit invariant, CPU/tunable restriction, interrupt/IRQ stability
assumption, callee contract, nwc claim, or register preservation theorem here.
Those belong to later function units. No handwritten program replaces a lift.

Layout provenance remains the accepted compiled official FreeRTOS V11.1.0,
commit `dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`, ELF SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
The helper kit imports only the reviewed original `Picinae_armv6m`, with no
IRQ/callee contracts or e19 mask-engineering changes. Accepted e05 has 17
closed-leaf artifacts; its 24 unsupported call closures remain outside scope.
The inherited ISA/lifter and layout provenance do not become hardware/binary
refinement theorems through this memory kit.

## Validation and assumptions

All proof processes used the read-only
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`,
`PROOF_MEMORY_KB=2000000`, `ulimit -v 2000000`, stack 65536 KiB,
`--cache=disabled -j1`, one compiler at a time, full `.vo` mode.
No cap was raised. Every invocation and its actual exit/stdout/stderr is kept
by `tools/record-command.sh` in this directory.

- 06: first fixer full build, exit 1 at the remaining finite membership issue.
  All selected core dependencies compiled here with full checking.
- 08–09: full-target diagnostics, exit 1, exposed the membership disjunction.
- 10: fields/frame/typing/empty-spec proofs passed, exit 1 at opaque memsize.
- 11: full target success, exit 0, including all 19 declarations and witnesses.
- 12: `tools/print-assumptions.sh` queried **all 19 facts**, exit 0. Every
  `Print Assumptions` says verbatim `Closed under the global context`.
- 13–14: repository and unit source audits against pinned origin, exit 0;
  NEW totals `{}`; unit CURRENT totals `{}`. The baseline still inventories
  seven unrelated Admitted, one admit and 89 module-interface Parameters.
  These are not assumptions of any of the 19 facts, as the transitive output
  confirms. The inherited Stdlib
  `FunctionalExtensionality.functional_extensionality_dep` documented by e00
  is **absent from every one of these 19 theorem dependencies**.
- 15: exact definition/statement preservation, exit 0.
- 16: exact approved prerequisite+author ancestry whitelist, exit 0.
- 17: final source full-target rebuild, exit 0, after explanatory comments.
- 18–19: final declaration preservation and unit source audit, exit 0.
- 20: final raw all-19 assumptions output, exit 0; all 19 remain closed.
- 21: strengthened ancestry/source-scope audit before commit, exit 0.
- 22: local implementation commit and clean status, exit 0.
- 23: post-implementation ancestry whitelist, both diff stats, and clean
  worktree assertion, exit 0. Only the implementation and this evidence are
  added above the author checkpoint.

No new admission, Axiom, Parameter, or Abort is present in the kit.

## Ancestry and remaining boundaries

Pinned origin and merge-base:
`49956416928e5b6bb3928b54ae33e3b81091f006`.
Prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is origin. The initial sandbox network lookup failed (02),
then the exact read-only fork lookup succeeded empty (03). The initial sandbox
branch rename failed before changing anything (04); an authorized metadata
retry renamed only the prepared branch and fast-forwarded to Astra checkpoint
`7de9edcc1e5094133d66bbeae129ef48078b9265` (05). No auto-review rejection.

`audit-ancestry.sh` enforces the exact nine allowed pre-fixer commits (reviewed
e00/e03/e04/e05 plus Astra), plus explicitly supplied fixer commit(s). It records
merge-base, full origin-to-HEAD subjects, diff stat and status. It checks the
original ISA/frontend, fixture and generated lifts/manifests remain unchanged.
No fork base or unrelated history was imported. Shared campaign files and the
original author's notes are unchanged. No remaining proof gap exists within
these 19 statements; function execution, termination, hardware/lifting soundness,
permissions and scheduler/TCB reasoning remain future work as scoped above.
