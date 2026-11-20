# PARTIAL — a-memchr-nosimd

Initial author: **gpt-6-astra, xhigh/default**. Final proof model: **none**.
Assigned branch: `llm-proofs/a-memchr-nosimd`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ba9de42a`.

The single full Dune invocation **failed, exit 1**, at
`arm8_memchr_nosimd_spec.v:156` in `mc_all_alignments_inhabited`:

```
Error: Unable to find an instance for the variable m.
```

The exact command, admission waits, stdout/stderr and true exit are in
`initial-build.log`. The mandatory gate admitted the job at 3000000 KiB;
stack 65536, Dune -j1, cache disabled. This was a proof elaboration failure,
not an out-of-memory failure. No second Astra repair, Dune build or Rocq query
was run. No installation or publication occurred.

## Deliverables and actual validation

- Statements, scalar-loop/detector invariants, readable envelope and return
  specification are in `arm8_memchr_nosimd_spec.v` and
  `arm8_memchr_nosimd_proof.v`.
- Exact initial sources are `initial-arm8_memchr_nosimd_*.v.txt`. The first
  failing helper and both unattempted main-file proofs now end in **Abort**.
  Their statements and definitions are unchanged. This packaging was not
  rebuilt and is not a completion claim.
- **No successful new unit .vo target.** The dependency build produced the
  existing e30 generated lift .vo and core .vo files; the new spec file
  failed near its end, so the main proof file never reached the compiler.
- Eleven preceding helper Qeds were processed and printed their assumptions
  before the file failed. Ten printed `Closed under the global context`:
  `mc_nwc`, `mc_preserves_memory`, `mc_preserves_saved`, `mc_preserves_frame`,
  `mc_frame_refl`, `mc_zero_result`, `mc_null_iff`, `mc_witness_typed`,
  `mc_entry_inhabited`, `mc_zero_entry_inhabited`.
- `mc_welltyped` printed the inherited baseline assumption:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

`inline-assumptions-raw.txt` is the verbatim sequential query output from the
failed file, without inferred labels. This is evidence for the reached
helper declarations only, not a full .vo certificate. The generated lift's
own typing query printed the same inherited FE assumption. No imported
admitted lemma appears in these reached query outputs. The main theorems
have **no assumptions result** because they do not exist as proved constants.
`tools/print-assumptions.sh` was not run after failure: doing so would start
another build of the failed target. A Sol completion must run it under the
gate on all main results and inspect the transitive output.

Both the full source audit and scoped audit used base
`49956416928e5b6bb3928b54ae33e3b81091f006`; no new admission, axiom or parameter
was found. The repository-wide audit inventories unrelated inherited tokens;
none was added or imported from an existing function proof by this unit.
The generated lift and all prerequisite files remain unchanged.

## Required Sol handoff

The coordinator must launch a **new gpt-6.1-sol xhigh/default** fixer; this
author did not delegate one. Preserve the statements unless genuinely wrong,
and explain every change. The immediate elaboration failure is the unsupplied
`m` in `apply mc_entry_inhabited`. No fix was attempted.

One statement detail merits an explicit decision: `mc_entry_inhabited` and
`mc_all_alignments_inhabited` quantify a bounded `m`, and the initial witness
proof constructs a store containing it, but their existential conclusions do
not explicitly state `s V_MEM64 = m`. Thus the proved existential statement
alone establishes an inhabited domain, not the stronger arbitrary-specified-
memory witness claimed by the initial prose. Strengthening those conclusions
with the equality would make that stronger claim explicit; document that
statement change if made. This does not change the main correctness domain,
which quantifies all typed initial stores and assumes no memory contents.

The substantive functional proof is **still unverified**: pure detector borrow
analysis, prefix masking, paired loads, loop advance, REV+CLZ least-hit
selection, suffix padding, zero-length execution and actual RET transfer.
Neither `mc_detector_correct` nor `memchr_nosimd_correct` is proved. The latter
statement covers all alignments under `mc_domain`, least low8(X1) match,
NULL iff absent, original-memory reads and ABI frame, but establishes nothing
until checked. See SCOPE.md for the exact bounds and proof decomposition.
Termination, fault freedom and binary/lifter refinement remain outside the
partial-correctness statement even after it is proved.

## Ancestry and artifact evidence

The allowed prerequisite is exactly
`bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9`, with seven assigned commits above
origin. `verify-ancestry.py` checks the origin pin, prerequisite inclusion,
exact allowed set plus only scoped unit commits, and prints complete logs,
diff stats and status. Post-commit evidence is stored under the authorized
external `units/a-memchr-nosimd/` directory to keep this worktree clean.

`artifact-elf.log` records successful byte-for-byte comparison of all
56 instructions / 224 bytes against the existing pinned Ubuntu ELF, along
with successful ELF, generated program and raw-pcode SHA256 comparisons.
This is inherited provenance plus a byte check, not a lifter-soundness proof.
