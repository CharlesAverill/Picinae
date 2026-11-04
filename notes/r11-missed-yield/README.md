# r11-missed-yield — PARTIAL Astra handoff

Initial author: gpt-6-astra, xhigh, default (assignment). Final proof producer:
none. A NEW gpt-6.1-sol xhigh/default fixer is required; no child was launched.
No proof statement may be changed without explaining a genuine error.

The single full Dune attempt failed with `Fatal error: out of memory` and signal
ABRT in the authored target. Dune/resource helper exit 1. The resource gate
first waited for paging/RAM, then admitted the job with 1750000 KiB address-space
cap, stack 65536 KiB, -j1, cache disabled. No cap increase, second build, proof
repair cycle, assumptions compiler, or dependency installation was attempted.
Core dependencies and the generated lift compiled. There is NO successful full
proof target, NO new certified main theorem, and NO unit .vo. The compiler
emitted no source line for the OOM; no failing lemma is inferred from it.

`initial-attempt.v.txt` preserves the exact 18 theorem/lemma/corollary statements
and initial proof scripts, SHA256
`f4c7cb34fa53a4ecbd6e853d2852ee0e23bd188468531b82ac2a1dcac13cac9d`.
The live proof source keeps every definition and statement, replacing all proof
bodies with `Abort` to avoid asserting unvalidated results. This mechanical
handoff is not a repair. No second compilation was performed. `initial-build.log`
contains exact command, all stdout/stderr and the true exit code.

Attempted main coverage:

- `missed_yield_correct`, `missed_yield_post_at_bx`: typed entry 0x9c0 to the
  first BX LR cut at 0x9c6 in the actual generated finite instruction map.
- `missed_yield_functional`: xYieldPendings[0] becomes 1, exact four bytes
  [1;0;0;0] at 0x2000001c, and every modularly disjoint byte equals ENTRY memory.
- `missed_yield_preserves_registers` and `missed_yield_preserves_callee_saved`:
  exact exceptions MEM/R2/R3/N/Z; SP/LR and all other variables preserved.
- `missed_yield_entry_satisfiable`: arbitrary typed original memory and arbitrary
  ordinary LR, with write permission on the four target bytes.
- `missed_yield_execution_witness`, `missed_yield_return_step`, and
  `missed_yield_execution_returns`: actual LDR/MOVS/STR steps and guarded BX
  for odd LR strictly below 0xfffffff0. No unconstrained callee contract.
- Welltyping, nwc, memory-word/byte/frame and per-instruction helpers are
  included in the initial attempt. None is claimed as a unit .vo certificate.

Evidence: pinned V11.1.0 tasks.c SHA256 matches the e05 manifest; source line
5608 assigns xYieldPendings[portGET_CORE_ID()] = pdTRUE. The configuration has
one core; BaseType_t size is four; ELF nm/abi/literal evidence locates the
four-byte object at 0x2000001c. `provenance.log` records exact files/hashes/source.
No guessed object offset, no generated lift modification, no CPU/tunable or
old-value/path restriction. The C critical-section requirement is outside this
sequential IL theorem: no IRQ/concurrency or hardware safety claim is made.
No termination, scheduler-cardinality, whole-kernel, or proved lifter/binary
refinement claim is made. Literal bytes and inherited decoder remain trusted.

Validation:

- Full attempted target: `dune build --cache=disabled -j1 --display short
  Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.vo`, through the mandatory
  resource helper and read-only isolated toolchain. Exit 1, NOT successful.
- Base-wide and unit source audits exit 0; no new admissions/axioms/parameters.
  Final audits also check the aborted handoff.
- `tools/print-assumptions.sh` was NOT run: the first attempt failed and no unit
  main theorem is available. Raw assumptions output is unavailable. Inherited
  baseline FunctionalExtensionality.functional_extensionality_dep is known
  from e00/r06; this attempt has NOT established its transitive assumption set.
- No .vos, skipped proof checking, hidden callee assumptions, host installs,
  push, PR, or other remote writes.

Ancestry: prepared clean HEAD was e00 71470bffba65392adf1873a3df9f0cf0ca4f1ac9.
A successful empty `git ls-remote --heads fork
refs/heads/llm-proofs/r11-missed-yield` preceded renaming only the new prepared
branch. Fast-forwarded to exact assigned prerequisite
5fec2fc24d0c739bafc08add426f02a3085e15cd. Its ten commits above origin are the
explicit accepted ancestry, including r06 author/fixer commits and engineering
merges. No r00 or unrelated proof history was imported; templates were read-only.
`check-ancestry.py` verifies origin pin, merge bases, exact prerequisite set,
linear own commits and their file scope. Postcommit audit is also saved in the
external permitted unit evidence directory. Worktree:
/home/charles/.t3/worktrees/Picinae/t3-0bd052c9.
Assigned local branch: llm-proofs/r11-missed-yield.

Remaining work: Sol must diagnose the first capped OOM while preserving the
statements, finish and kernel-check the complete target under the assigned
resource gate/cap, and obtain verbatim Print Assumptions on all exported facts.
Partial source audits do not substitute for these missing certificates.
