# r06-task-count-fix — DONE

Initial author: OpenAI `gpt-6-astra`, xhigh, unit r06-task-count.
Repair and final proof producer: OpenAI `gpt-6.1-sol`, xhigh.
All eleven original statements now end in kernel-checked `Qed`.
All seven original definitions and all eleven statements are retained verbatim.
No admission, Abort, new axiom, or parameter remains in the active proof.

Branch: `llm-proofs/r06-task-count-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-96052210`.
Exact reviewed author checkpoint: `7042ff1b6abdf79e2b07a348c7ef9ed014126ded`.
Pinned origin and merge-base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
The final commit is returned in the handoff; final clean-tree/ancestry evidence
is also saved in the assigned external `units/r06-task-count-fix/` directory.

## Repairs and preservation

The entire archived initial attempt was restored. The original author's
branch, worktree, attempt, failure log and statement audit were left untouched.
The active proof differs from that attempt only in attribution and these proof
repairs; no predicate, definition, hypothesis, or theorem conclusion changed:

1. `task_count_witness_models`: after splitting the variable constructors,
   choose the matching bound by a syntactic `lazymatch`. Apply the initial
   memory bound only to V_MEM32, `ones_bound (2^32)` only to A_READ, the small
   concrete bound only to LR, and the generic `task_count_zero_bound width`
   to zero-valued variables. This avoids the original attempt's speculative
   `exact B`/unification against the enormous permission bitmap. Neither
   `N.ones (2^32)` nor `2^(8*2^32)` is computed. Stack/memory caps unchanged.
2. `task_count_return_step`: explicitly instantiate `ECast` with source width
   32 and value `s R_LR`. Explicitly instantiate `XJmp` and `EBinOp` with width
   32 and the two actual bitwise-AND operands. Width inference had failed;
   these arguments express the same ARMv6-M operation as the original attempt.
   The original reset-temporaries equality proof is retained and checked.

`attempt-01.v.txt` through `attempt-03.v.txt` preserve the fixer attempts.
`build-01.log` exited 1 at ECast width inference, after the witness, main
invariant, postcondition and callee frame had passed. `build-02.log` exited 1
at XJmp's missing width. `build-03.log` exited 0 for the entire `.vo` target.
Final source only wraps that attempt's long EBinOp line; `build-clean.log`
checks the final source from a clean Dune tree and exits 0.

`audit-statements.py` verifies all eleven statements and seven definitions
against the original archive, verifies its SHA256, confirms the author's notes
are unchanged, and checks all eleven transitive assumptions reports.
`statement-assumption-audit.log` records exit 0.

## Established specification and exact scope

The actual finite generated `uxTaskGetNumberOfTasks_armv6m_prog` is used,
never a replacement handwritten program. Entry is 0x59c, LDR literal into R3;
0x59e loads R0 from [R3]; designated exit 0x5a0 is BX LR. No calls occur.

- `task_count_nwc`: code is independent of the store.
- `task_count_welltyped`: the actual generated finite program is well typed.
- `task_count_preserves_memory`: memory is unchanged for all modeled endstates.
- `task_count_zero_bound`: positive power-of-two bound at any abstract width.
- `task_count_witness_models`: every architectural memory value
  `m < 2^(8*2^32)` has the explicitly defined well-typed entry witness.
- `task_count_entry_satisfiable`: the witness has that exact arbitrary memory,
  read permission on all four loaded addresses, and odd LR (LR=1). Its memory
  bound is inhabited, for example by zero using `task_count_zero_bound`.
- `task_count_correct`: `satisfies_all` partial correctness for traces starting
  at 0x59c with a modeled ARMv6-M store, through the first designated BX LR.
- `task_count_post_at_bx`: for an actual execution trace reaching that first
  exit, R0 equals **initial** memory's 32-bit little-endian word at 0x20000030.
  `task_count_frame` preserves **every variable except R0/R3**, including
  memory, permissions, flags, SP, LR, R1/R2/R4-R12 and every V_TEMP. There is
  no promise to preserve R0/R3.
- `task_count_preserves_callee_saved`: R4-R11, SP and LR are preserved there.
- `task_count_return_step`: for any store with odd LR, an actual modeled
  `can_step` of the finite program at 0x5a0 reaches
  `LR & (N.ones 32 - 1)` with the exact same store, including reset temporaries.
- `task_count_caller_result`: combines the functional result/full frame with
  that real BX LR step, using preservation of the initial odd LR. For modeled
  32-bit LR the target is LR with bit 0 cleared. This proves a step, not a
  further execution of caller code at its destination.

No result/count/nonzero hypothesis is assumed. There is no size, overlap,
path-length, CPU-feature or tunable restriction. Functional correctness assumes
a modeled initial store and the stated entry; the post-at-exit corollaries
also require an actual execution trace and no earlier designated exit.
Read permissions are consequences of such actual load execution; the separate
witness supplies them nonvacuously. The return lemma explicitly requires odd
LR. The model is sequential: no IRQ interference, critical-section transition,
or scheduler invariant is assumed or established by this getter.

Provenance remains inherited and unvalidated as a binary-refinement theorem:
FreeRTOS Kernel V11.1.0 commit
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`, ELF SHA256
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`.
The unchanged generated getter SHA256 is
`d237568eb2e532018e17575cf35830200626e9a48ea6f0004f81e6139f51b63e`.
The folded code literal at 0x5a4 is trusted immutable-code data. The existing
ISA/frontend and fixture are unchanged. Accepted e05 closed-leaf artifacts
apply to this zero-call body; the missing 24 broader call closures are not
assumed complete. No unproved kernel/callee contract is imported.
No task-object cardinality, ISR atomicity, hardware EXC_RETURN behavior,
termination or binary/lifter soundness theorem is claimed.

## Validation and raw assumptions

All compiler and assumptions processes use the existing read-only isolated
wrapper, `PROOF_MEMORY_KB=2000000`, stack 65536 KiB, Dune `-j1`, cache disabled.
No concurrent proof compilers, installations, shared environment edits,
remote writes, pushes, PRs, or comments were used. `toolchain.log` records
Rocq 9.1.1, OCaml 4.14.2 and Dune 3.22.2 with the actual limits.
The inherited root explicit Dune module list already includes the target and
its generated dependency; no Dune edits or globs were necessary.

Successful clean full target command (`build-clean.log`, exit 0):

```bash
env PROOF_MEMORY_KB=2000000 PROOF_STACK_KB=65536 \
 /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
 bash --noprofile --norc -e -c \
 'ulimit -v 2000000; ulimit -s 65536; dune clean; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_uxTaskGetNumberOfTasks_proof.vo'
```

`assumptions.log` contains verbatim `Check`/`Print Assumptions` output for
all eleven names, obtained using `tools/print-assumptions.sh`, exit 0.
The exact command (including all names) is its `COMMAND=` line. The first
six results in the list above are `Closed under the global context`.
The other five report exactly:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is inherited `Stdlib.Logic.FunctionalExtensionality` (provenance in
`notes/e00-build/logs/15-extensionality-provenance.log`). There are no other
transitive assumptions and no imported admitted lemmas in these eleven results.

`source-audit.log` is the whole-tree `tools/audit-proof-source.py --base
49956416928e5b6bb3928b54ae33e3b81091f006` output, exit 0, `NEW totals: {}`.
Inherited unrelated baseline files still contain seven `Admitted`, one `admit`
and 89 module-interface `Parameter` tokens. `unit-source-audit.log` has no
such tokens. A whole-staged-diff whitespace check flags two trailing spaces
in verbatim Rocq/reflog stdout (`raw-log-whitespace.log`, exit 2); those raw
logs are deliberately preserved. The proof/scripts pass their whitespace check. No unrelated admitted module is a dependency of the target.

## History and final handoff

The prepared tree was clean at e00 with sole parent pinned origin. A successful
read-only exact fork-name check returned no match **before** renaming only
`t3/task-count-fix` to the assigned branch. The reviewed author checkpoint
was imported solely by `git merge --ff-only`. `preparation-transcript.txt`
records the initial observations, sandbox failures and successful retries;
`prepared-history.log` also records the rename/import reflog and e00 diff stat.
`fork-recheck.log` independently captures the later successful empty check.
No other branch was renamed/changed/deleted. No checkout/worktree was created.

`audit-ancestry.py` checks the exact nine reviewed prerequisite/author commits
and permits only scoped linear fixer commits afterward, verifies the pinned
origin/merge-base and generated hash, and prints the full log/diff stat/status.
`ancestry-imported.log` records imported history; `ancestry-precommit.log`
records final precommit history/status. The final external evidence records
full commit SHA, merge-base, complete log and diff stat, and clean status after
local commits. Only this unit's proof and notes are changed above the author
checkpoint. No r00/e19 or unrelated fork history was imported.

State: **DONE** for the exact sequential IL partial-correctness scope above.
Remaining gaps are the explicitly excluded termination, concurrency,
EXC_RETURN and binary/lifter refinement claims; none is claimed completed.
