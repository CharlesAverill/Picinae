# a-ffs-fix: iterative Sol repair

Initial author: OpenAI gpt-6-astra, xhigh/default (see unchanged notes/a-ffs).
Repair model: OpenAI gpt-6.1-sol, xhigh/default. State: PARTIAL / WIP.
Charles ordered immediate wrap-up before a successful full proof certificate.
No final certified proof producer is claimed.

Prepared worktree: `/home/charles/.t3/worktrees/Picinae/t3-cc28baf9`.
Assigned local branch: `llm-proofs/a-ffs-fix`. No publication is authorized.
The worktree began clean at e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`.
The required read-only remote query succeeded with empty output before rename.
An initial sandbox DNS failure and a read-only Git-metadata failure were retried
with sandbox escalation. Only the prepared branch was renamed and fast-forwarded
to the exact allowed checkpoint `6acd817e95e667cbf81f7ac40118e2d0f31ded4d`.
The initial UI-prepared branch name changed from t3/cc28baf9 to t3/ffs-proof-fix
before this agent's recorded rename. No other branch was modified.

The exact allowed pre-unit history above origin is e00 plus 081d023, 052521a,
378fe1b, 9ae8e68 and 6acd817. Full SHAs are in 03-after-prepare.log.
The scope explicitly allows this author checkpoint's prerequisite forest.
No fork branch or unrelated implementation history was imported.

Original author evidence under notes/a-ffs is preserved byte-for-byte, including
initial-attempt.v.txt SHA256
96ea8fe0ae907de546e74b0cb6bc50a57132b61dc2376b45107a293770660dea.
The archive was restored to the active proof file before repairing it.
All 16 original statements and all 9 definitions are checked for exact retention
by check-retention.py; both historical and canonical generated maps are checked
against the checkpoint. No generated-map or root Dune change is needed.

Every compiler and assumptions query uses build.sh's shared resource gate:
unit a-ffs-fix, 1,750,000 KiB hard address-space cap, 65,536 KiB stack,
Dune --cache=disabled -j1, shared isolated environment read-only.
No dependency installation, shared config modification or other-unit process
interference is performed. No .vos or admission is acceptable as completion.

check-table.py independently reads the exact pinned Ubuntu ARM64 libc ELF,
checks its SHA256, resolves the file-backed PT_LOAD range for ELF 0x14e738,
and compares all 256 bytes against e08's JSON, the unchanged proof literal and
index bit length. The model address is ELF+0x100000 = 0x24e738. The predicate
quantifies over the table index, independently of input X0, and does not assert
the desired ffs output. This is executable provenance evidence, not a lift proof.

The intended contract covers every typed 64-bit X0, using only its low32;
zero returns zero, otherwise X0 receives the least-set-bit position in 1..32,
zero extended. No path, positive-value, size, overlap, alignment, CPU extension
or tunable restriction is added. The explicit pinned table hypothesis remains.
The postcondition frames memory, SP, X30; separate frames include X19-X30,
SP, model LR and Z8-Z15. A table-valid typed arbitrary-input witness and a
post-RET adapter with an external-address guard are required obligations.
Even full success will establish sequential IL partial correctness, not
termination, fault freedom, lifter soundness or complete binary correctness.

## Repair details so far (declarations unchanged)

- `ffs_return_cut`: replace the rejected `[->|->]` intro pattern by named
  disjunction equations and explicit substitution.
- `ffs_isolation_spec`: normalize `k+1-1` after unfolding `ffs_spec`, where
  that expression actually occurs; normalizing only the outer equality left
  the semantic bit-index obligations unchanged.
- `ffs_table_satisfiable`: state the side condition as
  `255-i+1 <= 18446744073709551616`; avoid `cbn` expanding subtraction before
  arithmetic reasoning. Both the table predicate and bytes are unchanged.
- `ffs_correct` first cut: build the outer conjunction explicitly to reuse
  `SPEC`, instead of recursively splitting its semantic definition. Normalize
  modular subtraction with `msub_mod_r 32 32` to retain arbitrary upper X0 bits.
- Execution from cut12 rewrites the invariant's X1/X2 values after each step,
  so the finite position split executes concrete machine branches without
  enumerating a restricted set of input words.

The first gated run compiled core/ARM8/common/generated dependencies and reached
`ffs_isolation_spec`; the next reached `ffs_table_satisfiable`; the next checked
all arithmetic/table/entry witnesses and reached the first `ffs_correct` cut.
These are prefix checks from failed full builds, not completed unit certificates.
All failed commands and true exits remain in the numbered build logs.


## Immediate wrap-up ordered by Charles

No further proof work, retries, compiler queries or assumptions checks were run
following the wrap-up instruction. Only this unit's own gate/compiler descendants
were stopped with SIGTERM. The latest run had finally been admitted at the assigned
cap but had no completed target when stopped; the recorder reports exit 143.
No cap increase or out-of-memory failure occurred.

Thirteen prefix declarations passed in failed full builds through log11: nwc,
welltyped, memory/callee frames, return-cut, lowest-set-bit, isolation,
spec satisfiability, isolation-spec, table-byte correctness, table satisfiability,
table-memory bound and typed arbitrary-input entry satisfiability. They are not
claimed as exported certified constants: no full unit .vo was completed.
The latest full source attempt is preserved exactly in wrap-up-attempt.v.txt.
The unchecked ffs_correct, return-guard witness and guarded-return bodies are
packaged as Abort in the active file; their original statements remain unchanged.
There are no new admissions, axioms or parameters. The final packaging was not
rebuilt, as ordered. No raw assumptions query was possible for the missing mains.
The generated dependency printed inherited functional extensionality in log04;
this is not a main-theorem assumptions certificate.

Next authorized continuation: restore the WIP attempt, repair/check the first-cut
low32 normalization and every finite-position execution obligation, then the RET
adapter. Obtain a full .vo with the unchanged gate/cap, run all 16 transitive
assumptions queries, rerun retention/source/ancestry audits and report real results.
The latest low32/execution edits remain unchecked. No theorem or contract was
weakened; the table provenance and satisfiable-witness obligations remain explicit.
