# r02-list-init-fix — completed retained ARMv6-M list initialization proofs

State: **DONE for all twelve original statements**, with the partial-correctness,
modeled-return and inherited provenance limits below. Initial author:
OpenAI gpt-6-astra, xhigh/priority. Final proof producer: **OpenAI
gpt-6.1-sol, xhigh/priority**. No subagents or subdelegation.

Branch: `llm-proofs/r02-list-init-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-4bc3a1d0`.
Imported EXACT author checkpoint: `4fc9de554cb6db7f0b7e3c541f4e81a1bea044f1`.
Implementation commit: `215ae494f4ba75e310bd3836f813f80423ea882a`.
The local implementation commit and subsequent clean audit are recorded in
`16-implementation-commit.log` and `17-after-implementation.log`.
The final handback supplies the full final evidence-commit SHA.

## Retention and repair

Read the shared campaign plan and assigned row, BUILDING.md,
Examples/claude/SKILL.md, notes/r02-list-init/README.md and the complete
first-build log before implementation. Charles's stricter completion rules
supersede the skill's advice to use admissions. Restored the complete archived
`notes/r02-list-init/initial-attempt.v.txt`, including all four previously
Aborted attempts, before editing the proof scripts.

`check-preservation.py` compares the complete comment/proof-stripped original
and final text, including imports, definitions, predicates and twelve theorem/
lemma declarations. All are identical; all twelve declarations end in Qed.
No declaration was dropped, renamed or weakened. The original eight prefix
proofs and the complete at-BX extraction script are unchanged. No supporting
proof declaration was added. No source statement was false or needed correction.

The main repair removes an already-consumed R0 rewrite. Symbolic execution
has already substituted R0=p and normalized modular addresses. Rather than
asking conversion to unfold two large memory expressions with a remaining
p+0 mismatch, the proof explicitly rewrites with the retained proved
`list_init_stores_image`, exposes only `list_init_stores`/`write_field32`, and
normalizes additions. The ordinary return proof explicitly fixes the cast
and jump evaluation widths at 32 bits. The original final witness script had
one excess closing bracket; it is corrected.

The generated map, original author notes, accepted r00 kit, ISA, manifests,
fixture, toolchain, root Dune list and every other existing file are unchanged.
The checkpoint already includes this exact proof target and its dependencies
in the selective root Dune module list, so no list extension was needed.

## Exact theorem scope

The target is the actual eleven-instruction `vListInitialise_armv6m_prog`,
entry 0x40 through BX LR at 0x54, with stores in order at offsets 4,8,12,16,0.
It is not a handwritten replacement implementation.

- `list_init_correct`: satisfies_all for a trace starting at 0x40 in a state
  modeling armv6mtypctx with R0=p, p nonzero, p mod 4=0, p<2^32,
  p+20<=2^32, and all twenty object bytes writable. Original memory is
  arbitrary within its modeled width. The invariant at 0x54 gives EXACT
  original-memory-based `empty_image`, R0=p, R2=0xffffffff, R3=0,
  N/Z/C/V=0/1/0/0. The list is count=0, index=p+8, sentinel value=0xffffffff,
  next=previous=p+8. No owner/container field is invented in the 12-byte
  embedded sentinel.
- `list_init_at_bx`: extracts that post from an actual exec_prog trace at
  0x54 with the specified start and unterminated prefix, and proves the
  empty-list field layout, equality of EVERY original byte outside the
  20-byte object, and all registers selected by list_init_preserved.
- `list_init_return_step`: actual can_step for the unchanged BX instruction,
  typed state, LR mod 2=1 and LR<0xfffffff0, to Addr (LR & 0xfffffffe),
  with the entire state unchanged. The original exception-range exclusion
  remains; the modeled BX semantics is not hardware exception refinement.
- `list_init_nwc`, `list_init_welltyped`, `list_init_register_frame`:
  immutable finite map, typing, and global no-assignment frame. R0/R1,
  R4-R12, SP/LR, permission maps and temporaries are preserved.
- `list_init_swap_zero`, `list_init_stores_image`,
  `list_init_post_layout_frame`: original store-order equivalence,
  initialization fields and original-memory byte frame.
- `list_init_entry_witness`, `list_init_concrete_entry_witness`,
  `list_init_return_witness`: inhabited writable typed entries for EVERY
  bounded original memory and supported pointer/return word, plus concrete
  p=4096, LR=257. Permission bitmaps use symbolic N.ones lemmas. No concrete
  evaluation of the enormous architectural memory/permission space occurs.

There is no other object/disjointness hypothesis: arbitrary preexisting
contents within and outside the destination are allowed. There are no loads,
stack accesses or calls before BX, hence no read permission, stack alignment,
callee contract, CPU feature, tunable, scheduler or IRQ premise. The finite
map ignores A_EXEC as inherited from e05. This is sequential partial
correctness and an ordinary modeled-return step, not termination, reaching
BX for every entry, asynchronous safety, whole-kernel correctness, or
binary/lifter/hardware refinement. The inherited official FreeRTOS V11.1.0
commit and exact ELF hash remain documented in the unchanged manifest and
proof header. No unresolved proof gap remains within the retained statements.

## Actual validation and failures

Every proof compiler, Dune and assumptions invocation uses the shared
read-only `/home/charles/code/friends/.toolchains/arm-validation/picinae-env`,
virtual memory cap **2000000 KiB**, stack **65536 KiB**, `--cache=disabled -j1`
and full `.vo` mode. No cap was increased and no proof compilers ran
concurrently inside this unit. No dependency installation or environment
mutation was needed. Commands, complete compiler stdout/stderr and true exit
codes are preserved by tools/record-command.sh.

- `01-diagnostic-build.log`: exit 1 after a deliberate SIGINT of this unit's
  own compiler, recorded in `03-stop-slow-diagnostic.log`. R0 replacement
  exposed the fully stepped post, then conversion at the original `change`
  statement was still running after several minutes. The identified own
  rocqworker had RSS 628660 KiB and VSZ 833132 KiB at inspection. No other
  unit's process was signaled. This is an interrupted diagnostic, not a
  successful build or an out-of-memory claim.
- `04-store-expression-repair.log`: exit 1 at the previously unchecked return
  cast; main and at-BX proofs reached Qed.
- `06-return-cast-repair.log`: exit 1 at the jump's missing width.
- `07-return-jump-repair.log`: exit 1 at the original extra witness bracket.
- `08-full-target.log`: **exit 0**, actual full target compiled with ALL
  twelve retained proofs checked. Exact successful command:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInitialise_proof.vo'
```

- `09-declaration-preservation.log`: exit 0, all declarations/definitions
  retained exactly and twelve Qed endings. `05` is an earlier static-only
  retention check, not kernel-check evidence.
- `10-source-audit.log`, `11-unit-source-audit.log`: **exit 0**, both against
  pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`. Repository NEW
  totals `{}`; unit CURRENT/NEW totals `{}`. Seven unrelated baseline
  Admitted, one admit and 89 module-interface Parameters remain unchanged.
- `12-assumptions.log`: **exit 0**, tools/print-assumptions.sh checks ALL
  twelve main/helper/frame/witness theorems with `PROOF_MEMORY_KB=2000000`
  and `PROOF_STACK_KB=65536`. Raw Check and Print Assumptions output is
  verbatim. `13-inspect-assumptions.log` checks every block: nine closed,
  three inherited-FE-only, no imported admitted theorem or other assumption.
  The complete command is at the start of the raw log.

For list_init_correct, list_init_at_bx and list_init_return_step, the verbatim
assumptions output is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

The other nine say verbatim `Closed under the global context`. The inherited
Stdlib functional extensionality dependency is documented by e00 and is
reported honestly here; it is not an imported admission or a new unit axiom.

## Ancestry and local-only boundaries

Prepared HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
whose sole parent and this branch's merge-base with origin are pinned
`49956416928e5b6bb3928b54ae33e3b81091f006`. Initial worktree was clean.
The first sandbox read-only fork lookup failed DNS; the authorized recorded
retry (`r02-list-init-fix-name-check.log`) succeeded with no result.
The initial sandbox branch rename failed on read-only linked Git metadata;
the authorized retry renamed ONLY the prepared t3/r02-list-init-fix branch.
`r02-list-init-fix-rename.log` and `r02-list-init-fix-import.log` record the
rename and exact fast-forward to the assigned author checkpoint. No automatic
approval rejection occurred. No other branch was changed and no fork history
was imported.

`audit-ancestry.sh` enforces the EXACT thirteen approved commits through the
Astra checkpoint, plus only explicitly supplied own fixer commit(s), the
pinned origin/merge-base, protected source identity, and a fixer diff limited
to this proof and notes/r02-list-init-fix/. It records the full origin-to-HEAD
log, diff stats, and status. The original preparation snapshot is
`r02-list-init-fix-before.log`; subsequent audits are in `02`, `15`, `17`.

No pushes, PRs, remote comments/writes, installs, shared campaign/status edits,
other worktree/branch mutation, or imported unrelated validation history.
