# r18-mutex-held-fix — WIP / PARTIAL

Stopped immediately on Charles's explicit wrap-up order. No further compiler,
query, retry, or wait is authorized. Initial author: gpt-6-astra xhigh/default;
fixer: gpt-6.1-sol xhigh/default. Final checked proof producer: none.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-9c5b07a8
Branch: llm-proofs/r18-mutex-held-fix

## Actual proof status

There is NO successful full proof-module .vo and NO new Print Assumptions
certificate. Eleven prefix declarations (the original ten plus repaired
mutex_held_current_satisfiable) reached Qed in failed builds; this is not a
completed module certificate. Main mutex_held_correct and its post_at_bx,
callee-saved, return_step and caller_result corollaries remain unverified.
Current proof bodies use Qed as attempted source, without a successful build;
do not mistake this WIP source for checked theorems. No admissions or new
axiom/parameter declarations were added. No imported assumptions query ran.
Inherited FE is expected from the reviewed baseline, not certified for this WIP.

## Changes and failures

Restored Astra's exact archive (05-restored.log proves byte equality), preserving
all 16 statements and definitions. Generated map, original evidence, and Dune
list are unchanged; 06-statement-ancestry.log audits these and pinned ancestry.
The current witness fixes explicit width and locally makes memsize transparent,
then restores opacity. Its Qed passed in later failed module builds.

build-01.log: exit 1, memsize opacity prevents unfolding.
build-02.log: exit 1 after agent SIGINT of only verified own compiler PID 761258;
the witness and both execution paths had passed, but broad functional memory
conversion stalled. 08-stop-context.txt corrects the provisional diagnostic.
build-03.log / build-04.log: exit 1, intentional branch-goal diagnostics.
build-05.log / build-06.log: exit 1, NULL and register frames discharge; non-NULL
store modulo-value lemma fails to match 2^(4*8) with the goal's 2^32.
Current untested fix explicitly changes 4*8 to 32 in the instantiated lemma.
The pending build-07 request was rejected by automatic approval review after
Charles ordered no more builds. It did not run; no exit code or result exists.
This rejection enforces wrap-up and is not a new technical compiler failure.

Functional proof changes split register frames before memory conversion and
use fully instantiated getmem/setmem address/value modulo lemmas, then addition
commutativity. No statement/domain restriction was changed. Both NULL/non-NULL
paths still target original pointer return, original-memory count+1 modulo32,
exact four-byte store/frame and guarded ordinary BX. Neither functional main
Qed nor later return proof has been certified; the next authorized fixer must
finish the store equality and all later obligations, run a successful full .vo
build and all 16 raw transitive assumptions queries.

All attempted compilers used the required shared gate at 2000000 KiB, stack
65536, -j1, cache disabled and the read-only isolated wrapper. Gate waits
accounted for substantial time. No memory-cap exhaustion was observed; one
own expensive conversion was interrupted. No cap raise, host installation,
other-unit process mutation, subdelegation, push, PR or remote write occurred.
The source-only initial scoped audit (07-source-audit-initial.log) exited 0,
NEW totals {}; no final audit or assumptions run was performed after stop.

## History and evidence

Prepared e00 was clean, with sole parent pinned origin. Only an ff-only import
of exact assigned checkpoint efb04e07c821be4b78f20714edb727c4f4ee36e7 was done.
Successful empty read-only fork-name check preceded sole prepared branch rename.
Initial sandbox failures and successful authorized retries are preserved.
preparation.txt records initial clean observations and platform branch rename.
All original author evidence is unchanged. Only this proof and fixer notes
are changed above the exact author checkpoint; no unrelated history imported.
The merge base is 49956416928e5b6bb3928b54ae33e3b81091f006.

Scope remains sequential lifted ARMv6-M IL partial correctness at entry0x153c /
BX0x154a, typed input, every32-bit pointer including NULL, modulo32 count and
address wrapping including aliases, no size/count/nonoverlap/alignment/tunable
restriction. Permission and typed witnesses are mathematical entry witnesses;
ordinary return requires odd LR below0xfffffff0. Termination, full execution
existence, concurrency/IRQ/EXC_RETURN and binary/lifter refinement are not proved.
