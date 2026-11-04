# a-memcpy-medium — PARTIAL author handoff

Initial author: OpenAI **gpt-6-astra, xhigh/default**. Final proof model: **none**.
Local branch: `llm-proofs/a-memcpy-medium`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-d3a7e613`.

The single full relevant build failed with `Fatal error: out of memory`;
Rocq received SIGABRT and Dune/resource-run/record-command returned **1**.
No `arm8_memcpy_medium_proof.vo` was emitted. This is not a completed unit.
No second author build, proof repair cycle, or new compiler was started after
that failure. Return to the coordinator for a **new gpt-6.1-sol xhigh/default
fixer**, retaining the statements unless a genuine error is explained.

## Exact attempt and retained work

`initial-proof.v.txt` preserves the entire initial source, before the build,
including all 104 theorem/lemma statements and their one-shot scripts.
`initial-build.log` is the exact command, complete stdout/stderr and real exit
status, recorded using `tools/record-command.sh`. The gate initially waited
three times for paging activity, then admitted the job. The first build used:

```sh
bash tools/record-command.sh notes/a-memcpy-medium/initial-build.log \
  python3 /home/charles/code/friends/.refs/picinae-llm-proofs/resources/resource-run.py \
  --unit a-memcpy-medium --memory-kib 2000000 -- \
  /home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'bash notes/a-memcpy-medium/build.sh'
```

`build.sh` invokes exactly:

```sh
ulimit -v 2000000
ulimit -s 65536
dune build --cache=disabled -j1 --display short Examples/claude/arm8_memcpy_medium_proof.vo
```

There is **no successful full unit target command**. Core dependencies, the
unchanged generated map and `arm8_memcpy_common.vo` succeeded as dependencies
of this failed command. The compiler printed checks through these five facts:

- `memcpy_medium_nwc`
- `memcpy_medium_welltyped`
- `memcpy_medium_witness_typed`
- `memcpy_medium_entry_inhabited`
- `memcpy_medium_alignment_witness`

It then completed `memcpy_medium_case_33` through `memcpy_medium_case_46`.
There are exactly fourteen size-lemma Print Assumptions blocks before failure.
The next terminal goal belongs to case 47, whose Qed/Print output never arrived.
The source retains the checked prefix verbatim. Every remaining statement,
including cases 47..128, `memcpy_medium_correct`,
`memcpy_medium_preserves_callee_saved`, and `memcpy_medium_at_ret`, remains
verbatim with **Abort**, not an admission. Their original proof scripts remain
in the archive. The declaration audit compares all 104 statements and seven
definitions exactly. Prefix Qed evidence is not a full-module certificate;
there has been no build of the post-failure Abort handoff.

The likely resource issue is accumulation of many concrete-size proof terms
in one module, in addition to symbolic execution state; this is an inference,
not a diagnosed proof defect. Live observations show enforced hard/soft address
space of 2,048,000,000 bytes and stack of 67,108,864 bytes. The last sampled
VmPeak was 1,854,436 KiB; the subsequent allocation failed. No cap was raised.
The first sandboxed resource inspection saw only its own PID namespace and
is retained as such; the `*-host`, `*-later`, `*-eight`, and `*-thirteen` logs
observe the actual compiler. No process was signaled or killed by this agent.

## Intended statement and scope

The unchanged accepted e08 map contains 99 `__memcpy_generic` instructions plus
nine mempcpy-wrapper instructions. The intended theorem starts at actual
model entry **0x19ab40** and stops at RET cuts **0x19abf8/0x19ac38**. It covers
**33..64, 65..96, and 97..128**; it is not a whole-memcpy theorem. Provenance
is inherited Ubuntu ARM64 glibc 2.35-0ubuntu3.15, libc SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`, explicit
Ghidra 11.4.2 scalar replacement, model address = ELF address + 0x100000.
No binary-to-IL soundness claim is added.

The domain requires typed ARM8 state, X0=d/X1=s/X2=n, 33<=n<=128,
d+n<=2^64, s+n<=2^64, modular bytewise NOV, source readability and destination
writability. Pointers/count are 64-bit. It imposes no extra alignment, non-null,
CPU-feature or tunable condition. The postcondition copies each ORIGINAL source
byte, preserves EVERY outside-destination byte, returns X0=d, and frames SP,
X19..X30, the distinct R_LR, and whole modeled Z8..Z15. The symbolic entry
witness covers arbitrary representable memory and pointers satisfying the
domain; the alignment witness covers every size and all source/destination
alignment pairs modulo 16 at disjoint locations. No callee contract is assumed.

`memcpy_medium_correct` is intended as `satisfies_all` IL partial correctness;
`memcpy_medium_at_ret` extracts the full postcondition on reached RET cuts.
Neither asserts termination, execution of RET, fault freedom, binary lifting
soundness, cache/IRQ behavior, wrapper correctness, or sizes outside 33..128.
Both remain unproved in this handoff. Even a passing concrete prefix does not
establish the exported all-size theorem.

## Assumptions and source audit

The compiler's verbatim target stdout/stderr is also extracted without edits
in `initial-compiler-output.txt`. The four prefix facts other than typing print
`Closed under the global context`. Typing and the fourteen size lemmas print:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

This is the inherited e00-documented assumption. No other assumption appeared
in those transitive queries. Shared memory helper queries are closed; map
welltyping has the same inherited FE assumption. Main theorems have **no
assumptions output**, because they were never proved. The required independent
`tools/print-assumptions.sh` audit was **not run**: it would rebuild the failed
target, violating the one-shot handoff policy. `assumptions.sh` is prepared for
the fixer to use through the gate only after a successful full target; it is
not evidence of an executed query. Lexical success does not certify the
unfinished dependency closure or the aborted main theorem.

The whole-tree pinned-base `tools/audit-proof-source.py` succeeds both before
and after the handoff: no new Admitted/admit/Axiom/Parameter. Existing unrelated
baseline counts remain 7 Admitted, 1 admit and 89 module-interface Parameters.
No assigned existing admission required removal. The only new code is the
private medium proof and its explicit Dune module/alias; generated maps,
shared helpers, small-copy proof and other inherited files are unchanged.

## Ancestry and permissions

Prepared HEAD was e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`, whose sole
parent is pinned origin `49956416928e5b6bb3928b54ae33e3b81091f006`. The initial
status check was empty before notes creation. The orchestration layer renamed
the initial `t3/d3a7e613` prepared branch to `t3/memcpy-medium-proof` before the
recorded before-audit; this agent renamed only that prepared branch afterward.
The read-only fork collision query initially failed in the network sandbox,
then succeeded with no results. Git's initial import/rename attempts met
read-only metadata; the authorized retries succeeded. There was no auto-review
rejection, remote mutation or dependency installation.

The exact ff-only prerequisite is `1eb19d19c77636496bb24c6c9c53c029ac76935b`.
Its seven commits above origin are precisely the allowed prerequisite forest;
`audit-ancestry.py` checks that exact set plus scoped own commits, pinned origin,
merge base, branch name, and protected inputs. Full before/after origin-range
logs and diff stats are recorded. The final commit SHA, post-commit audit and
clean status are written to the authorized external unit evidence directory:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-memcpy-medium/`.
No shared plan/status/resource configuration was edited. The mandatory gate
alone managed its own admission registry. No subagent, other branch change,
push, PR, publication, host install or shared environment mutation occurred.
