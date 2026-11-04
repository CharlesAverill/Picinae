# a-strcmp-fix — partial Sol repair

Author model: `gpt-6-astra` (original statements and one-shot attempt).
Repair model: `gpt-6.1-sol`, xhigh (this run).
Final full-proof producer: **none**. Do not record `final_proof_model` as Sol.
Branch: `llm-proofs/a-strcmp-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-013cef89`.

The full `strcmp_correct : strcmp_full_contract` is still aborted and has no
constant. A successful module build certifies only its completed helpers.
It does not certify the full input/output contract. No new admission, axiom,
parameter, assumed callee contract, or result oracle is introduced.

## Retained contract and scope

All 29 original definitions and theorem statements are preserved exactly
apart from whitespace/comments. `audit.py` compares them to assigned prerequisite
`0226f479f5d2588871c30ae21bbb2bf028db7379` and protects every other prerequisite
file, including the generated 77-instruction map, its manifest, root Dune,
and all original Astra notes. No public domain or postcondition is weakened.

The intended contract remains unsigned first-stop byte comparison versus
signed32(W0), arbitrary lengths and alignments, aliases/overlap and high bytes,
either NUL first, and equal strings. The unchanged read envelopes are
`[down8(p),down8(p+K)+8)` and `[down8(q),down8(q+K)+16)`, with strict nonwrap
endpoints. There is no CPU-feature, tunable or disjointness premise. The
original memory, SP, X30, X19–X29, Z8–Z15 and access-mask frames remain.

The real map has two RET sites: `0x192fe4` and `0x1930b0`. All execution facts
here concern sequential Picinae IL and stop before RET. They do not establish
termination, executed caller return, hardware/lifter refinement, concurrency,
or whole-function fault freedom. Binary provenance remains inherited and
unvalidated by this proof unit.

## Concrete decoder invariant gap

The archived `strcmp_syndrome` says the first-stop syndrome byte is nonzero,
but does not constrain its high bit when both stop bytes are NUL. For
`X2=0x200`, `X3=0x400`, `X6=0x601`, `m=0`, `p=q=K=0`, that entire weak
`strcmp_decode` predicate holds. The original byte comparison is `Eq`.
The actual unchanged REV/CLZ/LSL/LSR/SUB suffix produces X0=`0xffffffffffffffff`
(signed32 -1): REV(0x601) starts with byte 1, so CLZ is 7 and the following
bytes contribute 1 versus 2. Thus preservation of the old decoder invariant
**alone** cannot establish the return postcondition.

`strcmp_fix_weak_decode_witness` checks the weak predicate and excludes the
strong auxiliary predicate. `strcmp_fix_weak_decoder_result` checks the actual
IL suffix, not a hand-written replacement program. This state is **not claimed
reachable from a valid strcmp entry** and does not refute the full contract.

`strcmp_fix_syndrome` retains the old predicate and adds a high-bit fact on a
common NUL. `strcmp_fix_decode_project` projects the stronger auxiliary cut
back to the unchanged public invariant; `strcmp_fix_strong_decode_witness`
establishes that this stronger predicate is inhabited. The full proof must
still derive it from the real subtract/borrow masks and shifted masks.

## Repair helpers and remaining work

The added helpers cover floor-to-eight bounds/monotonicity, domain nonwrap,
byte/p-word/q-word/lookahead/prefix read locations, model MemAcc permissions,
modular pointer displacement, fully typed entry witnesses for all seven
original samples, little-endian word-byte decomposition, first-stop byte
progress, signed32 subtraction sign, and bit-granular shifted-byte comparison.
The shift comparison permits arbitrary following-byte fragments and equal
high prefixes; it is not an unjustified exact-difference specification.

The full missing obligations remain: general subtract-one word-mask/borrow
facts, prefix masking, deriving the strong syndrome at every decoder edge,
general REV/CLZ/shift correspondence, alignment and lookahead loop advancement,
connecting every dynamic load to the checked envelopes/progress bounds, and
assembling both complete entry-to-exit paths into `strcmp_correct`.
The partial suffix and CCMP lemmas (if listed in final successful assumptions
output) do not establish those caller obligations.

## Environment and ancestry

No installation or remote write occurred. The shared isolated environment
was read-only. Builds use `_build`, an ignored symlink to this unit's distinct
`/home/charles/code/friends/.toolchains/a-strcmp-fix/build` directory. Every
compiler/Dune/assumptions command uses `ulimit -v 4000000`, stack 65536,
`--cache=disabled -j1`; no concurrent compiler was started in this unit.

The first tool inspection found a clean prepared e00 HEAD `71470bff...` with
sole parent and merge-base `49956416928e5b6bb3928b54ae33e3b81091f006`.
`00-prepared.log` was recorded after creating this unit's untracked notes;
its only status entry was that notes directory. The initial sandbox fork
check failed DNS; the successful read-only check in `01-fork-name.log` was
empty, exit 0, before renaming only the prepared branch. Git metadata was
read-only in the sandbox; the first local rename/merge attempt failed before
changing history. The authorized escalated local operations then renamed
this branch and fast-forwarded only the exact assigned prerequisite.

`allowed-prerequisites.txt` records the exact union of eight prerequisite
commits above origin before import. The post-import audit allows exactly
that set plus linear scoped commits of this unit. No fork or other active
unit history was imported. No other branch was renamed, written or deleted.

Exact commands, stdout/stderr and true exits are in the numbered logs. The
inherited aborted main attempt is replayed in `05-inherited-target.log` (exit
0 because it ends with Abort, with all 21 unresolved obligations printed).
The original Astra failure at Qed remains in the protected author notes.

Diagnostic `*-probe.v.txt` files are source snapshots compiled under this
unit's isolated `tmp/` directory with the same resource limits. Some omit
unchanged expensive frame lemmas to shorten repair iterations; they do not
replace the required complete Dune target. A diagnostic containing Abort
cannot certify that aborted declaration. Only the final full target and its
separate assumptions run establish the completed helpers in the unit module.

The slow symbolic shift diagnostic was interrupted **only in this unit** at
its final ordering tactic (log 25). Log 26 records the exact owned process and
its hard/soft limits: address space 4,096,000,000 bytes; stack 67,108,864 bytes.
No other process was signalled. Rewriting the equal quotient explicitly and
clearing unrelated arithmetic hypotheses fixes the expensive nonlinear step;
the revised complete shift lemma passes in log 27. No cap was increased and
no admission was introduced.

The `m < 2^256` bound in the new entry-store constructor is used only to
construct the concrete sample witnesses. It is not added to the public
contract. Likewise the shifted-byte lemma's equal-high-prefix and tail bounds
are auxiliary arithmetic premises that a future decoder proof must derive;
they are not entry assumptions or a result oracle.

## Final verification — partial, not full strcmp correctness

`29-full-target-build.log`: **exit 0**, complete
`Examples/claude/arm8_strcmp_proof.vo`, no `.vos` or skipped proof checking:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c \
  'ulimit -v 4000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/claude/arm8_strcmp_proof.vo'
```

`31-assumptions.raw.log`: **exit 0**, verbatim `Check`/`Print Assumptions`
for all **42** completed declarations (10 retained + 32 new). The exact list
is `completed-theorems.txt`, and the per-name inventory is
`assumptions-summary.json`. **38 are closed**. Four use only inherited FE:
`strcmp_welltyped`, `strcmp_fix_byte_exit`, `strcmp_fix_byte_ccmp`, and
`strcmp_fix_weak_decoder_result`. Their complete assumption output is:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

No imported admitted fact occurs in any of these transitive assumption
outputs. FE is the inherited core/typing/proof machinery assumption documented
in e00, not a new declaration here.

The new checked execution facts are `strcmp_fix_byte_exit` (SUB at `0x1930ac`
to postcondition/frame at RET `0x1930b0`), `strcmp_fix_byte_ccmp` (CMP/CCMP
at `0x193020..0x193024` to its exact ZF at `0x193028`), and the concrete
`strcmp_fix_weak_decoder_result` (REV/CLZ/shift/SUB at `0x192fc4..0x192fe0`
to the word RET). They are segment partial correctness only. The byte-exit
requires the original first-stop bytes already in X2/X3; the full proof must
establish that at its entry. Both byte segment contracts have checked
nonvacuity witnesses. The complete full-entry samples are checked by
`strcmp_fix_samples_typed_entry`.

`32-main-absence.log`: **expected exit 1** from the required assumptions
harness: `strcmp_correct` was not found. Its statement remains as an aborted
attempt, with **no constant and no main-theorem assumptions certificate**.
This explicitly prevents treating the successful module as a complete unit.
There are no new admissions, axioms or parameters. The unit state is
**PARTIAL**; there is no hardware or termination certification.

The final post-commit ancestry, whole-base diff stat and clean-status record
is written outside the checkout only to this unit's authorized location:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/a-strcmp-fix/final-ancestry.log`.

The full staged whitespace check (log 37) returns exit 2 because verbatim
compiler pretty-printing, raw assumptions and `/proc` limits contain trailing
spaces. Those raw logs are intentionally preserved byte-for-byte. The scoped
implementation/documentation/probe-source check in log 38 passes; these raw
output warnings are not proof or source-audit failures.
